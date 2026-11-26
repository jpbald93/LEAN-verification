# leancheck — lean/paperL_john (2026-11-19 14:39 UTC)

- path: /Users/john/lean/paperL_john
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'Clifford.MorleyKernel.EvenCorner_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'Clifford.MorleyKernel.evenCornerQL_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (36 declarations, standard axioms only)
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

Generated 2026-11-19 12:34 PST

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 577, "mut": 1544, "killed": 1527, "surv": 17, "tout": 13, "contra": 0, "sat": 0, "unres": 0, "nohyp": 0, "invalid": 1}

Baseline failures (files skipped): 0

## lean/paperL_john
- theorems: 577
- step 1 mutants: 1544 | killed 1514 | killed-timeout 13 | SURVIVED 17 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 347 | no-hyp 229 | invalid 1 | timeout 0
- step 2b satisfiable: CERTIFIED 0 | unresolved 0 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `det5_mul_det3` [eq->ne@125] (heartbeat limit)
  - killed by timeout `kK_expand` [eq->ne@42] (heartbeat limit)
  - killed by timeout `cross_second` [lit2->3@283] (heartbeat limit)
  - SURVIVED detail: own proof compiled; downstream errors at lines [233]
  - SURVIVOR `cliffordChain_one` [lit1->2@15]: `CliffordChain 1` -> `CliffordChain 2`
  - killed by timeout `det4_col1` [lit1->2@113] (heartbeat limit)
  - killed by timeout `lineOf_eq_line` [lit2->3@78] (heartbeat limit)
  - killed by timeout `crossVec_KP5_P0` [lit0->1@25] (heartbeat limit)
  - killed by timeout `crossVec_KP6_swap3` [eq->ne@27] (heartbeat limit)
  - killed by timeout `crossVec_KP6_swap3` [lit3->4@25] (heartbeat limit)
  - killed by timeout `crossVec_KP6_swap6` [eq->ne@27] (heartbeat limit)
  - killed by timeout `crossVec_KP6_swap6` [lit6->7@25] (heartbeat limit)
  - SURVIVED detail: own proof compiled; downstream errors at lines [1647]
  - SURVIVOR `ins_eval` [lit0->1@35]: `Fin.insertNth (α := fun _ => R) p 0 w k = w j` -> `Fin.insertNth (α := fun _ => R) p 1 w k = w j`
  - killed by timeout `kernel_eq_zero_of_P0` [lit2->3@22] (heartbeat limit)
  - killed by timeout `child_levelPt_kernel_line` [lit2->3@51] (heartbeat limit)
  - SURVIVED detail: own proof compiled; downstream errors at lines [2761]
  - SURVIVOR `dX_cD` [neg1->1@5]: `cD ⟨-1/5, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0` -> `cD ⟨1/5, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0`
  - SURVIVED detail: own proof compiled; downstream errors at lines [2761]
  - SURVIVOR `dX_cD` [neg1->1@30]: `cD ⟨-1/5, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0` -> `cD ⟨-1/5, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨1, 1⟩ 0 ≠ 0`
  - SURVIVED detail: own proof compiled; downstream errors at lines [2761]
  - SURVIVOR `dX_cD` [lit1->2@6]: `cD ⟨-1/5, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0` -> `cD ⟨-2/5, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0`
  - SURVIVED detail: own proof compiled; downstream errors at lines [2761]
  - SURVIVOR `dX_cD` [lit5->6@8]: `cD ⟨-1/5, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0` -> `cD ⟨-1/6, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0`
  - SURVIVED detail: own proof compiled; downstream errors at lines [2761]
  - SURVIVOR `dX_cD` [lit2->3@11]: `cD ⟨-1/5, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0` -> `cD ⟨-1/5, 3/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0`
  - SURVIVED detail: 
  - SURVIVOR `p0_children_gcircleS_false` [lit2->3@19]: `¬ ∀ (d : Fin (2 * 0 + 5) → ℂ), (∀ j, d j ≠ 0) →
      crossVec (KP (2 * 0 + 5) d (fun j => conj (d j))) 0 = 0 →
      ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircle` -> `¬ ∀ (d : Fin (3 * 0 + 5) → ℂ), (∀ j, d j ≠ 0) →
      crossVec (KP (2 * 0 + 5) d (fun j => conj (d j))) 0 = 0 →
      ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircle`
  - SURVIVED detail: 
  - SURVIVOR `p0_children_gcircleS_genPos` [lit2->3@70]: `∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * 0 + 5), (↑(levelPointN (2 * 0 + 4) (crossVec (KP (2 * 0 + 4) (d ∘ i.succAbove)
        (fun` -> `∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (3 * 0 + 5), (↑(levelPointN (2 * 0 + 4) (crossVec (KP (2 * 0 + 4) (d ∘ i.succAbove)
        (fun`
  - killed by timeout `d7_child_6` [lit6->7@28] (heartbeat limit)
  - SURVIVED detail: own proof compiled; downstream errors at lines [3922]
  - SURVIVOR `kpe_P0` [lit5->6@14]: `kpe (2 * k + 5) x y 0 = y ^ (k + 3)` -> `kpe (2 * k + 6) x y 0 = y ^ (k + 3)`
  - SURVIVED detail: 
  - SURVIVOR `hodd_inf_zero` [lit2->3@70]: `∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * 0 + 5), EptInf (2 * 0 + 4) (d ∘ i.succAbove) ∈ Y` -> `∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (3 * 0 + 5), EptInf (2 * 0 + 4) (d ∘ i.succAbove) ∈ Y`
  - SURVIVED detail: 
  - SURVIVOR `child_line_of_parent_mid_zero` [ne->eq@18]: `∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) ` -> `∃ p u : ℂ, u = 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) `
  - SURVIVED detail: 
  - SURVIVOR `child_line_of_parent_mid_zero` [eq->ne@351]: `∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) ` -> `∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) `
  - SURVIVED detail: 
  - SURVIVOR `child_line_of_parent_mid_zero` [ne->eq@186]: `∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) ` -> `∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) `
  - SURVIVED detail: 
  - SURVIVOR `child_line_of_parent_mid_zero` [lit0->1@20]: `∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) ` -> `∃ p u : ℂ, u ≠ 1 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) `
  - SURVIVED detail: own proof compiled; downstream errors at lines [5574]
  - SURVIVOR `polyF_natDegree_le` [lit2->3@25]: `(polyF k W).natDegree ≤ 2 * k + 5` -> `(polyF k W).natDegree ≤ 3 * k + 5`
  - SURVIVED detail: own proof compiled; downstream errors at lines [5574]
  - SURVIVOR `polyF_natDegree_le` [lit5->6@33]: `(polyF k W).natDegree ≤ 2 * k + 5` -> `(polyF k W).natDegree ≤ 2 * k + 6`
  - no mutants generated (manual look): EvenCorner_proof, GenPos5.pos4_abcd, GenPos5.pos4_abce, GenPos5.pos4_abde, GenPos5.pos4_acde, GenPos5.pos4_bcde, GenPosN.comp_succAbove, IsGCircle.liftS, IsGCircleS.preimage, c5_genPosN, c6_genPosN, cd_symm, chain3S_mem, chain3_mem, chainS_of_chain_pt, child_det_M7, child_det_MN, child_line_P0, child_line_P0N, cliffordChainS_all_of, cliffordChainS_inf, cliffordChainS_of_cliffordChain, cliffordChainS_of_corner, cliffordChainS_of_inf, cliffordChainS_of_inf', cliffordChainS_of_le_five, clifford_one, clifford_two, clifford_two_clean, coe_mem_liftS, collinear_of_line, cospherical_of_eq, cospherical_or_collinear, cx_genPosN, cx_genTriple, cx_transversal, d7_genPosN, evenCornerQL_proof, evenCorner_of_cornerQL, exists_gcircle

## Layers 6,9 — hypothesis ablation and bridge inventory
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 8 files
linter (scratch): 0 warnings in 26 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (36 declarations, standard axioms only) |
| tamper (layer 2) | 8/8 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 8 of 8 files ok |
| conclusion mutations (layer 4) | **1527/1544 rejected** (1514 by error, 13 by timeout/heartbeat); 17 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 347 probed ok — no-hyp 229 probe-invalid 1 |
| satisfiability (layer 8) | 0/0 certified [0 with hypotheses, 0 hypothesis-free binders, 0 closed], 0 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 0/0 credited, 0 unresolved |
| hypothesis ablation (layer 6) | 0 needed, **0 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 8 files |
| linter, scratch (layer 7) | 0 warnings in 26 files |
| bridge inventory (layer 9) | not run |

mutation survivors (classify by hand): `cliffordChain_one` [lit1->2@15] own proof compiled; downstream errors at lines [233]; `ins_eval` [lit0->1@35] own proof compiled; downstream errors at lines [1647]; `dX_cD` [neg1->1@5] own proof compiled; downstream errors at lines [2761]; `dX_cD` [neg1->1@30] own proof compiled; downstream errors at lines [2761]; `dX_cD` [lit1->2@6] own proof compiled; downstream errors at lines [2761]; `dX_cD` [lit5->6@8] own proof compiled; downstream errors at lines [2761]; `dX_cD` [lit2->3@11] own proof compiled; downstream errors at lines [2761]; `p0_children_gcircleS_false` [lit2->3@19] ; `p0_children_gcircleS_genPos` [lit2->3@70] ; `kpe_P0` [lit5->6@14] own proof compiled; downstream errors at lines [3922]; `hodd_inf_zero` [lit2->3@70] ; `child_line_of_parent_mid_zero` [ne->eq@18] 
LEANCHECK DONE Thu Nov 19 20:48:12 UTC 2026
