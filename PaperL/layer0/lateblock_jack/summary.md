# Lean statement audit (jack)

Generated 2026-11-25 03:41 UTC

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 596, "mut": 891, "killed": 875, "surv": 16, "tout": 3, "contra": 0, "sat": 0, "unres": 0, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## paperL_jack
- theorems: 596
- step 1 mutants: 891 | killed 872 | killed-timeout 3 | SURVIVED 16 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 0 | no-hyp 0 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 0 | unresolved 0 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
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
  - SURVIVOR `child_line_of_parent_mid_zero` [eq->ne@351]: `∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) ` -> `∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) `
  - SURVIVED detail: 
  - SURVIVOR `child_line_of_parent_mid_zero` [ne->eq@18]: `∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) ` -> `∃ p u : ℂ, u = 0 ∧ ∀ j : Fin (2*k+5),
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
  - no mutants generated (manual look): EvenCorner_proof, GenPos4.cliffordEq_miquel, GenPos4.mD_ne_zero, GenPos5.pos4_abcd, GenPos5.pos4_abce, GenPos5.pos4_abde, GenPos5.pos4_acde, GenPos5.pos4_bcde, GenPosN.comp_succAbove, GenPosN.exists_snoc, GenPosN.pos4, GenPosN.pos5, IsGCircle.liftS, IsGCircleS.infty_mem, IsGCircleS.preimage, KP6_row, KP_eq_scale, KP_mulVec_eq_zero_iff, K_exists_ker, K_finrank_ker_ge_two, Kc_exists_ker, Kc_finrank_ker_eq_one, Kf_border_even, Kf_border_odd, Kf_four_finrank, Kf_ker_eq_span, Kf_ker_smul, Transversal.left_ne_zero, Transversal.ne, Transversal.right_ne_zero, blockEquiv_inl, blockEquiv_inr, blockRev_blockEquiv, blockRev_val, c4_ne_zero, c5_genPosN, c6_genPosN, cD_eq_det, cD_eq_zero, cD_eq_zeroS

