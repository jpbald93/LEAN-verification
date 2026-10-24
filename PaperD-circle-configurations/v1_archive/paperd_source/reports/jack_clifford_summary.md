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

