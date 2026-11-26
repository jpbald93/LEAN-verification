# Layer 11 — name/line gate, Paper L v1.1

Instrument: `namegate.py` (this directory), run against a full line-numbered dump of the pinned tree (`jack:~/paperL_jack`, `Clifford/MorleyKernel.lean` sha `4beb169a…`, gate 37 declarations). It reads every `Clifford/File.lean:N` citation, not only backticked ones: prose, code comments, comma lists and table rows.

**Result: PASS.** 66 citation occurrences, 63 distinct `file:line` pairs, all resolving to a declaration; 33 attribution checks in the `` `name` (`file:line`) `` form all matching; 0 table rows (gate list, bridges, statement declarations) all matching the attributed name.

## Distinct citations

| file:line | declaration found |
|---|---|
| `Clifford/Basic.lean:394` | `second` |
| `Clifford/Basic.lean:402` | `GenTriple` |
| `Clifford/Bridge.lean:110` | `genTriple_iff` |
| `Clifford/Classify.lean:227` | `cliffordChain_iff` |
| `Clifford/Clean.lean:165` | `Chain` |
| `Clifford/Clean.lean:177` | `GenPosN` |
| `Clifford/Clean.lean:184` | `CliffordChain` |
| `Clifford/Counter6.lean:19` | `cx` |
| `Clifford/Counter6.lean:33` | `cx_genPosN` |
| `Clifford/Counter6.lean:182` | `not_chain6` |
| `Clifford/Counter6.lean:227` | `not_cliffordChain_six` |
| `Clifford/Mobius.lean:35` | `ChainS` |
| `Clifford/Mobius.lean:46` | `CliffordChainS` |
| `Clifford/Mobius.lean:51` | `liftS` |
| `Clifford/Mobius.lean:119` | `chainS_of_chain` |
| `Clifford/Mobius.lean:178` | `cliffordChainS_of_le_five` |
| `Clifford/Mobius.lean:181` | `cliffordChain_threeS` |
| `Clifford/Mobius.lean:330` | `cliffordChainS_all_of` |
| `Clifford/Mobius.lean:492` | `line0` |
| `Clifford/Mobius.lean:627` | `line5` |
| `Clifford/Mobius.lean:651` | `chainS_six` |
| `Clifford/MorleyKernel.lean:44` | `onCircleM_iff_lineOf` |
| `Clifford/MorleyKernel.lean:55` | `lineOf_eq_line` |
| `Clifford/MorleyKernel.lean:95` | `Kf` |
| `Clifford/MorleyKernel.lean:137` | `finrank_ker_eq_one` |
| `Clifford/MorleyKernel.lean:159` | `crossVec` |
| `Clifford/MorleyKernel.lean:164` | `mulVec_crossVec` |
| `Clifford/MorleyKernel.lean:187` | `Kf_ker_eq_span` |
| `Clifford/MorleyKernel.lean:214` | `KP` |
| `Clifford/MorleyKernel.lean:236` | `KP_mulVec_eq_zero_iff` |
| `Clifford/MorleyKernel.lean:321` | `levelPoint_four` |
| `Clifford/MorleyKernel.lean:406` | `k0k3_sub_k1k2` |
| `Clifford/MorleyKernel.lean:446` | `oddCircleEq` |
| `Clifford/MorleyKernel.lean:452` | `levelPointN` |
| `Clifford/MorleyKernel.lean:462` | `oddCircleEq_five_cross` |
| `Clifford/MorleyKernel.lean:514` | `step_four_five` |
| `Clifford/MorleyKernel.lean:560` | `StepEven` |
| `Clifford/MorleyKernel.lean:571` | `StepOdd` |
| `Clifford/MorleyKernel.lean:1674` | `stepEven_gen` |
| `Clifford/MorleyKernel.lean:2088` | `stepOdd_gen` |
| `Clifford/MorleyKernel.lean:2118` | `kernelCircle_eq` |
| `Clifford/MorleyKernel.lean:2140` | `kernelCircle_zeroSet` |
| `Clifford/MorleyKernel.lean:2160` | `kernelCircle_isGCircleS` |
| `Clifford/MorleyKernel.lean:2549` | `EptInf` |
| `Clifford/MorleyKernel.lean:2566` | `h4_pt_inf` |
| `Clifford/MorleyKernel.lean:4082` | `child_mulVec_of_parentN` |
| `Clifford/MorleyKernel.lean:4115` | `QL_zero_of_P0_Q0` |
| `Clifford/MorleyKernel.lean:4270` | `hodd_inf_P0_eq` |
| `Clifford/MorleyKernel.lean:4583` | `children_eq_of_P3_zero` |
| `Clifford/MorleyKernel.lean:4601` | `child_line_of_P3_zero` |
| `Clifford/MorleyKernel.lean:4643` | `hodd_inf_all'` |
| `Clifford/MorleyKernel.lean:4697` | `heven_kernel` |
| `Clifford/MorleyKernel.lean:4998` | `parent_crossVec_zero_of_mid` |
| `Clifford/MorleyKernel.lean:5119` | `heven_of_common` |
| `Clifford/MorleyKernel.lean:5137` | `heven_line_of_P0` |
| `Clifford/MorleyKernel.lean:5253` | `EvenCorner` |
| `Clifford/MorleyKernel.lean:5287` | `evenCorner_of_QL` |
| `Clifford/MorleyKernel.lean:5345` | `kpe5_eq_kpe6_succAbove` |
| `Clifford/MorleyKernel.lean:5499` | `polyF_coeff_top` |
| `Clifford/MorleyKernel.lean:5584` | `EvenCorner_proof` |
| `Clifford/MorleyKernel.lean:5586` | `heven_inf_all` |
| `Clifford/MorleyKernel.lean:5592` | `cliffordChainS_inf` |
| `Clifford/MorleyKernel.lean:5599` | `cliffordChainS_all` |

## Table rows checked (name → declaration at line)

| draft line | name in draft | file:line | declaration found |
|---|---|---|---|

## What this gate does not check

Names and lines only. It does not compare signatures or hypotheses; the signature anchors for the statement declarations are the rows of §1.3 of the verification record, which anchor a line, not a type. The hypothesis-level audit is layer 12's job, run on v0.1; the reviewer passes on v0.2, v0.3, v0.7, v0.9 and v0.10 are recorded in Appendix C of the verification record.

