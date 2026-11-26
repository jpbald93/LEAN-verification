# Layer 11 — name/line gate, Paper L draft v0.10

Instrument: `namegate.py` (this directory), run against a full line-numbered dump of the pinned tree (`jack:~/paperL_jack`, `Clifford/MorleyKernel.lean` sha `dce7b011…`). It reads every `Clifford/File.lean:N` citation, not only backticked ones: prose, code comments, comma lists and table rows.

**Result: PASS.** 143 citation occurrences, 98 distinct `file:line` pairs, all resolving to a declaration; 25 attribution checks in the `` `name` (`file:line`) `` form all matching; 85 table rows (gate list, bridges, statement declarations) all matching the attributed name.

## Distinct citations

| file:line | declaration found |
|---|---|
| `Clifford/Basic.lean:385` | `onCircleM_iff` |
| `Clifford/Basic.lean:394` | `second` |
| `Clifford/Basic.lean:398` | `Transversal` |
| `Clifford/Basic.lean:402` | `GenTriple` |
| `Clifford/Basic.lean:424` | `second_eq_coords` |
| `Clifford/Basic.lean:445` | `second_onCircleM_left` |
| `Clifford/Basic.lean:449` | `second_onCircleM_right` |
| `Clifford/Basic.lean:520` | `mD_ne_zero` |
| `Clifford/Basic.lean:601` | `clifford_one` |
| `Clifford/Basic.lean:693` | `clifford_two` |
| `Clifford/Bridge.lean:22` | `collinear_iff_conj_mul` |
| `Clifford/Bridge.lean:58` | `transversal_iff` |
| `Clifford/Bridge.lean:62` | `triP_ne_zero_iff` |
| `Clifford/Bridge.lean:70` | `cross_second` |
| `Clifford/Bridge.lean:83` | `cycP_ne_zero_iff` |
| `Clifford/Bridge.lean:104` | `onCircleM_iff_mem_sphere` |
| `Clifford/Bridge.lean:110` | `genTriple_iff` |
| `Clifford/BridgeL10.lean:32` | `det3_eq_det` |
| `Clifford/BridgeL10.lean:38` | `crs_eq_det2` |
| `Clifford/BridgeL10.lean:43` | `det_fin_four_eq_det4` |
| `Clifford/BridgeL10.lean:53` | `det_fin_five_eq_det5` |
| `Clifford/BridgeL10.lean:63` | `det4_eq_det` |
| `Clifford/BridgeL10.lean:70` | `det5_eq_det` |
| `Clifford/BridgeL10.lean:78` | `mN_eq_det` |
| `Clifford/BridgeL10.lean:86` | `mD_eq_det` |
| `Clifford/BridgeL10.lean:95` | `crossVec_eq_crossProduct` |
| `Clifford/BridgeL10.lean:105` | `miquel_eq_det_div` |
| `Clifford/BridgeL10.lean:117` | `triP_eq_zero_iff_collinear` |
| `Clifford/BridgeL10.lean:131` | `colD_eq_zero_iff_collinear` |
| `Clifford/BridgeL10.lean:137` | `cD_eq_det` |
| `Clifford/BridgeL10.lean:145` | `cospherical_or_collinear_of_eqn` |
| `Clifford/BridgeL10.lean:189` | `exists_eqn_of_cD` |
| `Clifford/BridgeL10.lean:209` | `cD_eq_zero_iff` |
| `Clifford/BridgeL10.lean:221` | `cycP_eq_cD` |
| `Clifford/BridgeL10.lean:239` | `cycP_eq_zero_iff` |
| `Clifford/BridgeL10.lean:248` | `onCircle3_iff_cospherical` |
| `Clifford/Classify.lean:43` | `cliffordChain_three` |
| `Clifford/Classify.lean:57` | `not_chain_of_extends` |
| `Clifford/Classify.lean:167` | `GenPosN.exists_snoc` |
| `Clifford/Classify.lean:219` | `not_cliffordChain_of_six_le` |
| `Clifford/Classify.lean:227` | `cliffordChain_iff` |
| `Clifford/Clean.lean:24` | `mem_line_of` |
| `Clifford/Clean.lean:36` | `collinear_of_line` |
| `Clifford/Clean.lean:43` | `clifford_points_on` |
| `Clifford/Clean.lean:93` | `miquel_all_eq` |
| `Clifford/Clean.lean:123` | `clifford_two_clean` |
| `Clifford/Clean.lean:165` | `Chain` |
| `Clifford/Clean.lean:177` | `GenPosN` |
| `Clifford/Clean.lean:184` | `CliffordChain` |
| `Clifford/Clean.lean:226` | `cliffordChain_four` |
| `Clifford/Clean.lean:245` | `cliffordChain_five` |
| `Clifford/Counter6.lean:19` | `cx` |
| `Clifford/Counter6.lean:33` | `cx_genPosN` |
| `Clifford/Counter6.lean:182` | `not_chain6` |
| `Clifford/Counter6.lean:227` | `not_cliffordChain_six` |
| `Clifford/General.lean:32` | `cD_eq_zero` |
| `Clifford/General.lean:61` | `chain4_cD` |
| `Clifford/General.lean:87` | `chain5_mem` |
| `Clifford/Mobius.lean:24` | `lineS` |
| `Clifford/Mobius.lean:28` | `IsGCircleS` |
| `Clifford/Mobius.lean:35` | `ChainS` |
| `Clifford/Mobius.lean:46` | `CliffordChainS` |
| `Clifford/Mobius.lean:51` | `liftS` |
| `Clifford/Mobius.lean:119` | `chainS_of_chain` |
| `Clifford/Mobius.lean:152` | `chainS_of_chain_pt` |
| `Clifford/Mobius.lean:157` | `cliffordChainS_of_cliffordChain` |
| `Clifford/Mobius.lean:178` | `cliffordChainS_of_le_five` |
| `Clifford/Mobius.lean:181` | `cliffordChain_threeS` |
| `Clifford/Mobius.lean:330` | `cliffordChainS_all_of` |
| `Clifford/Mobius.lean:492` | `line0` |
| `Clifford/Mobius.lean:627` | `line5` |
| `Clifford/Mobius.lean:651` | `chainS_six` |
| `Clifford/Mobius.lean:734` | `chainS_six_unique` |
| `Clifford/Mobius.lean:779` | `chainS_six_iff` |
| `Clifford/MorleyKernel.lean:95` | `Kf` |
| `Clifford/MorleyKernel.lean:159` | `crossVec` |
| `Clifford/MorleyKernel.lean:214` | `KP` |
| `Clifford/MorleyKernel.lean:219` | `aOf` |
| `Clifford/MorleyKernel.lean:236` | `KP_mulVec_eq_zero_iff` |
| `Clifford/MorleyKernel.lean:452` | `levelPointN` |
| `Clifford/MorleyKernel.lean:2549` | `EptInf` |
| `Clifford/MorleyKernel.lean:2566` | `h4_pt_inf` |
| `Clifford/MorleyKernel.lean:2571` | `hc_of_genPos` |
| `Clifford/MorleyKernel.lean:4643` | `hodd_inf_all'` |
| `Clifford/MorleyKernel.lean:4650` | `cliffordChainS_of_inf'` |
| `Clifford/MorleyKernel.lean:4697` | `heven_kernel` |
| `Clifford/MorleyKernel.lean:4998` | `parent_crossVec_zero_of_mid` |
| `Clifford/MorleyKernel.lean:5137` | `heven_line_of_P0` |
| `Clifford/MorleyKernel.lean:5253` | `EvenCorner` |
| `Clifford/MorleyKernel.lean:5269` | `cliffordChainS_of_corner` |
| `Clifford/MorleyKernel.lean:5287` | `evenCorner_of_QL` |
| `Clifford/MorleyKernel.lean:5317` | `EvenCornerQL` |
| `Clifford/MorleyKernel.lean:5325` | `evenCorner_of_cornerQL` |
| `Clifford/MorleyKernel.lean:5499` | `polyF_coeff_top` |
| `Clifford/MorleyKernel.lean:5539` | `evenCornerQL_proof` |
| `Clifford/MorleyKernel.lean:5584` | `EvenCorner_proof` |
| `Clifford/MorleyKernel.lean:5586` | `heven_inf_all` |
| `Clifford/MorleyKernel.lean:5592` | `cliffordChainS_inf` |

## Table rows checked (name → declaration at line)

| draft line | name in draft | file:line | declaration found |
|---|---|---|---|
| 496 | `Clifford.clifford_one` | `Clifford/Basic.lean:601` | `clifford_one` |
| 497 | `Clifford.clifford_two` | `Clifford/Basic.lean:693` | `clifford_two` |
| 498 | `Clifford.second_onCircleM_left` | `Clifford/Basic.lean:445` | `second_onCircleM_left` |
| 499 | `Clifford.second_onCircleM_right` | `Clifford/Basic.lean:449` | `second_onCircleM_right` |
| 500 | `Clifford.second_eq_coords` | `Clifford/Basic.lean:424` | `second_eq_coords` |
| 501 | `Clifford.onCircleM_iff` | `Clifford/Basic.lean:385` | `onCircleM_iff` |
| 502 | `Clifford.mD_ne_zero` | `Clifford/Basic.lean:520` | `mD_ne_zero` |
| 503 | `Clifford.clifford_two_clean` | `Clifford/Clean.lean:123` | `clifford_two_clean` |
| 504 | `Clifford.collinear_of_line` | `Clifford/Clean.lean:36` | `collinear_of_line` |
| 505 | `Clifford.miquel_all_eq` | `Clifford/Clean.lean:93` | `miquel_all_eq` |
| 506 | `Clifford.clifford_points_on` | `Clifford/Clean.lean:43` | `clifford_points_on` |
| 507 | `Clifford.mem_line_of` | `Clifford/Clean.lean:24` | `mem_line_of` |
| 508 | `Clifford.cliffordChain_four` | `Clifford/Clean.lean:226` | `cliffordChain_four` |
| 509 | `Clifford.cliffordChain_five` | `Clifford/Clean.lean:245` | `cliffordChain_five` |
| 510 | `Clifford.collinear_iff_conj_mul` | `Clifford/Bridge.lean:22` | `collinear_iff_conj_mul` |
| 511 | `Clifford.transversal_iff` | `Clifford/Bridge.lean:58` | `transversal_iff` |
| 512 | `Clifford.triP_ne_zero_iff` | `Clifford/Bridge.lean:62` | `triP_ne_zero_iff` |
| 513 | `Clifford.cross_second` | `Clifford/Bridge.lean:70` | `cross_second` |
| 514 | `Clifford.cycP_ne_zero_iff` | `Clifford/Bridge.lean:83` | `cycP_ne_zero_iff` |
| 515 | `Clifford.onCircleM_iff_mem_sphere` | `Clifford/Bridge.lean:104` | `onCircleM_iff_mem_sphere` |
| 516 | `Clifford.genTriple_iff` | `Clifford/Bridge.lean:110` | `genTriple_iff` |
| 517 | `Clifford.cD_eq_zero` | `Clifford/General.lean:32` | `cD_eq_zero` |
| 518 | `Clifford.chain4_cD` | `Clifford/General.lean:61` | `chain4_cD` |
| 519 | `Clifford.chain5_mem` | `Clifford/General.lean:87` | `chain5_mem` |
| 520 | `Clifford.Counter6.cx_genPosN` | `Clifford/Counter6.lean:33` | `cx_genPosN` |
| 521 | `Clifford.Counter6.not_chain6` | `Clifford/Counter6.lean:182` | `not_chain6` |
| 522 | `Clifford.Counter6.not_cliffordChain_six` | `Clifford/Counter6.lean:227` | `not_cliffordChain_six` |
| 523 | `Clifford.cliffordChain_three` | `Clifford/Classify.lean:43` | `cliffordChain_three` |
| 524 | `Clifford.not_chain_of_extends` | `Clifford/Classify.lean:57` | `not_chain_of_extends` |
| 525 | `Clifford.not_cliffordChain_of_six_le` | `Clifford/Classify.lean:219` | `not_cliffordChain_of_six_le` |
| 526 | `Clifford.cliffordChain_iff` | `Clifford/Classify.lean:227` | `cliffordChain_iff` |
| 527 | `Clifford.MorleyKernel.cliffordChainS_inf` | `Clifford/MorleyKernel.lean:5592` | `cliffordChainS_inf` |
| 528 | `Clifford.MorleyKernel.heven_inf_all` | `Clifford/MorleyKernel.lean:5586` | `heven_inf_all` |
| 529 | `Clifford.MorleyKernel.EvenCorner_proof` | `Clifford/MorleyKernel.lean:5584` | `EvenCorner_proof` |
| 530 | `Clifford.MorleyKernel.evenCornerQL_proof` | `Clifford/MorleyKernel.lean:5539` | `evenCornerQL_proof` |
| 531 | `Clifford.GenPosN.exists_snoc` | `Clifford/Classify.lean:167` | `GenPosN.exists_snoc` |
| 543 | `det3_eq_det` | `Clifford/BridgeL10.lean:32` | `det3_eq_det` |
| 544 | `crs_eq_det2` | `Clifford/BridgeL10.lean:38` | `crs_eq_det2` |
| 545 | `det_fin_four_eq_det4` | `Clifford/BridgeL10.lean:43` | `det_fin_four_eq_det4` |
| 546 | `det_fin_five_eq_det5` | `Clifford/BridgeL10.lean:53` | `det_fin_five_eq_det5` |
| 547 | `det4_eq_det` | `Clifford/BridgeL10.lean:63` | `det4_eq_det` |
| 548 | `det5_eq_det` | `Clifford/BridgeL10.lean:70` | `det5_eq_det` |
| 549 | `mN_eq_det` | `Clifford/BridgeL10.lean:78` | `mN_eq_det` |
| 550 | `mD_eq_det` | `Clifford/BridgeL10.lean:86` | `mD_eq_det` |
| 551 | `crossVec_eq_crossProduct` | `Clifford/BridgeL10.lean:95` | `crossVec_eq_crossProduct` |
| 552 | `miquel_eq_det_div` | `Clifford/BridgeL10.lean:105` | `miquel_eq_det_div` |
| 553 | `triP_eq_zero_iff_collinear` | `Clifford/BridgeL10.lean:117` | `triP_eq_zero_iff_collinear` |
| 554 | `colD_eq_zero_iff_collinear` | `Clifford/BridgeL10.lean:131` | `colD_eq_zero_iff_collinear` |
| 555 | `cD_eq_det` | `Clifford/BridgeL10.lean:137` | `cD_eq_det` |
| 556 | `cospherical_or_collinear_of_eqn` | `Clifford/BridgeL10.lean:145` | `cospherical_or_collinear_of_eqn` |
| 557 | `exists_eqn_of_cD` | `Clifford/BridgeL10.lean:189` | `exists_eqn_of_cD` |
| 558 | `cD_eq_zero_iff` | `Clifford/BridgeL10.lean:209` | `cD_eq_zero_iff` |
| 559 | `cycP_eq_cD` | `Clifford/BridgeL10.lean:221` | `cycP_eq_cD` |
| 560 | `cycP_eq_zero_iff` | `Clifford/BridgeL10.lean:239` | `cycP_eq_zero_iff` |
| 561 | `onCircle3_iff_cospherical` | `Clifford/BridgeL10.lean:248` | `onCircle3_iff_cospherical` |
| 580 | `second` | `Clifford/Basic.lean:394` | `second` |
| 581 | `Transversal` | `Clifford/Basic.lean:398` | `Transversal` |
| 582 | `GenTriple` | `Clifford/Basic.lean:402` | `GenTriple` |
| 583 | `lineS` | `Clifford/Mobius.lean:24` | `lineS` |
| 584 | `IsGCircleS` | `Clifford/Mobius.lean:28` | `IsGCircleS` |
| 585 | `ChainS` | `Clifford/Mobius.lean:35` | `ChainS` |
| 586 | `CliffordChainS` | `Clifford/Mobius.lean:46` | `CliffordChainS` |
| 587 | `chainS_of_chain` | `Clifford/Mobius.lean:119` | `chainS_of_chain` |
| 588 | `chainS_of_chain_pt` | `Clifford/Mobius.lean:152` | `chainS_of_chain_pt` |
| 589 | `cliffordChainS_of_le_five` | `Clifford/Mobius.lean:178` | `cliffordChainS_of_le_five` |
| 590 | `cliffordChainS_all_of` | `Clifford/Mobius.lean:330` | `cliffordChainS_all_of` |
| 591 | `chainS_six` | `Clifford/Mobius.lean:651` | `chainS_six` |
| 592 | `chainS_six_unique` | `Clifford/Mobius.lean:734` | `chainS_six_unique` |
| 593 | `chainS_six_iff` | `Clifford/Mobius.lean:779` | `chainS_six_iff` |
| 594 | `crossVec` | `Clifford/MorleyKernel.lean:159` | `crossVec` |
| 595 | `KP` | `Clifford/MorleyKernel.lean:214` | `KP` |
| 596 | `levelPointN` | `Clifford/MorleyKernel.lean:452` | `levelPointN` |
| 597 | `EptInf` | `Clifford/MorleyKernel.lean:2549` | `EptInf` |
| 598 | `h4_pt_inf` | `Clifford/MorleyKernel.lean:2566` | `h4_pt_inf` |
| 599 | `parent_crossVec_zero_of_mid` | `Clifford/MorleyKernel.lean:4998` | `parent_crossVec_zero_of_mid` |
| 600 | `EvenCorner` | `Clifford/MorleyKernel.lean:5253` | `EvenCorner` |
| 601 | `evenCorner_of_QL` | `Clifford/MorleyKernel.lean:5287` | `evenCorner_of_QL` |
| 602 | `EvenCornerQL` | `Clifford/MorleyKernel.lean:5317` | `EvenCornerQL` |
| 603 | `evenCorner_of_cornerQL` | `Clifford/MorleyKernel.lean:5325` | `evenCorner_of_cornerQL` |
| 604 | `evenCornerQL_proof` | `Clifford/MorleyKernel.lean:5539` | `evenCornerQL_proof` |
| 605 | `EvenCorner_proof` | `Clifford/MorleyKernel.lean:5584` | `EvenCorner_proof` |
| 606 | `heven_inf_all` | `Clifford/MorleyKernel.lean:5586` | `heven_inf_all` |
| 607 | `hodd_inf_all'` | `Clifford/MorleyKernel.lean:4643` | `hodd_inf_all'` |
| 608 | `cliffordChainS_inf` | `Clifford/MorleyKernel.lean:5592` | `cliffordChainS_inf` |
| 609 | `not_cliffordChain_of_six_le` | `Clifford/Classify.lean:219` | `not_cliffordChain_of_six_le` |

## What this gate does not check

Names and lines only. It does not compare signatures or hypotheses; the signature anchors for the statement declarations are the table rows of §3.3 above, which anchor a line, not a type. The hypothesis-level audit is layer 12's job, run on v0.1; the independent review rounds on v0.2, v0.3 and v0.7 are separately recorded (§5.11 of the draft).

