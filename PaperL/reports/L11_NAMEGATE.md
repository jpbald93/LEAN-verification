# Layer 11 — name/line gate, Paper L draft v0.3

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
| 473 | `Clifford.clifford_one` | `Clifford/Basic.lean:601` | `clifford_one` |
| 474 | `Clifford.clifford_two` | `Clifford/Basic.lean:693` | `clifford_two` |
| 475 | `Clifford.second_onCircleM_left` | `Clifford/Basic.lean:445` | `second_onCircleM_left` |
| 476 | `Clifford.second_onCircleM_right` | `Clifford/Basic.lean:449` | `second_onCircleM_right` |
| 477 | `Clifford.second_eq_coords` | `Clifford/Basic.lean:424` | `second_eq_coords` |
| 478 | `Clifford.onCircleM_iff` | `Clifford/Basic.lean:385` | `onCircleM_iff` |
| 479 | `Clifford.mD_ne_zero` | `Clifford/Basic.lean:520` | `mD_ne_zero` |
| 480 | `Clifford.clifford_two_clean` | `Clifford/Clean.lean:123` | `clifford_two_clean` |
| 481 | `Clifford.collinear_of_line` | `Clifford/Clean.lean:36` | `collinear_of_line` |
| 482 | `Clifford.miquel_all_eq` | `Clifford/Clean.lean:93` | `miquel_all_eq` |
| 483 | `Clifford.clifford_points_on` | `Clifford/Clean.lean:43` | `clifford_points_on` |
| 484 | `Clifford.mem_line_of` | `Clifford/Clean.lean:24` | `mem_line_of` |
| 485 | `Clifford.cliffordChain_four` | `Clifford/Clean.lean:226` | `cliffordChain_four` |
| 486 | `Clifford.cliffordChain_five` | `Clifford/Clean.lean:245` | `cliffordChain_five` |
| 487 | `Clifford.collinear_iff_conj_mul` | `Clifford/Bridge.lean:22` | `collinear_iff_conj_mul` |
| 488 | `Clifford.transversal_iff` | `Clifford/Bridge.lean:58` | `transversal_iff` |
| 489 | `Clifford.triP_ne_zero_iff` | `Clifford/Bridge.lean:62` | `triP_ne_zero_iff` |
| 490 | `Clifford.cross_second` | `Clifford/Bridge.lean:70` | `cross_second` |
| 491 | `Clifford.cycP_ne_zero_iff` | `Clifford/Bridge.lean:83` | `cycP_ne_zero_iff` |
| 492 | `Clifford.onCircleM_iff_mem_sphere` | `Clifford/Bridge.lean:104` | `onCircleM_iff_mem_sphere` |
| 493 | `Clifford.genTriple_iff` | `Clifford/Bridge.lean:110` | `genTriple_iff` |
| 494 | `Clifford.cD_eq_zero` | `Clifford/General.lean:32` | `cD_eq_zero` |
| 495 | `Clifford.chain4_cD` | `Clifford/General.lean:61` | `chain4_cD` |
| 496 | `Clifford.chain5_mem` | `Clifford/General.lean:87` | `chain5_mem` |
| 497 | `Clifford.Counter6.cx_genPosN` | `Clifford/Counter6.lean:33` | `cx_genPosN` |
| 498 | `Clifford.Counter6.not_chain6` | `Clifford/Counter6.lean:182` | `not_chain6` |
| 499 | `Clifford.Counter6.not_cliffordChain_six` | `Clifford/Counter6.lean:227` | `not_cliffordChain_six` |
| 500 | `Clifford.cliffordChain_three` | `Clifford/Classify.lean:43` | `cliffordChain_three` |
| 501 | `Clifford.not_chain_of_extends` | `Clifford/Classify.lean:57` | `not_chain_of_extends` |
| 502 | `Clifford.not_cliffordChain_of_six_le` | `Clifford/Classify.lean:219` | `not_cliffordChain_of_six_le` |
| 503 | `Clifford.cliffordChain_iff` | `Clifford/Classify.lean:227` | `cliffordChain_iff` |
| 504 | `Clifford.MorleyKernel.cliffordChainS_inf` | `Clifford/MorleyKernel.lean:5592` | `cliffordChainS_inf` |
| 505 | `Clifford.MorleyKernel.heven_inf_all` | `Clifford/MorleyKernel.lean:5586` | `heven_inf_all` |
| 506 | `Clifford.MorleyKernel.EvenCorner_proof` | `Clifford/MorleyKernel.lean:5584` | `EvenCorner_proof` |
| 507 | `Clifford.MorleyKernel.evenCornerQL_proof` | `Clifford/MorleyKernel.lean:5539` | `evenCornerQL_proof` |
| 508 | `Clifford.GenPosN.exists_snoc` | `Clifford/Classify.lean:167` | `GenPosN.exists_snoc` |
| 520 | `det3_eq_det` | `Clifford/BridgeL10.lean:32` | `det3_eq_det` |
| 521 | `crs_eq_det2` | `Clifford/BridgeL10.lean:38` | `crs_eq_det2` |
| 522 | `det_fin_four_eq_det4` | `Clifford/BridgeL10.lean:43` | `det_fin_four_eq_det4` |
| 523 | `det_fin_five_eq_det5` | `Clifford/BridgeL10.lean:53` | `det_fin_five_eq_det5` |
| 524 | `det4_eq_det` | `Clifford/BridgeL10.lean:63` | `det4_eq_det` |
| 525 | `det5_eq_det` | `Clifford/BridgeL10.lean:70` | `det5_eq_det` |
| 526 | `mN_eq_det` | `Clifford/BridgeL10.lean:78` | `mN_eq_det` |
| 527 | `mD_eq_det` | `Clifford/BridgeL10.lean:86` | `mD_eq_det` |
| 528 | `crossVec_eq_crossProduct` | `Clifford/BridgeL10.lean:95` | `crossVec_eq_crossProduct` |
| 529 | `miquel_eq_det_div` | `Clifford/BridgeL10.lean:105` | `miquel_eq_det_div` |
| 530 | `triP_eq_zero_iff_collinear` | `Clifford/BridgeL10.lean:117` | `triP_eq_zero_iff_collinear` |
| 531 | `colD_eq_zero_iff_collinear` | `Clifford/BridgeL10.lean:131` | `colD_eq_zero_iff_collinear` |
| 532 | `cD_eq_det` | `Clifford/BridgeL10.lean:137` | `cD_eq_det` |
| 533 | `cospherical_or_collinear_of_eqn` | `Clifford/BridgeL10.lean:145` | `cospherical_or_collinear_of_eqn` |
| 534 | `exists_eqn_of_cD` | `Clifford/BridgeL10.lean:189` | `exists_eqn_of_cD` |
| 535 | `cD_eq_zero_iff` | `Clifford/BridgeL10.lean:209` | `cD_eq_zero_iff` |
| 536 | `cycP_eq_cD` | `Clifford/BridgeL10.lean:221` | `cycP_eq_cD` |
| 537 | `cycP_eq_zero_iff` | `Clifford/BridgeL10.lean:239` | `cycP_eq_zero_iff` |
| 538 | `onCircle3_iff_cospherical` | `Clifford/BridgeL10.lean:248` | `onCircle3_iff_cospherical` |
| 557 | `second` | `Clifford/Basic.lean:394` | `second` |
| 558 | `Transversal` | `Clifford/Basic.lean:398` | `Transversal` |
| 559 | `GenTriple` | `Clifford/Basic.lean:402` | `GenTriple` |
| 560 | `lineS` | `Clifford/Mobius.lean:24` | `lineS` |
| 561 | `IsGCircleS` | `Clifford/Mobius.lean:28` | `IsGCircleS` |
| 562 | `ChainS` | `Clifford/Mobius.lean:35` | `ChainS` |
| 563 | `CliffordChainS` | `Clifford/Mobius.lean:46` | `CliffordChainS` |
| 564 | `chainS_of_chain` | `Clifford/Mobius.lean:119` | `chainS_of_chain` |
| 565 | `chainS_of_chain_pt` | `Clifford/Mobius.lean:152` | `chainS_of_chain_pt` |
| 566 | `cliffordChainS_of_le_five` | `Clifford/Mobius.lean:178` | `cliffordChainS_of_le_five` |
| 567 | `cliffordChainS_all_of` | `Clifford/Mobius.lean:330` | `cliffordChainS_all_of` |
| 568 | `chainS_six` | `Clifford/Mobius.lean:651` | `chainS_six` |
| 569 | `chainS_six_unique` | `Clifford/Mobius.lean:734` | `chainS_six_unique` |
| 570 | `chainS_six_iff` | `Clifford/Mobius.lean:779` | `chainS_six_iff` |
| 571 | `crossVec` | `Clifford/MorleyKernel.lean:159` | `crossVec` |
| 572 | `KP` | `Clifford/MorleyKernel.lean:214` | `KP` |
| 573 | `levelPointN` | `Clifford/MorleyKernel.lean:452` | `levelPointN` |
| 574 | `EptInf` | `Clifford/MorleyKernel.lean:2549` | `EptInf` |
| 575 | `h4_pt_inf` | `Clifford/MorleyKernel.lean:2566` | `h4_pt_inf` |
| 576 | `parent_crossVec_zero_of_mid` | `Clifford/MorleyKernel.lean:4998` | `parent_crossVec_zero_of_mid` |
| 577 | `EvenCorner` | `Clifford/MorleyKernel.lean:5253` | `EvenCorner` |
| 578 | `evenCorner_of_QL` | `Clifford/MorleyKernel.lean:5287` | `evenCorner_of_QL` |
| 579 | `EvenCornerQL` | `Clifford/MorleyKernel.lean:5317` | `EvenCornerQL` |
| 580 | `evenCorner_of_cornerQL` | `Clifford/MorleyKernel.lean:5325` | `evenCorner_of_cornerQL` |
| 581 | `evenCornerQL_proof` | `Clifford/MorleyKernel.lean:5539` | `evenCornerQL_proof` |
| 582 | `EvenCorner_proof` | `Clifford/MorleyKernel.lean:5584` | `EvenCorner_proof` |
| 583 | `heven_inf_all` | `Clifford/MorleyKernel.lean:5586` | `heven_inf_all` |
| 584 | `hodd_inf_all'` | `Clifford/MorleyKernel.lean:4643` | `hodd_inf_all'` |
| 585 | `cliffordChainS_inf` | `Clifford/MorleyKernel.lean:5592` | `cliffordChainS_inf` |
| 586 | `not_cliffordChain_of_six_le` | `Clifford/Classify.lean:219` | `not_cliffordChain_of_six_le` |

## What this gate does not check

Names and lines only. It does not compare signatures or hypotheses; the signature anchors for the statement declarations are the table rows of §3.3 above, which anchor a line, not a type. The hypothesis-level audit is layer 12's job and has run on v0.1 and v0.2 text only (§5.11 of the draft).

