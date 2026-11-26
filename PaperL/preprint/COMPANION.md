# Paper L — verification record and provenance

**Companion to “Clifford’s chain for every n: point–circle configurations on the Riemann sphere,
formalised in Lean 4” (v1.2, 26 November 2026).**

This document is the audit trail behind the paper. The paper itself carries only the mathematics and
the statements about what was checked; everything that would turn it into a test report lives here:
the per-file hashes of the pinned tree, the gate's declaration list with file and line, the definition
bridges, the mutation and contradiction runs with their survivors, the satisfiability runs on two
machines, the blind-restatement comparison, the artefact provenance, and the history of the document.
Every figure quoted here is a recorded figure; nothing is estimated, and every place where a claim
rests on a numerical or on a single-machine run says so.

Section numbering here does not follow the paper's. §1 is the tree and the citation gate, §2 the
verification record, §3 the coverage limits in full, Appendix A the provenance, Appendix B the layer
table and Appendix C the history. Where the text needs to point at the paper, it says “the paper's
§n”.

Two conventions. **std** $=$ `[propext, Classical.choice, Quot.sound]`, Lean's standard axioms. A
*hyp-free* or *no-hypothesis* row of the contradiction or satisfiability runs means the declaration
carries no hypothesis to probe or to inhabit; it is not evidence either way.

What the paper claims, and what this record is here to support, are five statements: the library
states the chain for every $n$ in one declaration (`cliffordChainS_all`); the terminal theorems
depend on **std** only; the finite-plane predicate is false for $n \ge 6$ and the sphere repairs it;
the even side is proved in full, corner included; and the even-level point is not unique, so the
existential recursion is the correct statement. Section 2 of this record gives the instrument behind
each of them.

---

## 1. The tree, the toolchain and the citation gate

The development is a git repository, published at
[github.com/jpbald93/paperl_clifford_chain](https://github.com/jpbald93/paperl_clifford_chain), with
the audited tree at commit `3df056f` (v1.2, 159 files). The per-file sha256 table below is the identity of
that tree and the table every citation in this record was checked against; the eleven hashes were
re-checked against a fresh clone of the published repository on 2026-11-26, immediately after the
push. Toolchain:
`leanprover/lean4:v4.33.1` (`lean-toolchain`); Mathlib pin
`0df444a360eaa60ab8c11dca51a86af692955474` (`lake-manifest.json`). File sizes and hashes of the ten
source files plus the gate:

| file | lines | sha256 |
|---|---|---|
| `Clifford/Basic.lean` | 724 | `d5c14edbf2da8ec8288484b4eeee54e30e85cf04e5c440c406b4c7144ca0cb16` |
| `Clifford/General.lean` | 99 | `90b42ad2f407f49b7ebc955573af3823727cef5403047ccd2467222afd36eeff` |
| `Clifford/Bridge.lean` | 121 | `93eb80b639791dc7e271249a79e0439dd3fd08c831eb71e367129c52c8cecf5b` |
| `Clifford/Clean.lean` | 257 | `2a7cf40b4c473e56c97db8b1485aa5ad468c9cbb5c9a56b5b7ac9adaf33cc463` |
| `Clifford/Mobius.lean` | 787 | `f8c9f013188f7767b8c2f5850b0f761cfb689d0e490a782d5c9e10ddaec83200` |
| `Clifford/Counter6.lean` | 233 | `d6bf1cc913841fd487c539c61e4db62054e62d4b861af3a3cb9eaac8cf35d57a` |
| `Clifford/Classify.lean` | 239 | `ba4fc1b3c567f5d69ca33ea2bcbab0dfaed3a54a779e3405efdb4241be65b83b` |
| `Clifford/MorleyKernel.lean` | 5607 | `1dfe2f13df852e927015dd433eed51b41cc5ba584cbc6e4acb4525b6d5297ba6` |
| `Clifford/BridgeL10.lean` | 251 | `097722f3d2ff994965dcb1ccff5180d8a62404ea3dfc362bef345934c1ab6054` |
| `Clifford.lean` (root) | — | `8bb0f5f0d4663cb4e026980d88fae6e24d0c2046b32062fb6cce25a9e465f046` |
| `gate.sh` | — | `445a7093332fd04144e050328364e0fd8b51af43d556d2929e96f81da3fda599` |

Total: 8,318 lines of Lean across the nine `Clifford/*.lean` files, of which the layer-10 bridge file
contributes 251 (`MorleyKernel.lean` alone is 5,607 lines: 5,610 at v1.1, less the two lines of `hQ0`
and the one of `_hP0` removed in v1.2. Before promotion the scratch file was 5,611 — a 5,344-line prefix
plus the 267-line round-26 proof — and the two gate-forced edits of §2 took it to 5,610).

Every `file:line` citation in this record — prose, code comments, comma lists and tables alike — is
machine-checked by `namegate.py` (layer 11, `L11_NAMEGATE.md`): **67 occurrences of 63 distinct
`Clifford/File.lean:N` pairs** on v1.2 (68 / 64 on v1.0, 66 / 63 on v1.1), each resolving to a declaration in the pinned tree, and the 34 checks
written in the form `` `name` (`file:line`) `` additionally checked against the name the paper
attributes to them. (In the v0.12 draft the same gate read 143 occurrences of 98 distinct pairs: the
twelve declaration tables that carried most of them are in this record now, not in the paper.) Bare single-line citations have been removed; the eight "lines A–B" range citations left (four distinct spans)
name a region of a file or of a log, not a declaration. The script counts a citation inside a table
row or a code comment like any other, which is what the earlier 66-citation figure did not do (it
read only backticked citations in prose). What the gate checks is **names and lines, not
signatures**: §1.3 anchors the carrier and statement declarations, paper §2.1 quotes their definitions and
paper §2.3–2.4 their statements, and the hypothesis-level audit is layer 12's (`L12_REVIEW.md`, which
reviewed v0.1 — see §3.11).

**Availability.** The repository holds the ten Lean source files, `gate.sh`, `tests/tamper.sh`,
`lakefile.toml`, `lean-toolchain` and `lake-manifest.json` at the pinned commit, and the two check
files of paper §1.1 and §3.4 in `check/` on `main`. `lake exe cache get` fetches the prebuilt Mathlib,
`lake build` compiles the library (the manifest, not the lakefile's version tag, fixes Mathlib at
`0df444a3…`), `./gate.sh` prints the gate verdict and the `#print axioms` report for all 37 required
declarations, and
`bash tests/tamper.sh` runs the eight-test tamper suite; the two `.bak-r26` files are the pre-promotion
copies, kept so the round-26 edits of §2 can be audited. The paper-side material — the layer reports,
the review rounds and their triages, the layer-13/14/15 comparisons, the mutation, contradiction and
satisfiability reports, and `namegate.py` — is published in the `PaperL` folder of
[github.com/jpbald93/LEAN-verification](https://github.com/jpbald93/LEAN-verification), arranged as
`preprint/`, `reports/`, `reviews/`, `layer0/`, `layer13/`, `check/` and `evidence/`; Appendix A gives
the mapping from the artifact-relative paths this paper uses.

### 1.1 The 37 gate declarations

The gate (`gate.sh`) lists 37 required declarations; the anchor table (`layer11/ANCHORS.md`) resolves
all 37 to file:line, with kind and axiom list, by parsing the gate list, `Clifford/BridgeL10.lean` and
the two layer reports. Every one depends on **std** only.

| # | declaration | file:line | kind |
|---|---|---|---|
| 1 | `Clifford.clifford_one` | `Clifford/Basic.lean:601` | theorem |
| 2 | `Clifford.clifford_two` | `Clifford/Basic.lean:693` | theorem |
| 3 | `Clifford.second_onCircleM_left` | `Clifford/Basic.lean:445` | theorem |
| 4 | `Clifford.second_onCircleM_right` | `Clifford/Basic.lean:449` | theorem |
| 5 | `Clifford.second_eq_coords` | `Clifford/Basic.lean:424` | theorem |
| 6 | `Clifford.onCircleM_iff` | `Clifford/Basic.lean:385` | theorem |
| 7 | `Clifford.mD_ne_zero` | `Clifford/Basic.lean:520` | theorem |
| 8 | `Clifford.clifford_two_clean` | `Clifford/Clean.lean:123` | theorem |
| 9 | `Clifford.collinear_of_line` | `Clifford/Clean.lean:36` | theorem |
| 10 | `Clifford.miquel_all_eq` | `Clifford/Clean.lean:93` | theorem |
| 11 | `Clifford.clifford_points_on` | `Clifford/Clean.lean:43` | theorem |
| 12 | `Clifford.mem_line_of` | `Clifford/Clean.lean:24` | theorem |
| 13 | `Clifford.cliffordChain_four` | `Clifford/Clean.lean:226` | theorem |
| 14 | `Clifford.cliffordChain_five` | `Clifford/Clean.lean:245` | theorem |
| 15 | `Clifford.collinear_iff_conj_mul` | `Clifford/Bridge.lean:22` | theorem |
| 16 | `Clifford.transversal_iff` | `Clifford/Bridge.lean:58` | theorem |
| 17 | `Clifford.triP_ne_zero_iff` | `Clifford/Bridge.lean:62` | theorem |
| 18 | `Clifford.cross_second` | `Clifford/Bridge.lean:70` | theorem |
| 19 | `Clifford.cycP_ne_zero_iff` | `Clifford/Bridge.lean:83` | theorem |
| 20 | `Clifford.onCircleM_iff_mem_sphere` | `Clifford/Bridge.lean:104` | theorem |
| 21 | `Clifford.genTriple_iff` | `Clifford/Bridge.lean:110` | theorem |
| 22 | `Clifford.cD_eq_zero` | `Clifford/General.lean:32` | theorem |
| 23 | `Clifford.chain4_cD` | `Clifford/General.lean:61` | theorem |
| 24 | `Clifford.chain5_mem` | `Clifford/General.lean:87` | theorem |
| 25 | `Clifford.Counter6.cx_genPosN` | `Clifford/Counter6.lean:33` | theorem |
| 26 | `Clifford.Counter6.not_chain6` | `Clifford/Counter6.lean:182` | theorem |
| 27 | `Clifford.Counter6.not_cliffordChain_six` | `Clifford/Counter6.lean:227` | theorem |
| 28 | `Clifford.cliffordChain_three` | `Clifford/Classify.lean:43` | theorem |
| 29 | `Clifford.not_chain_of_extends` | `Clifford/Classify.lean:57` | theorem |
| 30 | `Clifford.not_cliffordChain_of_six_le` | `Clifford/Classify.lean:219` | theorem |
| 31 | `Clifford.cliffordChain_iff` | `Clifford/Classify.lean:227` | theorem |
| 32 | `Clifford.MorleyKernel.cliffordChainS_inf` | `Clifford/MorleyKernel.lean:5589` | theorem |
| 33 | `Clifford.MorleyKernel.heven_inf_all` | `Clifford/MorleyKernel.lean:5583` | theorem |
| 34 | `Clifford.MorleyKernel.EvenCorner_proof` | `Clifford/MorleyKernel.lean:5581` | theorem |
| 35 | `Clifford.MorleyKernel.evenCornerQL_proof` | `Clifford/MorleyKernel.lean:5536` | theorem |
| 36 | `Clifford.GenPosN.exists_snoc` | `Clifford/Classify.lean:167` | theorem |
| 37 | `Clifford.MorleyKernel.cliffordChainS_all` | `Clifford/MorleyKernel.lean:5596` | theorem |

(`GenPosN.exists_snoc` is namespace-qualified in its declaration, which is why a naive
`theorem <short> match` misses it; the anchor harvester records that explicitly.)

### 1.2 The 19 definition bridges

`Clifford/BridgeL10.lean` adds 19 theorems, each with a docstring, all in `namespace Clifford`, all
on **std**, none of them in the gate's REQUIRED list. They tie the paper's own notions to Mathlib:

| # | declaration | file:line | notion → Mathlib counterpart |
|---|---|---|---|
| L10.1 | `det3_eq_det` | `Clifford/BridgeL10.lean:32` | `det3` → `Matrix.det` (Fin 3) |
| L10.2 | `crs_eq_det2` | `Clifford/BridgeL10.lean:38` | `crs` → `Matrix.det` (Fin 2) |
| L10.3 | `det_fin_four_eq_det4` | `Clifford/BridgeL10.lean:43` | any `Matrix (Fin 4) (Fin 4) R` → `det4` |
| L10.4 | `det_fin_five_eq_det5` | `Clifford/BridgeL10.lean:53` | any `Matrix (Fin 5) (Fin 5) R` → `det5` |
| L10.5 | `det4_eq_det` | `Clifford/BridgeL10.lean:63` | `det4` → `Matrix.det` |
| L10.6 | `det5_eq_det` | `Clifford/BridgeL10.lean:70` | `det5` → `Matrix.det` |
| L10.7 | `mN_eq_det` | `Clifford/BridgeL10.lean:78` | `mN` → `Matrix.det` |
| L10.8 | `mD_eq_det` | `Clifford/BridgeL10.lean:86` | `mD` → `Matrix.det` |
| L10.9 | `crossVec_eq_crossProduct` | `Clifford/BridgeL10.lean:95` | `crossVec` (2×3 matrices only) → `Mathlib` `crossProduct` |
| L10.10 | `miquel_eq_det_div` | `Clifford/BridgeL10.lean:105` | `miquel` → ratio of two `Matrix.det` |
| L10.11 | `triP_eq_zero_iff_collinear` | `Clifford/BridgeL10.lean:117` | `triP = 0` ↔ `Collinear ℝ` |
| L10.12 | `colD_eq_zero_iff_collinear` | `Clifford/BridgeL10.lean:131` | `colD = 0` ↔ `Collinear ℝ` |
| L10.13 | `cD_eq_det` | `Clifford/BridgeL10.lean:137` | `cD` → `Matrix.det` |
| L10.14 | `cospherical_or_collinear_of_eqn` | `Clifford/BridgeL10.lean:145` | from an explicit equation to `Cospherical ∨ Collinear` |
| L10.15 | `exists_eqn_of_cD` | `Clifford/BridgeL10.lean:189` | `cD` → real linear equation `A|p|²+Bp.re+Cp.im+D=0` |
| L10.16 | `cD_eq_zero_iff` | `Clifford/BridgeL10.lean:209` | `cD = 0` ↔ `Cospherical ∨ Collinear` (no extra hypothesis) |
| L10.17 | `cycP_eq_cD` | `Clifford/BridgeL10.lean:221` | `cycP = −2·I·cD 0 a b c` |
| L10.18 | `cycP_eq_zero_iff` | `Clifford/BridgeL10.lean:239` | `cycP = 0` ↔ `Cospherical ∨ Collinear` of `{0,a,b,c}` |
| L10.19 | `onCircle3_iff_cospherical` | `Clifford/BridgeL10.lean:248` | `OnCircle3` ↔ `Cospherical` (definitional) |

Two points deserve to be in the paper rather than only in the report. First, `cD_eq_zero_iff` needs
**no** nondegeneracy hypothesis: degenerate point sets fall under one of the two disjuncts, and the
`←` direction is `Clean.exists_gcircle` plus `General.cD_eq_zero`, while `→` goes through a nonzero
kernel vector, a real equation, and a circle if `A ≠ 0` and a line if `A = 0`. This is the lemma
that ties `cD = 0` to the standard `Cospherical ∨ Collinear` reading of "four points on a circle"; it
does not by itself bridge the sphere predicate `IsGCircleS` (§3.6). Second, `cycP_eq_cD`: the first
sign guess `+2·I` was false (`ring` failed with goal `LHS = −LHS`) and the correct factor is `−2·I`;
the report records that, and the draft should not hide it — a formalisation account that reports only
its successes is not a verification record.

### 1.3 The statement declarations behind paper §2

These are the declarations the prose of §1–2 leans on and that the 37-row gate list does not cover;
each is checked at the cited line by the same layer-11 script that checks the prose citations.

| # | declaration | file:line | role in §1–2 |
|---|---|---|---|
| S1 | `second` | `Clifford/Basic.lean:394` | second intersection of two circles |
| S2 | `Transversal` | `Clifford/Basic.lean:398` | pairwise non-collinearity of `M, c, d` |
| S3 | `GenTriple` | `Clifford/Basic.lean:402` | the two conjuncts of triple general position |
| S4 | `lineS` | `Clifford/Mobius.lean:24` | a line plus `∞` |
| S5 | `IsGCircleS` | `Clifford/Mobius.lean:28` | generalized circles on the sphere |
| S6 | `ChainS` | `Clifford/Mobius.lean:35` | the sphere recursion |
| S7 | `CliffordChainS` | `Clifford/Mobius.lean:46` | existence of a level-n object |
| S8 | `chainS_of_chain` | `Clifford/Mobius.lean:119` | transport of a finite chain object |
| S9 | `chainS_of_chain_pt` | `Clifford/Mobius.lean:152` | transport of a singleton chain object |
| S10 | `cliffordChainS_of_le_five` | `Clifford/Mobius.lean:178` | the sphere base cases `n ≤ 5` |
| S11 | `cliffordChainS_all_of` | `Clifford/Mobius.lean:330` | the two-step induction to `ChainS` |
| S12 | `chainS_six` | `Clifford/Mobius.lean:651` | level-6 repair of the six-centre witness |
| S13 | `chainS_six_unique` | `Clifford/Mobius.lean:734` | uniqueness there (this configuration only) |
| S14 | `chainS_six_iff` | `Clifford/Mobius.lean:779` | the iff form of S12–S13 |
| S15 | `crossVec` | `Clifford/MorleyKernel.lean:159` | signed maximal minors |
| S16 | `KP` | `Clifford/MorleyKernel.lean:214` | row-scaled Morley matrix |
| S17 | `levelPointN` | `Clifford/MorleyKernel.lean:452` | `−v_last / v_{n/2}` |
| S18 | `EptInf` | `Clifford/MorleyKernel.lean:2549` | the totalized projective level point |
| S19 | `h4_pt_inf` | `Clifford/MorleyKernel.lean:2566` | the level-4 certificate for `EptInf` |
| S20 | `parent_crossVec_zero_of_mid` | `Clifford/MorleyKernel.lean:4995` | `V = 0` in the corner |
| S21 | `EvenCorner` | `Clifford/MorleyKernel.lean:5250` | the geometric corner statement |
| S22 | `evenCorner_of_QL` | `Clifford/MorleyKernel.lean:5284` | corner from the scalar identity |
| S23 | `EvenCornerQL` | `Clifford/MorleyKernel.lean:5314` | the scalar identity |
| S24 | `evenCorner_of_cornerQL` | `Clifford/MorleyKernel.lean:5322` | packaging |
| S25 | `evenCornerQL_proof` | `Clifford/MorleyKernel.lean:5536` | round-26 proof of S23 |
| S26 | `EvenCorner_proof` | `Clifford/MorleyKernel.lean:5581` | S21 from S25 |
| S27 | `heven_inf_all` | `Clifford/MorleyKernel.lean:5583` | the even payload |
| S28 | `hodd_inf_all'` | `Clifford/MorleyKernel.lean:4642` | the odd payload |
| S29 | `cliffordChainS_inf` | `Clifford/MorleyKernel.lean:5589` | the headline, `n ≥ 3` |
| S30 | `not_cliffordChain_of_six_le` | `Clifford/Classify.lean:219` | finite-plane failure for `n ≥ 6` |

The gate's earlier omission of `ChainS`, `CliffordChainS`, `lineS`, `IsGCircleS`, `chainS_six*`,
`evenCorner_of_QL` and `evenCorner_of_cornerQL` is what S1–S30 close; it is still a name-and-line
check, not a signature audit, and `L12_REVIEW.md` did not perform one (it could not inspect those
types at the time). v0.3 quotes the definitions themselves in paper §2.1, so a reader can compare the
paper's prose against the code without running Lean.

---

## 2. The verification record

All figures below are quoted from the recorded reports; the runner is the `leancheck` battery that
was developed for this paper series. Host: `jack`. Report
`~/leancheck/reports/paperL_jack_20261119_020713.md` (+ `.log`); the verdict table is computed from
`~/leancheck/out/paperL_jack/results.jsonl` (935 rows) and `~/lc_gap_paperL_jack/results.jsonl`
(771 rows), independently recounted. The battery ran with `--fast` against the promoted library at
`~/paperL_jack`: `Clifford/MorleyKernel.lean` sha `dce7b011…`, gate REQUIRED 37. Wall clock:
02:07:13Z → 19:28:24Z on 2026-11-19, **17 h 21 min**, and the verdict line is
`LEANCHECK DONE Thu Nov 19 07:28:24 PM UTC 2026`.

| layer | what it checks | result |
|---|---|---|
| 1 | gate: every REQUIRED declaration present, `#print axioms` ⊆ std | **PASS (37 declarations, standard axioms only)** |
| 2 | tampering: 8 hand-made cheat attempts must be rejected | **8/8 rejected** — the log records `ALL TAMPERING TESTS REJECTED` |
| baseline | the 8 audited source files compile as given | **8/8 ok** |
| 4 | mutation: inject a wrong constant at a declaration and require a downstream error | battery (2026-11-19, re-run 2026-11-25): **535 decisive kills + 95 timeout/heartbeat**, **1 SURVIVED**, **0 error-unattributed** over 259 declarations of 8 source files, only 61 of `MorleyKernel.lean`'s 343; late block (2026-11-25): **872 kills + 3 timeout**, **16 SURVIVED**, 0 unattributed over 257 further `MorleyKernel` declarations — together **318 of the 343** in that file (see §3.1) |
| 5 | contradiction probes: try to prove `False` from a theorem's hypotheses with limited tactics | **0 CONTRADICTORY** over 551 of the 577 declarations (310 `ok`, 218 no-hypothesis, 22 timeout, 1 probe-invalid, 0 error-unattributed): the battery's 294 plus a late block over 257 further `MorleyKernel` declarations at lines 816–5586 (163 `ok`, 93 no-hypothesis, 1 probe-invalid). `ok` means the limited search failed, not that satisfiability was certified (§3.2) |
| 6 | ablation: delete a hypothesis and check whether the proof still compiles | **501 needed / 8 unused**, 0 skipped, 0 timeout, 0 bad-control, over 262 declarations |
| 7 | linter (library files) | **0 warnings in 8 files**; the scratch leg was not run by the battery and is quoted from `layer10/REPORT_L10.md` (§2 below) |
| 8 | satisfiability certification | **run on two machines, 2026-11-25/26**: jack **400 of 596 (67.1%)**, john **394 of 584 (67.5%)** certified; across the 577 declarations both ran, **397 (68.8%)** are certified by at least one and 180 by neither; 0 stmt-invalid, nothing refuted (§3.2) |
| 8b | theorem ↔ witness linkage | **0 links** — neither tree contains hand-written `*_sat` witnesses, so there is nothing to link (§3.2) |
| 9 | notion inventory: which notions have a Mathlib bridge | **137 notions, 24 flagged `has-bridge`, 113 not** — a heuristic flag, not a semantic count (§3.6) |
| 10 | definition bridges (`BridgeL10.lean`) | 19 theorems; **13 of the 113** moved to bridged; 25 reclassified INTERNAL; **75 remain unbridged** (arithmetic, same caveat) |
| 11 | name/line anchors for the paper | **PASS** — 67 occurrences / 63 distinct citations on v1.2, 34 attribution checks, all resolving (§1) |

The eight tamper tests are `sorry`, `ax2line`, `evalfake`, `macro`, `wrap` (nonstandard-axiom catch),
`falsehyp`, `cleanand`, `classify6`; the log reports `ALL TAMPERING TESTS REJECTED` (there is no
`TAMPER_RC` string in it, and none is claimed here). The gate is not a build-time check alone: it
also pins the axiom set, which is why the two later edits in round 26b — inlining two tactic macros
at all **13 use sites** (8 `fin_idx` + 5 `fin_idxO`; the 15 identifier occurrences include their two
definition lines), and rewording three comments containing the word "prefix" (module comments in the
promoted file, plus one docstring moved into a module comment) — were forced by the gate rather than
by the mathematics (a `macro` could redefine `#print axioms`; `\bprefix\b` is a forbidden token).
Both edits are recorded, and the 267-line round-26 proof is untouched by them.

The single mutation survivor of the 2026-11-19 battery is `cliffordChain_one`; the late block's
sixteen are analysed in §3.1. The injected mutant is exactly
`CliffordChain 1 → CliffordChain 2` (row `lit1->2@15`): a different but equally true statement, with
a proof term of the same shape, so it survives compilation of its own declaration and the
discrepancy surfaces downstream inside `cliffordChain_iff` (`Clifford/Classify.lean:227`), which needs the
`n = 1` instance and finds the wrong type. That is a limitation of mutation testing at a declaration
whose statement is level-parametric, not a hole in the proof; nothing in the battery classifies it as
either.

Build receipts at the pin. On jack: `lake build Clifford` rc = 0 (8,716 jobs at the layer-10
collection), `gate.sh` PASS (37 declarations, standard axioms only), `bash tests/tamper.sh` 8/8 rejected.
The scratch file `scratch/ChainEvenCornerQL.lean` has 5,611 lines, sha `b4d07119…`, its first 5,344
lines are byte-identical to `scratch/ChainEvenCorner.lean`, and its last 267 lines are byte-identical
to the promoted suffix; it compiles in **58 s on jack**, and its `#print axioms` block names all four
new theorems. The promotion timings quoted in the round-26/26b notes (71 s jack, 74 s john) and the
john-side build, gate, tamper, axiom and scratch receipts (**67 s john**) are recorded in
`notes/math-papers.md` and were **not** re-verified for this record: john was unreachable from
the evening of 2026-11-19 until 2026-11-25, his published battery report carries no round-26 timing,
and only the
statement layers were re-run on his machine since (§3.5). They are labelled accordingly in §3.5 and
Appendix A.

Two harness defects from the same overload event must be stated, because they explain two rows of the
table rather than a gap in the library. The report's `## Layers 4,5,8` section is empty: the batch
driver died with a `UnicodeDecodeError` on a child's stdout cut mid-character, and the traceback sits
at lines 14–17 of the `.log`, so the **mutation/contradiction child's section is cut off there**; the
log itself continues to its last line and ends with `LEANCHECK DONE`, and the verdict table is correct
because it is computed from `results.jsonl`. And the scratch linter leg of layer 7 failed with
`FileNotFoundError: 'lake'` because the subprocess did not inherit the elan PATH; it was re-run
correctly in layer 10 (`layer10/REPORT_L10.md` step 4) and returned **0 warnings across 37 files**, of
which 31 compile — the 6 failures are 3 stale library copies (`G.lean`, `General.lean`, `T.lean`) and
3 broken fragments (`E.lean`, a renamed Mathlib constant; `j28_test.lean`, an unknown module prefix;
`j31_tail.lean`, a fragment without imports).

One ordering fact a reader should have: the battery ran on 2026-11-19 from 02:07Z to 19:28Z, and
`Clifford/BridgeL10.lean` and the new root were written at 21:18Z the same day. Layers 2–9 therefore
never saw the bridge file; it is covered only by the build, gate, tamper and axiom outputs recorded in
`layer10/REPORT_L10.md`, which post-date it.

---

## 3. Coverage limits

A formalisation paper is only as good as its account of what it has not done. These are the limits,
in descending order of consequence for a reader.

1. **Mutation and contradiction probes now reach the late block, and neither covers every declaration.** The eight audited
   source files contain 577 `theorem`/`lemma` declarations. Mutation ran twice: on 2026-11-19 over
   259 declarations (198 outside `MorleyKernel.lean` and 61 of its 343, all in lines 33–806), and in
   a late block on 2026-11-24/25 over 257 further `MorleyKernel.lean` declarations, all in lines
   816–5586 and disjoint from the first set. `MorleyKernel.lean` therefore has **318 of its 343
   declarations (93%)** under mutation, including the round 19–26 material: `heven_kernel`
   (`Clifford/MorleyKernel.lean:4696`), `heven_line_of_P0` (`Clifford/MorleyKernel.lean:5134`),
   `evenCorner_of_QL`, `heven_inf_all` and `polyF_coeff_top` (`Clifford/MorleyKernel.lean:5496`)
   each carry mutant rows. The late block contributes 891 mutant rows — 872 killed outright, 3 killed by heartbeat
   timeout, **16 survivors**, 0 unattributed — against the first battery's 631 rows over all eight
   files. Of the sixteen late-block survivors, nine compile their own mutant proof and are caught
   downstream (at lines 1647, 2761, 3922 and 5574); three change `2*0+5` to `3*0+5` in a `k = 0`
   statement, where both are 5, so the mutant is the same proposition and the row is vacuous; and
   four alter the conjunct `u ≠ 0` in the *conclusion* of `child_line_of_parent_mid_zero` — a branch
   lemma whose hypotheses are inconsistent on purpose (`hmid` and `P₀ ≠ 0` force `V = 0`, contradicting
   `hv`), so no proof obligation reaches the mutant (§3.8). **No survivor is a hole in a headline statement.** The 25 declarations with no mutant on
   jack split in two: six primed names that jack's collector skips
   (`d7_children_gcircleS'`/`''`, `hodd_inf'`, `hodd_inf_all'`, `hodd_one_P0_line'`,
   `p0_levelpts_collinear'`), which john's second-machine run mutates and kills every mutant of, and
   nineteen on which the generator produced no mutant — `evenCornerQL_proof`, `EvenCorner_proof`
   and `cliffordChainS_inf` are of that kind — which are not covered by mutation: they rest on the
   gate, tamper and axiom checks and, where the declaration carries its hypotheses as explicit
   binders, on the satisfiability layer — a hypothesis packed inside a `Prop` definition is invisible
   to both (§3.2). Contradiction probes ran in two blocks as well: the battery's 294 declarations, all 234
   outside `MorleyKernel.lean` and 60 of its 343, every one before line 816, and on 2026-11-25 a late
   block over 257 further `MorleyKernel` declarations at lines 816–5592 — 163 `ok`, 93 with no
   hypothesis and one `probe-invalid`, **0 CONTRADICTORY**. That is **551 of the 577 declarations
   (95.4%)** probed. The 26 without a probe row are the six primed names jack's collector skips
   (`d7_children_gcircleS'`/`''`, `hodd_inf'`, `hodd_inf_all'`, `hodd_one_P0_line'`,
   `p0_levelpts_collinear'`) and twenty further `GenPosN`/determinant lemmas and definitional
   restatements (`cliffordChainS_inf` — the headline, not a corollary — `cliffordChainS_of_corner`, `cliffordChainS_of_inf`,
   `cliffordChainS_of_inf'`, `evenCornerQL_proof`, `EvenCorner_proof`, `evenCorner_of_cornerQL`,
   `parent_on_child_line`, `child_det_M7`, `child_det_MN`, `parent_det_MN`, `c5_genPosN`,
   `c6_genPosN`, `d7_genPosN`, `stepEven_gen`, `stepOdd_core`, `blockRev_val`, `child_line_P0`,
   `child_line_P0N`, `p0_levelpts_gcircleS`). One late-block row is invalid rather than passing: for
   `subfamily_P0_zero_gen` the `True` control itself failed to compile (`conj` is bound as an
   implicit variable under `autoImplicit`), so the probe never ran and no contradiction claim is
   made for it. The 26 are a limit of jack's collector only: john's like-for-like receipt probes all
   343 `MorleyKernel` declarations, these 26 included, and reports 0 CONTRADICTORY
   (`layer0/john_receipt_20261119/RECEIPT_VERDICT.md`). **OPEN**: an expected-job manifest for the
   late block.

2. **Satisfiability was run on two machines; about a third of the declarations remain unresolved.** The
   2026-11-19 battery ran with `--fast`, which replaces the job list with `sat = []`: that row was a
   disabled layer, not an empty candidate class. The layer was then run properly on 2026-11-25/26 —
   jack over 596 declarations (13 h 04 min) certifies **400 (67.1%)**, john over 584 (10 h 17 min)
   certifies **394 (67.5%)** — and nothing was refuted: `stmt-invalid` is 0 on both machines, so no
   declaration's existential statement failed to elaborate. Vacuity is not inferred from that count.
   The 397 split by statement class: **210** have no hypothesis to inhabit, **119** have no binders
   at all (the statement reduced to `True`), and **68** inhabit a hypothesis of the declaration. So
   layer 8 witnesses the hypotheses of **68** of the 577 shared declarations, not 397 — and a
   hypothesis packed inside a `Prop` definition (`EvenCornerQL`, `EvenCorner`, the payloads) is
   invisible to it, exactly as it is to layer 6. The one declaration whose hypotheses are the corner
   itself, `parent_crossVec_zero_of_mid`, is unresolved on both machines, so whether the corner is
   inhabited rests on the numerical witness of paper §1.1, not on layer 8; for the remaining 180 nothing is
   claimed either way. Across
   the **577 declarations both machines ran, 560 agree** on the verdict class, 17 differ only in
   which machine found a witness, and **397 (68.8%) are certified by at least one machine**; **180**
   are unresolved on both. A certificate is an accepted instance: Lean checks a proof of
   `∃ binders, True` whose binders include each of the declaration's hypotheses as a `Prop`-valued
   binder, so the certificate must *exhibit an inhabitant of every hypothesis*; that is what makes it
   a satisfiability witness rather than an assumption of what it is meant to certify. An `unresolved` row is a failed
   search — deterministic patterns plus at most three model proposals — and is **not** a refutation;
   it says nothing about the declaration one way or the other. A curated witness table (concrete data
   values supplied per declaration, 107 of the more tractable unresolved names, jack, 2026-11-26)
   closed **none**: 88 of the 107 fail because the instrument cannot discharge the propositional side
   conditions of the hypotheses — its simp set leaves `(starRingEnd ℂ) 2` unreduced and `decide`
   cannot discharge equalities over `ℂ` — so a table helps only together with a per-family proof
   library for `Transversal`, `GenTriple`, `GenPos4/5`, `Chain 4 ![…]` and `mD ≠ 0`. Layer 5's `ok`
   remains a failed search for `False`, not a satisfiability certificate, and layer 8b reports 0 links
   because neither tree contains a hand-written `*_sat` witness. **OPEN**: the 180 unresolved
   declarations, with the per-family proof library the table would need.
3. **The layer-13 comparison covers all seven statements, and the bridge layer now closes two rows in
   both directions.** `L13_FULL_COMPARE.md` and `layer13/BlindCompareFull.lean` (compile exit 0,
   2.8 s, no `sorry`) compare the blind writer's real types — `BlindGenPos`, `BlindSecond`,
   `BlindIsGCircle` with `0 < r`, `BlindCliffordP`, `BlindCliffordFin` — against the paired library
   theorems. Row S6 is a **definitional** difference: the two sides assert the same geometric content over
   independently invented predicates, and the bridge proves it in both directions. S7 is definitional
   in its predicates but stronger in its hypothesis — its writer again quantifies over `BlindGenPos`,
   as S1 does — and it is closed only because `N7_RB` proves the writer's statement outright, without
   passing through the library theorem. Rows S4
   and S5 are not: the writer's finite-plane variant (`BlindCliffordFin`) requires every level object
   to lie in `BlindPlane`, so a level object that is a line — which contains ∞ — is unrepresentable,
   while the library's `CliffordChain` admits lines. That is a difference in the predicate, not in
   presentation: the `BlindGenPos` triple of `layer13/BRIDGE_NOTES.md` (three centres on a circle
   through `M`, whose second intersections are distinct and collinear) satisfies the writer's
   hypotheses, and a blind finite-plane level-3 object would have to be a positive-radius circle
   through three distinct collinear points (impossible) or a line (excluded by the plane conjunct),
   so the writer's S4 statement is false as written at `n = 3`; the library's cutoff is unaffected
   and includes `n = 3`. This is a hand argument on exact coordinates — the triple's second points are
   `2+2i`, `(1−√3/2)+i(1+√3/2)` and `3+i√3`, distinct and collinear — not a Lean-checked negative
   statement. S5 is stated over the same encoding. Rows S2 and S3 add a
   quantifier difference: the writer asks for existence plus incidence of **every** certified point
   on one generalized circle, while the real payloads place the canonical `EptInf` only; the
   uniqueness step that would identify the two is false (§3.4). S1 is definitional *as well as*
   carrying a hypothesis-strength gap — the writer quantifies over `BlindGenPos`, the library over the
   strictly stronger `GenPosN` — so its two sides do **not** assert the same content, which is why it
   is excluded from the two definitional rows above and stays open. Because the real propositions are
   theorems, the blind statement implies each of them trivially — that direction is closed for all
   seven rows and carries no information. The informative direction, real theorem ⇒ writer's
   statement, is now **proved in Lean for S7 and S6**. `layer13/BridgeBlind.lean` (sha
   `f3819d69…`, 829 lines, compiles with exactly two `sorry`s, both at S1 and the general
   transport) supplies the predicate bridges — the circle (`mem_sphere_iff_onCircleM`), the
   transversal/second-point pair (`blindTransversal_iff`, `BlindSecond_eq`), general position
   (`genPosN_blindGenPos`), the generalized-circle transport (`isGCircleS_of_blindIsGCircle`,
   `chainS_of_blind`), and `BlindSix_eq` — and on them `N7_RB` (proved unconditionally: the writer's
   level-3 statement holds outright) and `N6_RB` (existence by an explicit per-level construction
   over the six `Counter6` centres, uniqueness by `chainS_six_unique`). Both depend only on
   **std**, with no `sorry` in their cone. **S1 stays open and is not a bridging problem**: `RealN1`
   supplies chains only for `GenPosN`, the writer quantifies over the strictly weaker `BlindGenPos`,
   and a concrete three-centre configuration separates the two (`layer13/BRIDGE_NOTES.md`); whether
   S1 holds at the weaker hypothesis is unsettled, and settling it needs a direct writer-side
   construction, not a rescoping of the statement: `layer13/BRIDGE_NOTES.md` §2 records that the
   blind statement appears to be true at the weaker hypothesis (the counterexample search above found
   none), so weakening it to `GenPosN` would replace a true statement by a weaker one. That
   construction is partly recorded: `layer13/BlindChain.lean` (1,296 lines, sha `6d5bfe5d…`) proves
   the writer's level-3 and level-4 objects for every `BlindGenPos` tuple, including the collinear and
   mixed-degenerate cases, proves level 5 under `GenPos5` or finite Miquel points, and reduces the
   all-`n` statement to one named lemma, `blindClifford_second` — the all-degenerate deletion — which
   is the file's single remaining `sorry`.
   A search for a counterexample to the blind statement found none
   (`layer13/s1_counterexample/SUMMARY.md`): all 3,732 and 25,820 `BlindGenPos` configurations on a
   small integer grid at `n = 4, 5`, 1,197 further random configurations checked at sixty digits, and
   a sample at `n = 6`, all admit the blind object — the collinear case is absorbed because a blind
   line carries `∞`. So S1 is expected to be true as the writer states it, but it is not proved, and
   this paper does not claim it.
   The general transport `blindOfChainS` also stays open on one branch: `IsGCircleS` admits the
   radius-zero circle (a finite singleton) where `BlindIsGCircle` requires `0 < r`. **OPEN**: S2/S3
   need a universal-incidence theorem, not uniqueness; S4/S5 need a corrected writer-side encoding of
   the finite plane (S4 is false as written, because the encoding forbids the line case that the
   library admits); S1 needs the statement decision above. The comparison file itself does run on a
   second machine: `BlindCompareFull.lean` (sha `32dfa1b2…`) is byte-identical to
   `john:~/lean/paperL_john/layer13_receipt.lean` and compiles there (rc 0, 5.4 s against jack's
   2.8 s); the blind writer was not re-run on john.

4. **The even-level Clifford point is not unique, and `UniqEven` is false.** `EptInf` is a canonical
   selection, not a theorem of uniqueness: for the centres `2t − 2it²` the level-6 objects `{4i}`
   and `{∞}` both satisfy `ChainS 6`, as checked in `check/not_UniqEven.lean` (**std** axioms). Only
   the `Counter6` instance has a uniqueness theorem (`chainS_six_unique`). Two consequences: the
   definite article of the former paper §2.5 wording (now replaced by “some level-(n−1) object”) cannot be
   justified in general, and any future statement
   identifying existential witnesses with `EptInf` needs extra hypotheses or a different selection
   predicate. Nothing here weakens the existence theorem.
5. **The two-machine receipt now holds for the statement layers.** The series' evidence standard is
   a second machine. On 2026-11-24/25 john audited the same file at the same pin
   (`Clifford/MorleyKernel.lean`, sha `dce7b011…`) with the same generator under a patched `REPOS`
   and `OUT`: **1,083 mutants over 324 declarations — 1,058 killed, 9 killed by heartbeat timeout,
   16 SURVIVED — and 343 contradiction probes (228 `ok`, 114 no-hypothesis, 1 probe-invalid, 0
   timeout), 0 CONTRADICTORY.** That reproduces jack exactly where reproduction is possible: the
   survivor set is the **same sixteen `(declaration, mutation)` pairs** on both machines, no
   survivor is machine-specific, and both report zero contradictions (§3.1). john also covers
   the six primed declarations jack's collector skips, killing all of their mutants. The v0.4 numbers
   quoted from `notes/math-papers.md` — 1,536 mutant rows over 520 declarations with 17 survivors,
   and 573 contradiction declarations — came from john's earlier wide run over a different tree and
   are **superseded** by this like-for-like rerun. What remains external: the round-26b timings (71 s on jack and 74 s on
   john for the promotion build, 67 s for the scratch receipt on john) and the build/gate/tamper receipts, quoted from the notes and not re-run
   here; and layers 6 and 9 were never run on john. Full comparison:
   `layer0/john_receipt_20261119/RECEIPT_VERDICT.md`.

6. **The "75 unbridged notions" is inventory arithmetic, not a semantic count.** Layer 9's 137 / 24 /
   113 comes from a heuristic `has-bridge` flag that points at internal lemmas as well as at
   Mathlib: its `has-bridge` list contains `GenPosN → hodd_inf_P0_eq`, `KP → A7_0_eq`,
   `IsGCircleS → IsGCircleS.infty_mem` and `ChainS → chainS_six_iff`, none of which identifies the
   notion with a Mathlib counterpart, while `GenTriple` stays among the 75 even though
   `genTriple_iff` (`Clifford/Bridge.lean:110`) already bridges it. The arithmetic 113 − 13 − 25 = 75
   is right; the reading "75 notions have no bridge to Mathlib" is not. The reason the sphere
   machinery is unlikely to bridge is real and separate: Mathlib has no generalized-circle or
   Möbius-sphere notion to target, so `IsGCircleS`, `ChainS`, `CliffordChainS` and `liftS` have
   nothing to be identified with. The 19 concrete bridge theorems and their 13 targets stand on their
   own. **OPEN**: a manual reconciliation of false positives and negatives.
7. **The 16 unattributed rows are now decisive.** Nine mutation rows and seven contradiction rows had
   carried `rc=137` (SIGKILL) or `rc=None` with an empty error string: the child was killed while the
   host sat at load ≈ 50. They were re-run on 2026-11-25, 19:32Z–19:42Z, under a lighter load and
   restricted to the 14 affected declarations (`lc_mod_requeue.py`, 46 jobs), and all sixteen
   resolved — the nine mutation rows as kills, the seven probe rows as `ok`. The battery file now
   contains **935 rows and no `error-unattributed` row**: 631 mutation rows (535 killed, 95 killed by
   heartbeat or wall-clock timeout, 1 survivor) and 294 probe rows (147 `ok`, 125 no-hypothesis,
   22 timeout). The only rows still without a verdict are those 22 probe timeouts, which are limits
   of the tactic budget, not load artifacts, and the one `probe-invalid` row of item 1.
8. **Eight unused hypotheses, removed in v1.2; one the ablation cannot see.** The layer-6 report
   (2026-11-19) named eight auxiliary lemmas carrying assumptions their proofs did not use:
   `cramer2_P0` and `cramer2_Qm` `(hm : 1 ≤ m)`; `child_levelPt_kernel_line` `(hd : ∀ j, d j ≠ 0)`;
   `p0_children_gcircleS_genPos` `_hP0`; `kpe_odd_succ_eq_mul_x` `(hj : j ≤ 2*k+4)`; `kpe5_hi`
   `(hj' : j ≤ 2*k+5)`; `kpe6_hi` `(hj' : j ≤ 2*k+6)`; and `parent_on_child_line` `(hQ0 : … ≠ 0)`.
   All eight are removed at the v1.2 pin, together with the two hypotheses of immediate callers that
   only forwarded them (`rowRel2_gen`'s `hm`; `child_levelPt_kernel_line_five`'s `hd`). Each removal was
   hand-checked before the build: dropping `hj'` reproduces the two `kpe` lemmas, and dropping the lower
   bound `(hj : k+3 ≤ j)` / `(k+4 ≤ j)` does not — `omega` then fails — so the report's "`hj`, `hj'`"
   wording is corrected here: only the upper bounds were unused, and they stay removed while the lower
   bounds stay. The late-block mutation run adds a different case, not an unused input:
   `child_line_of_parent_mid_zero` concludes `∃ p u, u ≠ 0 ∧ …` from `hv : V ≠ 0`, `hmid` and
   `P₀ ≠ 0`, and its proof is `absurd (parent_crossVec_zero_of_mid …) hv` — the branch is empty, so
   the four mutants of the conjunct `u ≠ 0` in its *conclusion* have no proof obligation to break and
   survive. The lemma is an empty-branch closer that mutation cannot test; that is a limit of the
   audit, not an unused hypothesis, and it is why `0 CONTRADICTORY` in layer 5 does not by itself
   exclude this source-visible vacuity. To the eight add `evenCornerQL_proof`'s `_hall` (paper §3.7),
   which layer 6 could not reach because `EvenCornerQL` is a `Prop` definition: it is not removable,
   because the geometric form uses it downstream through `evenCorner_of_QL`; it is recorded as a
   statement-level hypothesis the identity does not use. **RESOLVED for the eight** (v1.2; gate PASS 37
   std, tamper 8/8 at the new pin).
9. **Carver's classification is cited, not formalised.** paper §1.2 says this; it belongs in the limits
   list too. The development proves the chain exists on the sphere, including the line and ∞ cases
   as they arise; it does not state or prove the key-matrix criterion that predicts *when* they
   arise, and its carrier is not Carver's (which admits a point-circle at infinity that
   `IsGCircleS` excludes). **OPEN**.
10. **The prior-art search has recorded gaps**, and a novelty claim is only as strong as its weakest
    search: MathSciNet and zbMATH were not searched (no subscription or API key available); Morley
    1900, F. Morley 1929, Wagner 1929 and Kobayashi 1958 were seen only as metadata behind the JSTOR
    paywall (Carver 1920 is the only one of them read in full, from the archive.org OCR); HAL timed
    out twice; Google Scholar is not reachable from this runtime; the non-English web query returned
    nothing; the Mizar MML body was not full-text searched; and LeanGeo, LeanPool, Principia, TLMC,
    ACL2, PVS, Nuprl and Naproche were not searched individually. `SCOUT.md` §2 records these as
    *not searched*, not as *empty*. The novelty claim in §1 is therefore: no formal statement of the
    chain for arbitrary n was found in any of the sources logged in `SCOUT.md` §0 (26 search rows), not: none exists.
11. **What has and has not run, per input version, and on how many machines.** Layers 1–10 ran
    against the code (the battery at `dce7b011…`, before the bridge file; layer 10 after it). Layer 11
    ran on v0.1 and was **re-run** on every draft from v0.2 through v0.11; each re-run is a corrected
    re-run on a new input, not a reproduction, and v0.5–v0.11 changed only evidence and provenance, so the
    citation set it certifies is the one introduced between v0.2 and v0.4. Layer 12 **reviewed v0.1**;
    the three-model round reviewed v0.2; an independent review of v0.3 is applied in v0.4; an
    independent referee pass on v0.7 produced the corrections of v0.8, a referee pass on v0.9 those
    of v0.10, and an Opus 5.5 pass on v0.10 those of v0.11 (Appendix C). Layer 13's blind
    writer was **re-run** after the parity repair of the blind text, three rows were compared on v0.2,
    and all seven rows were compared against the writer's real types on v0.3, with the bridge layer
    closing S6 and S7 in both directions (§3.3). Layer 14 was cut from v0.2 and **re-cut and re-run on
    v0.7**; layer 15 was built on v0.2 and **re-built on v0.7** (`L14_RESTATEMENTS_v07.md`,
    `L15_PRIOR_ART_v07.md`).
    On machine count: layers 4 and 5 were reproduced on **both** machines for `MorleyKernel.lean` (the
    like-for-like receipt, §3.5); layer 8 ran on **both** over their full inventories (§3.2); and the
    layer-13 comparison file `BlindCompareFull.lean` compiles on both, while the later bridge file
    `BridgeBlind.lean` was checked on jack only. Layers 1, 2 and 7 also have a john run in his 19 November battery at the
    same pin (wider file set: gate PASS 37, tamper 8/8, linter 0; published in
    `layer0/john_receipt_20261119/BATTERY.md`); layers 6, 9, 10, 11, 12, 14 and 15 are jack-only. The upload is no
    longer open: the pin is commit `3df056f`, the repository is public at that commit and the
    supporting material is published (§1); the Zenodo deposit is the authors' remaining step and is
    not described here as done.

---

## Appendix A — provenance

All paths in this appendix are relative to the paper's artifact directory `AFM/PaperL/` unless
prefixed `jack:` or `john:` (host paths). A flat review packet that copies these files to one
directory must be read through this mapping; the files themselves are the ones named here.

* Claim set, route and statement form: `AFM/PaperL/PLAN.md` §Claim set, §Route.
* Novelty verdicts quoted in §1 and §3.10: `AFM/PaperL/SCOUT.md` §0 (search log, 26 rows), §1
  (verdict table, L1–L9), §2 (gaps), §3 (what may and may not be claimed).
* Rounds 19–26b (odd side, even side, the corner, `EvenCornerQL`, promotion, gate 32 → 36):
  `notes/math-papers.md`, sections "Paper L — round 19" through "Paper L — round 26b". Bundled
  excerpt: `evidence/math-papers-PaperL-excerpt.md` (also at `jack:~/paperL_jack/layer0/`); it is the
  source of the john timings quoted in §2 and §3.5, which remain *recorded, not verified*. Its john
  battery snapshot is superseded by the like-for-like rerun of 2026-11-25 (§3.5).
* Layer 10 content and the 19 bridges: `jack:~/paperL_jack/layer10/REPORT_L10.md`.
* Layer 11 anchor table (37 declarations, 19 bridges, axioms): `jack:~/paperL_jack/layer11/ANCHORS.md`;
  the citation gate: `namegate.py` and `L11_NAMEGATE.md` (regenerated for every draft from v0.4
  through v0.11; the current report is v0.11).
* Layers 1–9 numbers, harness defects, the 16 unattributed rows, the layer-6 unused list, john's
  snapshot: `jack:~/leancheck/reports/paperL_jack_20261119_020713.md` and
  `notes/math-papers.md` "Paper L — round 26b leancheck battery".
* Corner witness (numerical, not a certificate) and its margins:
  `layer0/r25_jack/RANK_ROUTE_COUNTEREXAMPLE.json`, bundled with the paper.
* The two check files added for this record: `check/allN.lean` (the all-n composition, rc 0, **std**)
  and `check/not_UniqEven.lean` (the counterexample to uniqueness, rc 0, **std**); copies at
  `jack:~/paperL_jack/scratch/`.
* Paper D (base cases `n ≤ 5` and the six-centre failure): Zenodo record 23653309.
* John's 19 November battery report is published in `layer0/john_receipt_20261119/` (`BATTERY.md`,
  `.log`, `RESULTS_20261119.jsonl`); it was hosted only at
  `john:~/leancheck/reports/lean/paperL_john_20261119_143939.md` before this release. Still host-only:
  jack's `leancheck` battery report and `.log`, the layer-6/7/9 raw outputs behind 501/8 and
  137/24/113 (`~/leancheck/reports/paperL_jack_20261119_020713.md`, `~/lc_gap_paperL_jack/`), and the
  round-26/26b timings for john. Those figures are quoted from the notes excerpt.

### Where each cited artifact is published

| cited here | published in `LEAN-verification/PaperL` |
|---|---|
| `AFM/PaperL/DRAFT.md`, `COMPANION.md` | `preprint/DRAFT_v10.md`, `preprint/COMPANION.md` and the PDF of the paper beside them |
| `AFM/PaperL/PLAN.md`, `SCOUT.md`, `namegate.py`, `L11_NAMEGATE.md`, `L12_REVIEW.md`, `L13_REPORT.md`, `L14_*`, `L15_*`, `JOHN_LEG.md` | `reports/` |
| `AFM/PaperL/REVIEW_*`, `REVIEW_TRIAGE_*` | `reviews/` |
| `AFM/PaperL/layer13/*` | `layer13/` (the same files, minus `run4/`–`run6/`) |
| `AFM/PaperL/layer0/*` (the eight run directories cited) | `layer0/` |
| `AFM/PaperL/check/*`, `evidence/*` | `check/`, `evidence/` |
| `layer13/BlindCompareFull.lean`, `layer13/BridgeBlind.lean` | `layer13/` in this folder; in the code repository they are `scratch/…` |

## Appendix B — which layers ran, and where their output lives

| layer | input | what it establishes | artifact |
|---|---|---|---|
| 1 | code `dce7b011…` | gate: 37 REQUIRED declarations present, axioms ⊆ std | `gate.sh`, §2 |
| 2 | code `dce7b011…` | tampering: 8 cheat attempts rejected | `tests/tamper.sh` |
| baseline | code `dce7b011…` | the 8 audited source files compile | battery report |
| 4 | code `dce7b011…` | mutation: 535 decisive kills, 1 survivor, 0 unattributed over 259 declarations — plus a late block of 891 rows (872 kills, 3 timeout, 16 survivors) over 257 further `MorleyKernel` declarations; 318/343 of that file in total (§3.1) | battery report; `layer0/lateblock_jack/` |
| 5 | code `dce7b011…` | contradiction probes: 0 CONTRADICTORY over 551 declarations — 294 from the battery and 257 from the late block at lines 816–5592 (failed proof search, §3.2) | battery report; `layer0/contra_late_jack/` |
| 6 | code `dce7b011…` | ablation: 501 needed / 8 unused over 262 declarations | battery report, §3.8 |
| 7 | code `dce7b011…` | linter: 0 warnings in 8 library files; scratch leg from layer 10: 0 in 37 files, 31 compiling | battery report; `layer10/REPORT_L10.md` |
| 8 | code `dce7b011…` | satisfiability certification: **run on jack and john**, 400/596 and 394/584 certified; 397 of 577 shared declarations certified by at least one machine, 180 by neither | `layer0/sat_jack/`, `layer0/sat_john/`, §3.2 |
| 8b | code `dce7b011…` | witness linkage: **0 links** (no `*_sat` witnesses in either tree) | §3.2 |
| 9 | code `dce7b011…` | notion inventory: 137 / 24 flagged / 113, heuristic | `~/lc_gap_paperL_jack/inventory.md` |
| 10 | code + `BridgeL10.lean` | definition bridges: 19 theorems, 13 notions bridged, 25 INTERNAL, 75 left | `layer10/REPORT_L10.md` |
| 11 | v0.1, re-run on every draft from v0.2 through v1.0 | citation gate on the paper: 68 occurrences / 64 distinct, all resolving, 33 attribution checks; the tables of §1.1–1.3 of this record are the same citations at file:line | `L11_NAMEGATE.md` |
| 12 | v0.1, v0.2 (three models), v0.3, v0.7, v0.9, v0.10 | prose versus code (independent reviewers): v0.1 review 5 MAJOR / 6 MINOR → v0.2; three-model round on v0.2 → 19 rows → v0.3; v0.3 review 0 MAJOR / 6 MINOR / 3 NOTE → v0.4; v0.7 referee 7 MAJOR / 3 MINOR → v0.8; v0.9 referee 2 MAJOR / 8 MINOR → v0.10; v0.10 Opus 5.5 pass → v0.11 | `L12_REVIEW.md`, `REVIEW_*_v02.md`, `REVIEW_TRIAGE_v02.md`, `REVIEW_gpt-6-astra_v03.md`, `REVIEW_TRIAGE_v03b.md` |
| 13 | v0.3 prose, blind writer re-run after the parity repair | blind re-formalisation: seven rows compared against the writer's real types; the bridge layer now proves the real ⇒ writer direction for S6 and S7 (§3.3); S4/S5 are stated over the writer's finite-plane encoding, which excludes lines, and S4 is false as written there | `layer13/L13_REPORT.md` and `layer13/L13_FULL_COMPARE.md`, with `jack:~/paperL_jack/scratch/` for the comparison sources and `jack:~/reformal/` for the blind files |
| 14 | v0.2, re-cut and re-run on v0.7 | independent restatement of the seven signatures: 7 of 7 faithful; two wording notes | `L14_RESTATEMENTS_v07.md` (v0.2 pass: `layer13/L14_RESTATEMENTS.md`) |
| 15 | v0.2 + `SCOUT.md`, rebuilt on v0.7 | prior-art verdict table: PASS with recorded search limits | `L15_PRIOR_ART_v07.md` (v0.2 table: `L15_PRIOR_ART.md`) |

Second-machine reproduction: layers 4 and 5 are reproduced on john at the same pin for
`MorleyKernel.lean` — 1,083 mutants over 324 declarations, the identical sixteen survivors, zero
contradictions (`layer0/john_receipt_20261119/RECEIPT_VERDICT.md`) — and the layer-13 comparison file
`BlindCompareFull.lean` also compiles there byte-identically; the later bridge file was compiled on
jack only. Layers 1, 2 and 7 also ran on john in his 19 November battery, on a wider file set; layers 6 and 9 were not run on john; the round-26b build/gate/tamper timings
are still quoted from the notes; and the re-runs of layers 11 and 13 are re-runs on new inputs, not
reproductions.

## Appendix C — changes in v0.3 through v0.12

### v0.3 — all nineteen rows of `REVIEW_TRIAGE_v02.md`

All nineteen rows are applied; none required a change to the Lean.

1. paper §2.5(b): `UniqEven` is **false**, with the checked counterexample; the named-point form is a
   selection, not a uniqueness theorem.
2. §3.3: the layer-13 comparison is described as it was — writer's universal reading, re-typed
   existential restatement, three rows, one direction; "structure untouched" and "strictly stronger"
   withdrawn. `L13_REPORT.md` corrected to match. (v0.3→v0.4: rewritten again for the seven-row
   comparison of §3.3 below.)
3. §2/§3.2: layer 8 is disabled by `--fast`; layer 8b has no recorded result; layer 5's `ok` is
   failed proof search.
4. §2/§3.1: mutation/contradiction coverage disclosed — 61/60 of 343, all before line 807, no headline
   theorem — and separated from the 16 inconclusive rows.
5. §2/§3.5/App. A: john's receipts and timings labelled recorded-not-verified; the corner witness
   bundled and labelled numerical; grandchildren **coincide** in the exact corner.
6. §1.3: signature anchors added for the statement declarations; the gate claim now matches what the
   script checks (occurrence count, comment and comma forms, no bare "line N").
7. paper §2.1: `second`, `Transversal`, `GenTriple` (both conjuncts), `crossVec`, `KP`, `levelPointN` and
   `EptInf` (with its zero-vector totalization) defined; paper §2.3 adds the role of `h4_pt_inf` and
   `cliffordChainS_all_of`.
8. paper §1.2: Paper D's C₆ qualified; base cases limited to `n ≤ 5`; `not_cliffordChain_of_six_le` named
   for the `n ≥ 6` failure.
9. paper §2.3 and §2.5(a): `cliffordChainS_of_le_five` cited for the base cases; the aggregate all-n statement is
   the composition in `check/allN.lean`, since no single declaration states it.
10. paper §1, §2.1 and §2.5(d): Carver cited as §3 pp. 160–161 (Theorem 13) and §6 pp. 161–164 (limiting
    figures); the point-circle-at-infinity difference from `IsGCircleS` stated.
11. §2/§3.6: layer 9's 24/113/75 relabelled as inventory flags, with the false positive and false
    negative named.
12. §2: the survivor is the alternative-level mutant `CliffordChain 1 → 2`, caught downstream by a
    type mismatch; "weaker"/"not counted" removed.
13. §2: 13 macro use sites (15 identifier occurrences), three reworded module comments.
14. §3.11/App. B: per-layer input versions; the blanket "nothing was run twice" removed.
15. paper §2.5: indefinite article throughout, with the reason.
16. App. A/App. B: artifact paths corrected — paper-relative paths under the `AFM/PaperL/` tree,
    host paths for `jack:~/paperL_jack/scratch/` and `jack:~/reformal/`; a flat review packet is
    read through the mapping stated at the head of Appendix A.
17. paper §2.4/§3.8: `EvenCornerQL` does not use `hall`; why layer 6 could not see it.
18. §1: toolchain `leanprover/lean4:v4.33.1` and the Mathlib pin recorded.
19. §2/§3/App. B: receipt and wording corrections — the batch log's mutation/contradiction
    section cut off at its traceback (the log itself continues to `LEANCHECK DONE`), linter
    cited to `REPORT_L10.md` with the 3+3 failure split, 525 decisive kills reported
    separately from 95 timeouts, the bridge file's post-battery date, the scratch-only byte identity,
    `SCOUT.md` §0 row 18, Clifford's dates aligned to 1870–71/1882, "forced to be lines" marked as
    explanation, and the corner's `V = 0` derivation cited to `parent_crossVec_zero_of_mid`.

### v0.4 — independent review of v0.3 (`REVIEW_gpt-6-astra_v03.md`; dispositions in `REVIEW_TRIAGE_v03b.md`)

1. paper §2.1: the `Counter6` "zero parent cross vector" example was **false** and is replaced by the
   paper §2.4 parabola tuple, with the exact checks named; the `Counter6` last coordinate is recorded as
   `−238878720000`.
2. paper §2.1: the piecewise entry formula of `KP` is displayed; `Kf`, `aOf`, `tOf` are given with lines;
   the kernel equivalence is qualified by nonzero centres, with the `n = 1` counterexample noted.
3. paper §2.3: the `P_{k+2} = 0` branch now says the **finite** child points coincide, that zero middle
   coordinates are `∞`, and that `heven_of_common` supplies the line; no non-uniqueness inference.
4. §3.2/§3.4: the two stale references (the "0/0 row", the "definite article in paper §2.5") now point at
   the former wording and the battery report's row.
5. §3.5: five recorded ssh attempts, not six.
6. paper §1.1: corner-witness margins reported per solver run; the JSON's location in the artifact tree
   stated (the flat referee packet did not carry `layer0/`).
7. §3.3 rewritten for the seven-row layer-13 comparison; §3.11's per-layer provenance updated.
8. App. A/B path claims: paper-relative paths and the flat-packet mapping stated.
9. §1/App. B: gate count refreshed to 143 occurrences / 98 distinct (three new anchors this round);
   `L11_NAMEGATE.md` regenerated.

### v0.5 — the late-block mutation run (2026-11-25)

No statement, proof or definition changed in this version; the evidence did.

1. §2/§3.1/App. B: mutation coverage of `Clifford/MorleyKernel.lean` rises from **61 of 343**
   declarations (all in lines 33–806) to **318 of 343** (93%). A late block, run on jack
   2026-11-24 21:28Z → 2026-11-25 03:41Z, adds 891 mutant rows over the 257 declarations at lines
   816–5586: 872 killed, 3 killed by heartbeat timeout, 16 survivors, 0 unattributed. The round 19–26
   material — `heven_kernel`, `heven_line_of_P0`, `evenCorner_of_QL`, `heven_inf_all` — now carries
   mutation rows, so the earlier sentence that no round 19–26 declaration had been mutated is
   withdrawn. Contradiction probes were **not** extended (layer 5 was skipped), and that stays OPEN
   in v0.5 (closed in v0.6).
2. §3.1: the 16 late-block survivors are itemised: nine caught downstream, three vacuous
   (`2*0+5 → 3*0+5` at `k = 0`), and four mutations of `child_line_of_parent_mid_zero`'s `u ≠ 0`.
   None is a hole.
3. §3.8: `child_line_of_parent_mid_zero`'s `u ≠ 0` added to the unused-hypothesis list.
4. §3.5/§2/App. B: john came back online on 2026-11-25 and his like-for-like rerun finished the same
   day — 1,083 mutants over 324 declarations of `MorleyKernel.lean`, 1,058 killed, 9 timeout,
   **16 survivors**, 343 contradiction probes with 0 CONTRADICTORY. The survivor set is the **same
   sixteen pairs** as jack's, so the two-machine receipt is now claimed for layers 4–5 and §3.5
   rewritten accordingly (`layer0/john_receipt_20261119/RECEIPT_VERDICT.md`); the v0.4 snapshot
   figures are marked superseded. The earlier "unreachable since 2026-11-19" wording is corrected.

### v0.6 — the late-block contradiction probes and the unattributed rows (2026-11-25)

No statement, proof or definition changed in this version either; the evidence did.

1. §2/§3.1/App. B: contradiction probes rise from **294** declarations to **551 of the 577**
   (95.4%). A late block, run on jack 2026-11-25 17:31Z → 19:09Z over the 257 `MorleyKernel.lean`
   declarations at lines 816–5592, returns 163 `ok`, 93 with no hypothesis to probe, 1
   `probe-invalid` and **0 CONTRADICTORY**. Layer 5 now covers both blocks of the file that layer 4
   covers, and §3.1 lists the 26 declarations that carry no probe row.
2. §3.1: the `probe-invalid` row is identified — `subfamily_P0_zero_gen`, where the `True` control
   itself fails to compile because `conj` is bound as an implicit variable under `autoImplicit` — and
   is excluded from the `ok` count rather than reported as a pass.
3. §3.1 item 7: the 16 `error-unattributed` rows were re-run under a lighter load and are all
   decisive, so the battery file has **935 rows and zero unattributed rows**; §2's layer-4 and
   layer-5 rows and App. B quote the re-run tallies (535 kills, 147 `ok`) instead of the published
   plus unattributed sums.

### v0.7 — the two-machine satisfiability passes (2026-11-26)

No statement, proof or definition changed in this version; the evidence did.

1. §2/§3.2/App. B: layer 8's "not performed" row is replaced by the real record. jack certified 400 of
   596 declarations (67.1%, 13 h 04 min) and john 394 of 584 (67.5%, 10 h 17 min) with the same
   instrument at the same pin; `stmt-invalid` is 0 on both. Across the 577 declarations both machines
   ran, 560 agree, 17 differ only in which machine found a witness, and 397 (68.8%) are certified by
   at least one machine; 180 are unresolved on both. The section now states precisely what a
   certificate means (an accepted proof that the hypotheses are simultaneously satisfiable), that
   `unresolved` is a failed search and not a refutation, and that layer 5's `ok` is neither.
2. §3.2: the curated witness table (107 names, jack, 2026-11-26) is reported as having closed none,
   with the reason — the instrument cannot discharge the propositional side conditions of the
   hypotheses (complex arithmetic; `decide` cannot close equalities over `ℂ`) — and what it would
   need (a per-family proof library for `Transversal`, `GenTriple`, `GenPos4/5`, `Chain 4 ![…]`,
   `mD ≠ 0`).
3. §2/App. B: layer 8b is recorded as **0 links** rather than "no recorded result": neither tree
   contains a hand-written `*_sat` witness.

### v0.8 — corrections from the referee pass on v0.7 (2026-11-26)

No statement, proof, definition or number changed in this version; nine sentences were corrected
because they said something the record does not support, and three stale provenance statements were
brought up to date. Source: `REVIEW_v07_referee_bigpickle.md` (one independent instrument, draft-only
input; two further instruments returned no report and are recorded as failed runs) and the
dispositions in `REVIEW_TRIAGE_v07.md`.

1. §1: the novelty sentence now carries its scope in the same breath — the 26 search rows of
   `SCOUT.md` §0 and the sources §3.10 records as not searched — instead of leaving the qualification
   three sections away.
2. paper §1.1: "The corner is not empty" became "not vacuous in practice", with the numerical search
   downgraded to approximate and exact membership explicitly not claimed from it (the theorem does not
   need it).
3. §3.2: the certificate is described correctly — the hypothesis is a `Prop`-valued *binder* the
   certificate must inhabit, not an assumption — and vacuity is no longer inferred from
   `stmt-invalid = 0`; 397 witnesses are claimed, 180 declarations are left open.
4. §3.3: S1 is removed from the four "definitional" rows and named as definitional **plus** a
   hypothesis-strength gap, which is why it stays open; S4/S5/S6/S7 remain definitional.
5. §3.11: "Nothing in this appendix was run twice on two machines" was false and is replaced by a
   per-layer statement of which layers ran on both machines; the layer-11 sentence no longer describes
   v0.3 as the current text; the OPEN list no longer names the bridge layer or the pin (both done) and
   names the upload only.
6. §1: the tree is no longer described as "a plain directory, not a repository" — it is a git
   repository at `d15464f` with no remote, and the per-file sha256 table is stated as the identity of
   the audited tree until it is pushed.
7. App. A: the `L11_NAMEGATE.md` label no longer says v0.3; App. B row 11 records re-runs through
   v0.7; App. C's heading covers v0.3–v0.9; paper §1.2 separates the polytope citation (Longuet-Higgins
   1972) from the cross-ratio route (Bobenko–Schief, arXiv:1509.04109, 2016).

### v0.9 — publication of the code repository (2026-11-26)

No mathematical statement, proof, definition or citation changed; this version records the publication
of the artifacts the earlier versions pinned, and corrects the inventory count.

1. §1: the repository is named with its URL and the pin, and the file count is corrected from 153 to
   156 — commit `d15464f` also carries `.gitignore` and the two `.bak-r26` files, added after the
   earlier count was taken.
2. §1: a new **Availability** paragraph names the repository, the pin, the two check files, the three
   commands that reproduce the gate and the tamper suite, and the `PaperL` folder of
   `LEAN-verification`, whose layout is mapped from the artifact-relative paths of Appendix A.
3. §3.11: the upload leaves the OPEN list — the repository is public at the pinned commit and the
   supporting material is published; the Zenodo deposit is recorded there as the authors' remaining
   step, not as done.
4. App. B: rows 14 and 15 now record the v0.7 re-cuts (`L14_RESTATEMENTS_v07.md`,
   `L15_PRIOR_ART_v07.md`) that §3.11 and §3 already described, and row 11's re-run list is brought
   up to v0.9 with a typo fixed.

### v0.10 — corrections from the referee pass on v0.9 (2026-11-26)

Source: `REVIEW_v09_astra.md` (one independent instrument; input: this record, the pinned tree and the
published reports), dispositions in `REVIEW_TRIAGE_v09.md`. Two findings were MAJOR and eight MINOR;
all ten were accepted after each was checked against the source or the record. No Lean proof,
statement or definition changed.

1. §3.3: the layer-13 classification of S4/S5 is corrected. They are not definitional variants: the
   writer's finite-plane encoding forbids ∞ at every level, so a level object that is a line is
   unrepresentable. The recorded `BlindGenPos` triple with collinear second points satisfies the
   writer's hypotheses and admits no blind finite-plane level-3 object, so the writer's S4 statement
   is false as written at `n = 3`; the library's cutoff includes `n = 3` and is unaffected. S6/S7
   remain definitional, and both directions are bridged.
2. §3.1/§3.8/App. C: the four surviving mutants of `child_line_of_parent_mid_zero` are re-described —
   they alter the **conclusion** of a lemma whose hypotheses are inconsistent on purpose, so the
   branch is empty and no proof obligation reaches them. (v0.11 refines this further: only two of the
   four touch the `u ≠ 0` conjunct; one flips the finiteness antecedent and one the incidence
   equation.) The lemma leaves the unused-input account; the layer-6 501/8 tally is unchanged.
3. §1: the tamper suite is **eight** tests, not nine, and the reproducer is `bash tests/tamper.sh`
   (the file is mode 100644 at the pin); the citation gate makes **25** name-attribution checks, not
   22.
4. §1/App. A: the supporting folder is described by its layout instead of as a mirror, the
   artifact-relative path convention is stated once, and john's original battery report is removed
   from the externally-hosted class — it is published in `layer0/john_receipt_20261119/`.
5. paper §1.1: the rank-route sentence now says numerical evidence, not refutation, and ties the `1e-9`
   residual and the `1e-8` collinearity figure to the earlier, looser run (`3.9e-5` collinearity for
   the stored tuple).
6. §3.1/§3.5/App. C: the stale satisfiability OPEN item is removed (only the expected-job manifest
   remains), the round-26b timings are labelled by machine and operation, and the v0.9 entry no longer
   says that no number changed.
7. §2: layer 5's warning now says that a failed search does not certify **satisfiability**.
8. §3.1/§3.11/App. B: "checks alone" and the machine-count summaries are scoped — layers 4/5 on john
   cover `MorleyKernel.lean`, layer 13 on john covers `BlindCompareFull.lean`, and the bridge file is
   jack-only.
9. Supporting reports: `L13_BRIDGE_STATUS.md`'s stale `sorryAx` line and `L13_FULL_COMPARE.md`'s
   "only definitional row" sentence are corrected with a dated note, and `L13_REPORT.md` carries a
   supersession header. The audited pin and the raw logs are untouched.

### v0.11 — corrections from the Opus 5.5 pass on v0.10 (2026-11-26)

Source: `REVIEW_v10_opus.md` (one independent instrument; inputs: this record, the pinned tree, the
published repositories; no compilation), dispositions in `REVIEW_TRIAGE_v10.md`. One finding was
MAJOR, ten MINOR and two NOTE; all thirteen were accepted after each was checked against the data or
the source. No Lean proof, statement or definition changed.

1. §3.2: layer 8's 397 certificates are now split by statement class — 210 hypothesis-free, 119
   closed, 68 inhabiting a hypothesis — so the paper no longer says that 397 "carry a witness of
   their hypotheses". It also records that a hypothesis packed inside a `Prop` definition is
   invisible to layer 8 as it is to layer 6, and that `parent_crossVec_zero_of_mid` is unresolved on
   both machines, so whether the corner is inhabited rests on paper §1.1's numerical witness.
2. §3.1/§3.8: only two of the four `child_line_of_parent_mid_zero` survivors touch the `u ≠ 0`
   conjunct; one flips the grandchild-finiteness antecedent and one the incidence equation.
3. §3.3: S6 alone is definitional; S7 is definitional **plus** a hypothesis-strength gap, closed
   because the writer's statement is proved outright. S4's falsity is labelled a hand argument on
   exact coordinates, not a machine-checked statement. The S1 paragraph records the direct route in
   `layer13/BlindChain.lean` (levels 3–4 for every `BlindGenPos` tuple, level 5 conditional, all-`n`
   reduced to `blindClifford_second`) and no longer offers rescoping, which the recorded note rules
   out.
4. §3.1: the 19 un-mutated declarations are ones on which no mutant was generated, not ones the
   generator "cannot" alter; the headline is no longer called a corollary; and john's receipt is
   recorded as probing all 343 `MorleyKernel` declarations, the 26 jack left unprobed included.
5. §2/§3.1/App. B/App. C: the late-block probe range is 816–5586 — `heven_inf_all` is the last probed
   declaration — not 5592.
6. §1: the citation gate leaves eight "lines A–B" range tokens (four distinct spans), and the
   reproduction steps add `lake exe cache get` and say the manifest, not the lakefile tag, fixes
   Mathlib.
7. App. A/§3.11/App. B: john's battery report is published and layers 1, 2 and 7 are not jack-only;
   the three layer-11 provenance statements now agree (through v0.11); the v0.9→v0.10 and
   v0.10→v0.11 review rounds are recorded; and App. A gains a table mapping every artifact path to
   its published location.
8. paper §1.1: the numerical-witness caveat is stated once and the duplicated sentence is merged.
9. Supporting reports: the three reports that still described `u ≠ 0` as an unused hypothesis carry a
   dated correction notice.

### v0.12 — typeset in the style of Papers I and K (2026-11-26)

No statement, proof, number or citation changed. The paper is now built as LaTeX with the preamble
used by the other papers in this series (11 pt article, 1 in margins, Latin Modern, booktabs
tables, numbered sections, title/author block with the licence footnote), instead of the markdown
pandoc build. The abstract, previously only in the deposit record, is now part of the paper. The
version changelog (this appendix) stays in the markdown source and is not typeset into the PDF;
`paperl.tex` is generated from `DRAFT.md` by `build_paperl.py`, and both are published beside the
PDF.


### v1.0 — restructured as a paper, and the all-`n` theorem enters the library (2026-11-26)

Two changes, one substantive and one presentational.

*The library.* `Clifford/MorleyKernel.lean` gains

```lean
theorem cliffordChainS_all (n : ℕ) : CliffordChainS n
```

which joins the transported levels $n \le 5$ with the Morley induction for $n \ge 3$, with no
hypothesis on $n$, and it is added to the gate's REQUIRED list: **37 declarations**, standard axioms.
Previously the all-$n$ statement existed only as the composition checked in `check/allN.lean`, which is
the one structural thing this version changes in the formal content. The build, the gate, the tamper
suite (8/8) and the axiom report were re-run at the new pin `1001939`; at that pin
`Clifford/MorleyKernel.lean` was 5,610 lines, sha `4beb169a…`, and `gate.sh` sha `445a7093…` (the file
lost three lines in v1.2, below). Nothing else in the library moved:
`Clifford/Mobius.lean` and the other eight files are byte-identical to the previous pin.

*The paper.* Restructured so that it reads as a mathematics paper rather than a test report. The
mathematics — the statements, the inversion, Morley's matrix and its readouts, the two-step induction,
the bordering step, the degenerate branches and the corner — is now §1–§3 of the paper, and the
verification record, the declaration tables, the layer table and the changelog are here. New in the
paper: the worked cases $n = 2, 3, 4$ that show how the matrix produces the level objects; the full
proof of the corner in three steps; and §2.5, which takes up the four places where the formal statement
makes a choice the classical prose leaves open (the existential recursion, the non-unique even-level
point, the totalisation of the vanishing vector to ∞, and `GenPosN` against classical general
position). A disclosure of the use of automated tools (paper §4.4) is now in the paper, and the
referee-style reading passes are described there as what they are rather than named by file.

*§4.4, first form.* v1.0's §4.4 opened with the author's statement that he wrote the paper as he directed
it and had hand-checked it. That wording was replaced in v1.1 (below), which states the same
responsibility and adds the plain attribution of the corner argument.

### v1.1 — the pre-submission referee pass (2026-11-26)

A referee read v1.0 and returned a list of corrections before submission. All of them were applied; no
statement, proof or number of the mathematics changed.

- **References.** The paper cited Clifford, Morley, Carver, Longuet-Higgins, Bobenko–Schief, Lean,
  Mathlib and the existing Miquel formalisations inline and had no list. A reference list now closes the
  paper, alphabetical and author–year, with DOIs or stable URLs for the classical sources, the two
  software entries, the Miquel formalisations, and this work's own earlier paper and code.
- **§4.4 rewritten.** The referee asked for the AI disclosure to be plain. The section now states the
  author's responsibility, and then says without hedging that the corner argument of §3.7 was produced
  by the coding agents in the course of the formalisation and is not the author's own discovery. The
  earlier claim that it was his has been removed from the paper. The prose paragraph (language-model
  drafting and reading passes, every correction checked against the development) is unchanged in
  substance.
- **Internal leftovers removed.** The round numbers and line counts of the proof rounds, the `hV`-only
  remark, the tamper suite's internal variant names, and the unexplained `BlindGenPos` / "blind
  restatement" sentence are gone; the tamper variants are described in words, and "the companion" is
  named and linked at its first mention (*Verification record for Paper L*, COMPANION.md, with the
  supporting material on GitHub).
- **§3.7 Step 3.** The prose said the $X^{2m+1}$ coefficient is the leading coefficient times the
  *constant* term; a coefficient of the top power of a binary form of degree $2m+1$ is leading times
  leading, and the displayed formula was already the leading-coefficient one. Corrected, and the
  conjugate is now stated explicitly to sit on $w_0$ — which is what `polyF_coeff_top` proves
  (`-(W (2k+5) * conj (W 0))` at the pin). The two places that mention the coefficient now agree.
- **Reconciled.** §1 said the corner argument had no counterpart in the literature while §3 opened with
  "Nothing here is new mathematics". Both now say the same thing: the statement is classical, the corner
  is a proof device not found in the sources, and it is not a new theorem.
- **Cross-references and layout.** §3.4's stale pointer to §2.3 is now to what §2.3 records; the §4.1
  table, which overflowed its columns, is a list; the stretched line around "The main result" in §2.3 is
  fixed, as are the theorem heads of §3.7 (their machine citations moved into the statements). 18 pages,
  0 overfull boxes, 0 undefined references.
- **New sections.** §1.1 Related work (classical sources; the four Miquel formalisations and what they
  prove; Mathlib's target list; the author's earlier plane formalisation) and §4.5 Lessons for
  formalisers (canonical payloads instead of uniqueness; coordinates before predicates; ∞ in the
  carrier; induct at the parity of the level).

*Done since.* The referee's strengthening list asked for two code changes. The eight unused hypotheses
were removed in v1.2 (pin `3df056f`; §3 item 8 above, paper §4.3). Splitting `MorleyKernel.lean`
(5,607 lines) is still queued: it moves declarations across files, so every `File:line` anchor in the
paper and this record has to be regenerated at the new pin, and it is best done with the next content
change rather than alone.

### v1.2 — the referee's last pass: cross-references, citations by hand, unused hypotheses removed (2026-11-26)

- **Two stale cross-references and one missing parenthesis.** §3.4 ended "the claim §2.3 records", but
  §2.3 states the theorem, not the odd side's hypothesis-freeness; the clause is gone. §3.7 said the
  corner statement was "obtained from a scalar identity (§2.5(c))", but §2.5(c) is the totalisation at ∞;
  it now names the corner identity proved in §3.7 and `evenCorner_of_QL`, and cites §2.5(c) only for the
  parent's ∞. §2.1's bare `Clifford/Basic.lean:394` gained its parentheses.
- **Every reference checked by hand against the source.** Clifford 1871: *Messenger of Math.* 5,
  124–141, reprint *Mathematical Papers* 38–54 — confirmed against the 1882 Tucker scan (article VIII
  opens p. 38, article IX opens p. 55). Bobenko–Schief 2016: title "Circle complexes and the discrete
  CKP equation", IMRN article **rnw021** — confirmed at Crossref/OpenAlex and the arXiv preprint
  1509.04109, which does use cross-ratio identities for Miquel and Clifford. Carver 1920: 42(3),
  137–167 with errata *ibid.* 42: 286 (doi 10.2307/2370470) — confirmed via Crossref and the JSTOR scan,
  which also confirms §5 pp. 160–161 (Theorem 13) and §6 pp. 161–164 (limiting figures). **Coxeter was
  wrong**: Introduction to Geometry (2nd ed., 1969) §14.9, p. 262, states Clifford's first three theorems
  and "and so on" — the chain in circles-through-a-point form — but gives no general step. §1.1 now
  says exactly that. The other eleven entries were re-checked (Crossref/OpenAlex, Zenodo API, GitHub
  contents API, the AFP entry page, Mathlib's `docs/1000.yaml` at the pin).
- **The eight unused hypotheses removed.** v1.2 pin `3df056f…`; MorleyKernel 5,607 lines; public raw
  sha `1dfe2f13…`. Hand check before the build confirmed only the *upper* bounds of `kpe5_hi`/`kpe6_hi`
  were unused (dropping the lower bound makes `omega` fail), which corrects the layer-6 report's "hj,
  hj'" wording. Build rc 0, gate PASS 37 std, tamper 8/8 at the new pin; `check/allN.lean` still passes.
- **§4.4 restated on the author's instruction**: the paper now opens by saying the author drafted it
  with the help of automated tools — the idea, direction and feedback his — and keeps the mechanical
  facts (proof scripts by coding agents under his specification; the corner produced in the proof work;
  tools drafting prose at his direction and making reading passes).
- **Result**: 18 pp, 0 overfull, 0 undefined; PDF sha `7ed7581e…`, 188,569 B, built with
  `SOURCE_DATE_EPOCH=1795705200` (2026-11-26T15:00:00Z) so that the build is byte-reproducible; name gate
  **PASS 67/63**, 34 attribution checks.
