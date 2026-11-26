# Review triage — referee pass on draft v0.9 (Astra, 2026-11-26)

Instrument: `gpt-6-astra` via `opencode run`, one independent session, inputs = `DRAFT_v09.md`, the
pinned tree (`d15464f` bundle clone) and the published reports; no Lean toolchain, no compilation.
Report: `REVIEW_v09_astra.md` (verdict **MAJOR REVISION — 2 MAJOR / 8 MINOR / 0 NOTE**). Draft under
review: v0.9; result: **v0.10**. All ten findings accepted after checking each against the source or
the record. No Lean proof, statement or definition changed.

Row closure of the earlier v0.3 findings (R-01…R-09), per the same report: **CLOSED 5** (R-01, R-04,
R-05, R-06, R-07), **PARTIAL 4** (R-02, R-03, R-08, R-09) — each partial is folded into a v0.9 finding
below and fixed, so all nine are closed in v0.10.

| id | sev. | claim | my check | disposition |
|---|---|---|---|---|
| V09-01 | MAJOR | The four surviving mutants of `child_line_of_parent_mid_zero` are misreported as an unused **input** hypothesis `u ≠ 0`; it is a conjunct of the existential **conclusion**, and the lemma is an empty branch (`absurd (parent_crossVec_zero_of_mid …) hv`). | Read `Clifford/MorleyKernel.lean:5034–5046`: conclusion is `∃ p u, u ≠ 0 ∧ …`; premises include `hv : V ≠ 0`, `hmid`, `P0 ≠ 0`; proof is `absurd (…) hv`; docstring "Under `hv` the branch is empty". | **ACCEPTED.** §5.1 and §5.8 re-described; the lemma leaves the unused-input list; 501/8 ablation tally unchanged, because layer 6 never saw the lemma (§5.8 already said so). |
| V09-02 | MAJOR | S4/S5 are not "definitional": the writer's `BlindCliffordFin` forbids ∞ at every level, so lines cannot be represented, while the library's `CliffordChain` admits them; the recorded `BlindGenPos` triple with collinear seconds makes the writer's S4 false at `n = 3`. | Read `scratch/BlindCompareFull.lean:13–58` (`BlindPlane`, `BlindIsGCircle`, `BlindCliffordP true → X ⊆ BlindPlane` at every level); read `BRIDGE_NOTES.md` §2 triple; recomputed the three second intersections (`2+2i`, `0.634+2.366i`, `3+1.732i`): distinct, collinear (imaginary part of the cross ratio 8e-16), centres concyclic through 0. Three distinct collinear points admit no positive-radius circle; the only generalized circle through them is their line, which contains ∞ and fails `X ⊆ BlindPlane`. | **ACCEPTED, and made stronger in the paper**: the blind writer's S4 statement is false as written at `n = 3`; the library cutoff includes `n = 3` and is untouched. §5.3 rewritten (S6/S7 remain definitional; S2/S3 quantifier; S1 hypothesis gap; S4/S5 encoding); §5.3 OPEN line, App. B row 13, App. C v0.10; `L13_FULL_COMPARE.md` row-4 verdict corrected with a dated note; `L13_REPORT.md` supersession header. |
| V09-03 | MINOR | "nine-test" is wrong (script lists eight), and `tests/tamper.sh` is mode 100644, so `bash tests/tamper.sh` is the reproducer. | `tests/tamper.sh:68` = `sorry ax2line evalfake macro wrap falsehyp cleanand classify6` (8); `tamper.log` 8 rows; `git ls-tree` shows mode 100644 (gate.sh 100755). | **ACCEPTED.** §3 Availability and §4 build receipt now say eight and `bash tests/tamper.sh`; release README corrected in a new commit. |
| V09-04 | MINOR | Citation gate makes 25 attribution checks, not 22; L11 report title still says v0.3. | `namegate.py` on v0.9/v0.10 prints `attribution checks: 25`; report regenerated today. | **ACCEPTED.** §3 says 25; `L11_NAMEGATE.md` regenerated for v0.10 (PASS 143/98/25/85) and the script's stale "v0.1/v0.2 only" line corrected. |
| V09-05 | MINOR | The supporting folder does not "mirror" the artifact directory; Appendix A's prefix convention is inconsistent; john's original battery report is no longer unavailable. | Checked the published `PaperL` layout (`preprint/`, `reports/`, `reviews/`, `layer0/`, `layer13/`, `check/`, `evidence/`) against App. A's paths; `layer0/john_receipt_20261119/BATTERY.md` is published. | **ACCEPTED.** Availability describes the layout and points to App. A for the mapping; App. A's externally-hosted bullet now names only the round-26b timings and host-only logs, and records john's battery report as published. |
| V09-06 | MINOR | "it also refuted the rank route" overstates a numerical search; the `1e-8` collinearity figure belongs to the earlier run. | `RANK_ROUTE_COUNTEREXAMPLE.json`: `V_abs_max 4.16e-10`, `collinear_max_dev 3.89e-5`, caveat ties `1e-9`/`1e-8` to the earlier looser run (`transversal 0.04`, `triP 0.14`). | **ACCEPTED.** §1.1 says numerical evidence, gives the stored tuple's numbers, and attributes `1e-9`/`1e-8` to the earlier run; exact nonemptiness still not claimed. |
| V09-07 | MINOR | §5.1 still lists "a satisfiability pass" as OPEN; §5.5's timing sentence garbles which machine each timing belongs to; App. C v0.9 says no number changed while changing 153 → 156. | Read §5.1 item 1 tail, §5.5 lines 816–818, App. C v0.9. | **ACCEPTED.** OPEN now names only the expected-job manifest; timings labelled (71 s jack, 74 s john promotion; 67 s john scratch receipt); v0.9 entry says no mathematical statement/proof/citation changed and that the inventory count was corrected. |
| V09-08 | MINOR | Published layer-13 summaries contradict the current state (N6_RB listed with `sorryAx`; "only definitional row" sentence; stage-4a account). | Read `L13_BRIDGE_STATUS.md:23–25` vs its own 13:05Z section and fresh check; `L13_FULL_COMPARE.md:110–112`; `L13_REPORT.md` stage 4a. | **ACCEPTED.** Report files corrected with dated notes (see V09-02); the audited pin and raw logs untouched. |
| V09-09 | MINOR | §4 layer-5 row says a failed search does not certify **unsatisfiability**; the intended warning is that it does not certify **satisfiability**. | `CONTRA_LATE_REPORT.md` §"what `ok` means"; §5.2 uses the correct direction. | **ACCEPTED.** One word fixed. |
| V09-10 | MINOR | "rest on the gate, tamper and axiom checks alone" and the machine-count summaries are broader than the record. | `SAT_*_REPORT.md` covers the whole inventories; `JOHN_RECEIPT_VERDICT.md` restricts the like-for-like run to `MorleyKernel.lean`; the bridge file was compiled on jack only. | **ACCEPTED.** §5.1 says "not covered by mutation" and names the satisfiability layer; §5.11 and App. B scope layers 4/5 on john to `MorleyKernel.lean` and layer 13 on john to `BlindCompareFull.lean`. |

## What was checked and found correct (not re-litigated)

The report's "Checked and correct" section matches my own re-checks where they overlap: the public
repository at `d15464f` with 156 files and additive `check/`; all eleven §3 hashes; 8,311 Lean lines;
the toolchain and Mathlib pins; 143/98 citations (the 25 attribution checks are new here); the
mutation/contradiction arithmetic (631 = 535+95+1, 294 = 147+125+22, 257 = 163+93+1, 551/577, 891 =
872+3+16, 318/343); the satisfiability numbers (400/596, 394/584, 577 shared, 560 agree, 17 differ,
397 union, 180 neither); the corner mechanism; and the novelty scope. Its "no new experiment"
restriction was respected: nothing in this round requested or produced a new run.

## Effect on the deposit

The v0.10 PDF is a new build (25 pp). The code repository is unchanged except the README correction
(eight tests, `bash`), which is a commit on `main` after the pin; nothing in the audited tree moves.
The Zenodo kit carries the v0.10 PDF.

Source: target=@dm:ch_dm_66f390589f07cd0b5334 comet_message_id=12464728 date=2026-11-26
sender=Josh Bald/b6ba674e-2ef4-4c87-901a-1771e2421129
