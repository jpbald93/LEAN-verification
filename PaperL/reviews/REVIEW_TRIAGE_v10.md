# Review triage — Opus 5.5 pass on draft v0.10 (2026-11-26)

Instrument: `claude-opus-5-5` via `opencode run`, one independent session; inputs = `DRAFT_v10.md`,
the pinned tree, the published code repository and `PaperL` folder; no Lean toolchain. The v0.9
referee report was withheld so this pass is independent. Report: `REVIEW_v10_opus.md` (verdict
**MINOR REVISION — 1 MAJOR / 10 MINOR / 2 NOTE**). Result: **v0.11**. All thirteen items accepted
after checking each against the data or the source. No Lean proof, statement or definition changed.

| id | sev. | claim | my check | disposition |
|---|---|---|---|---|
| M1 | MAJOR | "397 declarations carry a witness of their hypotheses" overclaims: the 397 split by statement class into 210 hypothesis-free, 119 closed (no binders), 68 with hypotheses; `Prop`-packed hypotheses are invisible; the corner lemma `parent_crossVec_zero_of_mid` is unresolved on both machines. | Recomputed from `sat_jack/results.jsonl` and `sat_john/results.jsonl`: jack 226/119/55 of 400, john 209/119/66 of 394; the 397 shared set splits **210 hyp-free / 119 closed / 68 hyps**. `kind` field present per row. `parent_crossVec_zero_of_mid` unresolved on both. | **ACCEPTED.** §5.2 now reports the split and says layer 8 witnesses 68 hypotheses, not 397; `Prop`-packed invisibility stated; corner inhabitation rests on §1.1's numerical witness. §5.1's "satisfiability layer" clause qualified the same way. Abstract updated. |
| m1 | MINOR | Only two of the four `child_line_of_parent_mid_zero` survivors touch `u ≠ 0`. | `lateblock_jack/results.jsonl`: `ne->eq@18` and `lit0->1@20` touch `u ≠ 0`; `ne->eq@186` flips the grandchild-finiteness antecedent; `eq->ne@351` flips the incidence equation. | **ACCEPTED.** §5.1, §5.8, App. C v0.10 item 2 refined. |
| m2 | MINOR | S7 has the same `BlindGenPos`/`GenPosN` gap used to exclude S1, so it is not purely definitional; it is closed by a direct proof (`N7_RB`). | `BlindCompareFull.lean` `BlindN7` quantifies over `BlindGenPos`; `N7_RB` (`BridgeBlind.lean:645`) proves it without `RealN7`. | **ACCEPTED.** §5.3: S6 alone definitional; S7 definitional plus hypothesis gap, closed outright. |
| m3 | MINOR | "S4 is false as written" is a hand argument, not Lean-checked; label it. | `L13_FULL_COMPARE.md` update says no Lean file was changed; the triple's coordinates are exact and the argument is elementary. | **ACCEPTED.** §5.3 now names it a hand argument on exact coordinates (second points `2+2i`, `(1−√3/2)+i(1+√3/2)`, `3+i√3`). |
| m4 | MINOR | The S1 paragraph omits the published `BlindChain.lean` direct route and offers "rescoping" that the notes rule out. | `layer13/BlindChain.lean`: 1,296 lines, sha `6d5bfe5d…`, one `sorry` at 1,252; `BRIDGE_NOTES.md` §4 says closing S1 means proving the blind chain directly, not rescoping. | **ACCEPTED.** §5.3 records the direct route (levels 3–4 for every `BlindGenPos` tuple, level 5 conditional, all-`n` reduced to `blindClifford_second`) and drops rescoping as an option. |
| m5 | MINOR | §5.1: 19 declarations on which no mutant was generated are described as ones the generator "cannot alter"; the headline is called a corollary; john probed all 26 jack left unprobed. | Several of the 19 have mutable literals (`parent_on_child_line`, `parent_det_MN`, `child_det_M7`, `stepOdd_core`); `cliffordChainS_inf` is the headline; `john_receipt_results.jsonl` has 343 probes over all 343 `MorleyKernel` declarations. | **ACCEPTED.** Wording changed to "produced no mutant"; "the headline, not a corollary"; john's 26-declaration coverage added. |
| m6 | MINOR | Late-block probes end at 5586, not 5592 (the draft lists `cliffordChainS_inf` at 5592 as unprobed); the gate counts 8 range tokens (4 spans), not three. | Recomputed the 257 probe names against the source: min 816, max **5586** (`heven_inf_all`). `namegate.py` prints 8 ranges; grep counts four distinct spans. | **ACCEPTED.** All four "816–5592" occurrences → 5586; §3 says eight range citations (four distinct spans). |
| m7 | MINOR | John's battery report is published, so App. A must not call it external; layers 1, 2, 7 are not jack-only; the "unreachable from 11-19" date is too broad. | `layer0/john_receipt_20261119/BATTERY.md`: gate PASS 36, tamper 8/8, baseline 8/8, linter 0 in 8 files, same pin, wider file set. `JOHN_LEG.md`: offline from 2026-11-20. | **ACCEPTED.** App. A bullet rewritten (published; host-only list now the battery report/timings); §5.11 and App. B record the john runs for layers 1, 2, 7 as wider-scope corroboration; §4's date qualified to the evening of 2026-11-19. |
| m8 | MINOR | App. A promises a path mapping §3 refers to and does not contain one; host-only raw outputs behind layers 6/7/9 are not published. | App. A had only a base-directory sentence; the 501/8 and 137/24/113 figures trace to the notes excerpt and the jack battery report, which is host-only. | **ACCEPTED.** App. A gains the mapping table (artifact → `preprint/`, `reports/`, `reviews/`, `layer0/`, `layer13/`, `check/`, `evidence/`) and names the host-only outputs. |
| m9 | MINOR | Layer-11 provenance says "through v0.7" (§5.11), "v0.4 to v0.8" (App. A), "through v0.9" (App. B); the v0.9→v0.10 review is missing. | Grep of the three statements; `L11_NAMEGATE.md` is headed v0.10 and reproduces 143/98/25/85. | **ACCEPTED.** All three now say through v0.11; §5.11 and App. B row 12 record the v0.9→v0.10 and v0.10→v0.11 rounds. |
| m10 | MINOR | Three published reports still describe `u ≠ 0` as an unused hypothesis. | `lateblock_jack/REPORT.md`, `RECEIPT_VERDICT.md`, `JOHN_LEG.md`. | **ACCEPTED.** Each carries a dated correction notice pointing at the paper's corrected account; the raw rows are untouched. |
| N1 | NOTE | §1.1 repeats the numerical-witness caveat three times and duplicates one sentence opening. | Read §1.1. | **ACCEPTED.** Caveat stated once; duplicate merged. |
| N2 | NOTE | Reproduction should include `lake exe cache get` and say the manifest fixes Mathlib. | `gate.sh` exits without `.lake/packages/mathlib`; `lakefile.toml` names `v4.33.1`, manifest pins `0df444a3…`. | **ACCEPTED.** Added to §3 Availability (and already in the release README). |

## What was checked and found correct

Opus's "Checked and correct" list agrees with my own re-checks: the eleven hashes and line counts
(8,311 Lean lines), 156 files at the pin, the file modes, the toolchain and Mathlib pins, the citation
gate 143/98/25/85 reproduced on v0.10, the headline call chain, the `_hall` usage, the round-26
provenance (5,611-line scratch file, 5,344-line identical prefix, 267-line suffix, hunks at
1006–2005), the eight unused-hypothesis items, the mutation/contradiction tallies (631 = 535+95+1,
294 = 147+125+22, 891 = 872+3+16, 343 probes), the identical john survivor set, the satisfiability
numbers (which M1 reinterprets, not disputes), the corner margins, the layer-13 file shas, and the S1
counterexample counts. Its two flagged assertions were confirmed: the empty-branch reading of
`child_line_of_parent_mid_zero` (with m1's correction to which mutants touch `u ≠ 0`) and the S4
falsity as a hand argument.

## Effect on the release

v0.11 is a new build (27 pp). The code repository is untouched by this round. The supporting folder
gains the Opus report and this triage, the v0.11 preprint, and the three correction notices; the v0.10
files are kept under `preprint/superseded/`. The Zenodo kit carries `paperl_v11.pdf`.

Source: target=@dm:ch_dm_66f390589f07cd0b5334 comet_message_id=12466884 date=2026-11-26
sender=Josh Bald/b6ba674e-2ef4-4c87-901a-1771e2421129
