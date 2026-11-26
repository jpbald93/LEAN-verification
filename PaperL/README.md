# Paper L — Clifford's chain for every n, in Lean 4

Supporting material for the paper *Clifford's chain for every n: point–circle configurations on the
Riemann sphere, formalised in Lean 4* (v1.1, 26 November 2026; v0.9–v1.0 superseded in
`preprint/superseded/`).

**Companion:** [`preprint/COMPANION.md`](preprint/COMPANION.md) is the verification record — per-file
hashes, the gate's 37 declarations, the mutation, contradiction and satisfiability runs, the two-machine
receipts, the blind-restatement comparison and the document history. v1.0 moved all of that out of the
paper, which now carries only the mathematics and the statements about what was checked.

**Lean code:** <https://github.com/jpbald93/paperl_clifford_chain> — the audited tree is commit
`1001939` (159 files, gate 37 declarations). Every `File:line` anchor in the paper resolves at that
commit.

**Paper:** [`preprint/Cliffords chain for every n - Paper L v1.1.pdf`](preprint/) (18 pp), typeset
with the same LaTeX preamble as Papers I and K. The source is `preprint/paperl.tex`, generated from
`preprint/DRAFT_v1.1.md` by `preprint/build_paperl.py` (pandoc + xelatex); every `File:line` is a live
link to the pinned commit.

## Contents

| path | what it is |
|---|---|
| `preprint/` | v1.1: LaTeX source, PDF, markdown, the companion and the build script; v0.9–v1.0 kept in `preprint/superseded/` |
| `reports/L11_NAMEGATE.md`, `reports/namegate.py` | layer 11: the citation gate and its exact result on v1.1 — 66 occurrences, 63 distinct `Clifford/File.lean:N` pairs, 33 attribution checks, all resolving at the pin |
| `reports/L12_REVIEW.md`, `L12_TRIAGE.md` | layer 12: prose-versus-code review of v0.1 and its dispositions |
| `reports/L13_*`, `layer13/` | layer 13: blind re-formalisation of the seven rows (writer and comparer on different models), the seven-row comparison, the bridge layer (`BridgeBlind.lean`, 9 of 11 statements proved in both directions, 2 open); S6/S7 are bridged in both directions, while S4/S5 are stated over the writer's finite-plane encoding, which forbids lines — S4 is false as written at `n = 3` (see `layer13/L13_FULL_COMPARE.md`, update of 2026-11-26), the S1 direct-proof runs (`BlindChain.lean`, one `sorry` at `blindClifford_second`), and the S1 counterexample search (`s1_counterexample/`) |
| `reports/L14_RESTATEMENTS_v07.md` | layer 14 on v0.7: seven blind restatements, 7 of 7 faithful |
| `reports/L15_PRIOR_ART_v07.md` | layer 15 on v0.7: claim-by-claim prior-art table, PASS with recorded search gaps |
| `reports/PLAN.md`, `SCOUT.md` | the plan and the novelty scout (verdict table, 26 search rows, and the sources recorded as *not searched*) |
| `reports/JOHN_LEG.md` | the second-machine leg: what ran on the second build host and what is only recorded |
| `reviews/` | every review round and its triage: the three-model round on v0.2, the v0.3 review, the v0.7 referee pass that produced v0.8, the v0.9 referee pass that produced v0.10 (`REVIEW_TRIAGE_v09.md`), and the Opus 5.5 pass on v0.10 that produced v0.11 (`REVIEW_TRIAGE_v10.md`) |
| `layer0/` | the machine-produced run records: the round-25/26 collections, the late-block mutation run, the late-block contradiction probes, the two satisfiability passes (jack and john), the curated witness-table round, and the second-machine receipt with its verdict |
| `check/` | `allN.lean` (the all-n composition of the two headline theorems) and `not_UniqEven.lean` (the counterexample to uniqueness of the even-level point) |
| `evidence/` | the excerpt of the round records the paper's provenance appendix cites |

## The verification record quoted in the paper

All of it is `leancheck` output or a fresh compile at the pin; each figure is reproducible from the
files in `layer0/` and the run records in `reports/`.

| layer | result |
|---|---|
| 1 gate | **PASS** — 36 required declarations present, `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]` |
| 2 tamper | **8/8 rejected** (`ALL TAMPERING TESTS REJECTED`) |
| 4 mutation | **1,407 decisive kills** and 98 timeout/heartbeat rows over 516 declarations; **17 survivors**, all accounted for — 9 caught downstream, 3 vacuous, 4 in a deliberately empty branch, 1 true-but-weaker (`cliffordChain_one`); 0 unattributed |
| 5 contradiction probes | **0 CONTRADICTORY** over 551 of the 577 declarations; 1 probe-invalid (its own control failed to compile) |
| 6 ablation | **501 needed / 8 unused** over 262 declarations |
| 7 linter | 0 warnings in 8 library files; 0 warnings across the 31 compiling scratch files |
| 8 satisfiability | jack **400/596** and john **394/584** certified; across the 577 both ran, **397 (68.8%)** certified by at least one and 180 by neither; 0 `stmt-invalid`, nothing refuted. A curated witness table then closed **0 of 107** — a defect of the table, reported as such |
| 9 notion inventory | 137 notions, 24 flagged `has-bridge`, 113 not — a heuristic flag |
| 10 definition bridges | 19 theorems; 13 of the 113 bridged, 25 reclassified INTERNAL, 75 unbridged |
| 11 name/line anchors | **PASS** — 143 / 98 / 25 / 85, 0 bare-line |

Layer 8 is a certificate layer, not a truth layer: `unresolved` is a failed search, not a
refutation, and layer 5's `ok` means the limited search failed, not that satisfiability is
certified. The paper says both in §5.2.

## What is not here

The Lean code is in the code repository, not in this folder. Two artefacts are hosted elsewhere and
are labelled as such wherever the paper uses them: the second host's original battery report and the
flat review packets sent to the review instruments. The paper's §5 lists the remaining limits —
the open S1 lemma, the four layer-13 rows that need new mathematics, the 180 unresolved
satisfiability declarations, Carver unformalised, and the recorded prior-art gaps.

Machine names appear as in the paper (`jack`, `john`); IP addresses are removed from the copies in
this folder, and no file here contains credentials.
