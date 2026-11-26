# Paper L — v0.2 review triage: dispositions in v0.3 (2026-11-24)

All nineteen merged rows of `REVIEW_TRIAGE_v02.md` are applied in `DRAFT.md` v0.3 (rows 2, 5, 7, 15 and 16 completed in v0.4; see `REVIEW_TRIAGE_v03b.md`). **No Lean proof
changed** — every finding was about what the paper says about its formalisation and its evidence. Two
new Lean-free check files were added under `check/` (and on `jack:~/paperL_jack/scratch/`), both
`lake env lean` rc 0 with **std** axioms:

| check | what it proves | time | axioms |
|---|---|---|---|
| `check/allN.lean` | `∀ n, CliffordChainS n`, composed from `cliffordChainS_of_le_five` and `cliffordChainS_inf` | ~3 s | `[propext, Classical.choice, Quot.sound]` |
| `check/not_UniqEven.lean` | the even-level point is **not** unique: both `{4i}` and `{∞}` satisfy `ChainS 6` for the centres `2t−2it²` | ~27–28 s | `[propext, Classical.choice, Quot.sound]` |

| # | finding (short) | sev | disposition in v0.3 | where |
|---|---|---|---|---|
| 1 | `UniqEven` is false, not open | MAJOR | Applied. §2.4 states the failure with the checked counterexample and withdraws uniqueness as a possible theorem; §5.4 makes it a named limit; `L13_REPORT.md` stage 5 corrected. | §2.4, §5.4, `L13_REPORT.md` |
| 2 | layer-13 comparison did not preserve the writer's types | MAJOR | Applied. §5.3 gives the four facts (definite article in BLIND.txt; writer's `∃p ∧ ∀p`; stage 4b restatement in existential form; only N1–N3); "structure untouched" and "strictly stronger" withdrawn; N2_RB/N3_RB hypotheses named. `L13_REPORT.md` and `L13_COMPARE_NORM.md` corrected. | §5.3, §2.3, §2.4, `L13_*` |
| 3 | layer 8 disabled, 8b unrecorded, layer 5 `ok` misdescribed | MAJOR | Applied. §4 rows 5/8/8b rewritten; §5.2 states `sat = []`, no `satlinkset` rows, `ok` = failed proof search, layer 13 does not substitute. | §4, §5.2 |
| 4 | mutation/contradiction coverage much narrower than claimed | MAJOR | Applied. §5.1 new item 1: 577 declarations, 294 contradiction (234 outside `MorleyKernel` + 60/343 inside), 259 mutation (198 + 61/343), all 61 inside in lines 33–806, round 19–26 material after line 4,000 with anchors; "at every declaration" removed; separated from the 16 inconclusive rows. | §5.1, §4 row 4 |
| 5 | john receipts / timings / corner JSON untraceable | MAJOR | Applied both ways the reviewers allowed: the JSON is bundled (`layer0/r25_jack/RANK_ROUTE_COUNTEREXAMPLE.json`) and labelled numerical; the notes excerpt is bundled (`evidence/math-papers-PaperL-excerpt.md`); john's artifacts are labelled recorded-not-verified everywhere they appear. Grandchildren **coincide** in the exact corner. | §1.1, §4, §5.5, App. A |
| 6 | name-gate claim overstated | MINOR/MAJOR | Applied. `namegate.py` extended to read code comments, comma lists and table rows; all bare single-line citations removed; re-run PASS (140 occurrences / 95 distinct / 85 rows); §3 claim rewritten to say what it checks; §3.3 adds 30 signature anchors including `ChainS`, `CliffordChainS`, `lineS`, `IsGCircleS`, `chainS_six*`, `evenCorner_of_QL`, `evenCorner_of_cornerQL`; `L12_REVIEW.md`'s scope stated (v0.1, no signature audit). | §3, §3.3, `L11_NAMEGATE.md` |
| 7 | six identifiers undefined; `h4_pt_inf`/`cliffordChainS_all_of` missing | MINOR | Applied. §2.1 defines `second`, `Transversal`, `GenTriple` (both conjuncts and what the second excludes), `crossVec`, `KP`, `levelPointN`, `EptInf` (with the zero-vector totalization); §2.3 adds `h4_pt_inf` and `cliffordChainS_all_of` as the certificate and the induction. | §2.1, §2.3, §3.3 |
| 8 | Paper D C₆ contradiction | MAJOR (Opus) | Applied. §1.2 qualifies C₆ by its non-degeneracy hypothesis, limits reuse to `n ≤ 5`, names `not_cliffordChain_of_six_le` for `n ≥ 6`. | §1.2 |
| 9 | no single `∀ n` declaration; base-case account disagreed | MINOR | Applied. §1.1 gives the call chain (`cliffordChainS_of_corner` → `cliffordChainS_of_inf'` → `cliffordChainS_all_of`) and the `check/allN.lean` composition; §2.5 cites `cliffordChainS_of_le_five`, not the transports, for the base cases. | §1.1, §2.5 |
| 10 | Carver §/theorem number and scope | MINOR | Applied. §5 pp. 160–161 (Theorem 13), §6 pp. 161–164 (limiting figures); §6 Type 2 point-circle at infinity vs `IsGCircleS` stated; "exactly the reading" replaced by "inspired by … not identical". | §1, §1.2, §2.2, §5.9 |
| 11 | layer 9 counts presented as semantic | MINOR | Applied. §4 row 9 and §5.6 relabel 24/113/75 as inventory flags, name the false positives (`IsGCircleS.infty_mem`, `chainS_six_iff`) and the false negative (`GenTriple`); §5.2/§3.2 cross-reference corrected. | §4, §5.6 |
| 12 | survivor is an alternative level, not a weakening | MINOR | Applied. §4 says `CliffordChain 1 → 2`, same-shape proof term, caught downstream by a type mismatch at `cliffordChain_iff`; "weaker"/"not counted" removed. | §4 |
| 13 | macro count 15 → 13; "docstrings" | MINOR | Applied. §4: 13 use sites (8 `fin_idx` + 5 `fin_idxO`), 15 identifier occurrences including 2 definitions; three module comments; one docstring moved to a module comment. | §4 |
| 14 | "no layer ran twice" false; layer 12 input version | MINOR | Applied. §5.11 and App. B give each layer's input version; the blanket assertion is replaced by an explicit statement that layers 11 and 13 were re-run (corrected re-runs, not reproductions). | §5.11, App. B |
| 15 | definite article implies uniqueness | MINOR | Applied. §2.5 rephrased to "some level-(n−1) object of the family with `c i` deleted", with the reason and a pointer to §5.4. | §2.5 |
| 16 | `layer13/…` paths do not exist on jack | MINOR | Applied. App. A/B cite the packet path (`layer13/…` here) and the host paths separately (`jack:~/paperL_jack/scratch/` for the comparisons, `jack:~/reformal/` for the blind files). | App. A, App. B |
| 17 | `EvenCornerQL` does not use `hall` | NOTE | Applied. §2.4 states it (and why layer 6 cannot see it); §5.8 adds it to the unused-hypothesis list. | §2.4, §5.8 |
| 18 | toolchain and manifest unrecorded | NOTE | Applied. §3 records `leanprover/lean4:v4.33.1` and the Mathlib pin `0df444a3…`. | §3 |
| 19 | receipt/wording notes (log cut, linter split, timeouts, bridge date, scratch-only byte identity, `SCOUT.md` §0 row 18, Clifford dates, "forced to be lines", corner `V = 0`, promoted line numbers) | NOTE | Applied, each at the place it matters: §1 (Clifford 1870–71/1882), §1.1 (`parent_crossVec_zero_of_mid`; coincidence), §2.2 ("forced to be lines" marked as explanation; `SCOUT.md` §0 row 18), §2.4 (byte identity **in the scratch file**), §4 (no `TAMPER_RC`; log section cut at its traceback; 0/37 from `REPORT_L10.md` with the 3+3 split; 525 decisive kills reported separately from 95 timeouts; bridge file post-dates the battery), §5.1/§5.2. | several |

## Still open after v0.3 (none of it a text fix)

* `UniqEven` is refuted, so no uniqueness theorem is pending; but the prose's definite article is
  now flagged as unjustifiable in general, and a canonical-selection-based statement is what the
  paper uses.
* Layer 12 has not run on v0.3; layer 13 has not been re-run against the writer's real types on all
  seven rows.
* Mutation/contradiction coverage of the later half of `MorleyKernel.lean` (item 4 of §5.1).
* Satisfiability pass with the job list enabled (§5.2).
* Second-machine receipt from john (§5.5).
* Pinning: the tree on jack is still a plain directory.
