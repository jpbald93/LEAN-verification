# Layer 8 (satisfiability) on jack — main pass, plus the two-machine comparison

Collected 2026-11-25 21:25 ET (2026-11-26 02:25Z) from `jackagent@[build host]`.
Tree: `~/paperL_jack`, pin `dce7b011…`. Instrument `~/lc_mod/lc_sat.py`, `WORKERS=2`, `TRIES=3`,
`SAT_BUDGET=72000`, log `~/lc_mod/sat_full.log`.

## Result

| | declarations |
|---|---|
| theorem/lemma declarations in the tree | 596 |
| **SAT-CERTIFIED** | **400 (67.1%)** — 373 deterministic, 3 deterministic-pattern, 24 model-witness |
| unresolved | **196 (32.9%)** — 86 hypothesis-free, 110 with hypotheses |
| stmt-invalid / llm-error | 0 / 0 |
| baseline (9 files) | 9 ok |
| layer 8b witness links | 0 (there are no `*_sat` declarations in this tree) |

Run: 13:16:32Z 2026-11-25 → 02:20:32Z 2026-11-26 (13 h 04 min), log ends `ALL DONE`. The results
file has 607 rows: 596 `sat`, 9 `baseline`, 2 `satlinkset` (the linkage step ran twice, both `ok`,
no links). `summary.md` is the harness's own summary written at 01:29Z, i.e. before the last rows;
the tallies above are counted from `results.jsonl` after `ALL DONE`.

Certification by statement class: 226 hypothesis-free, 119 with no bound slots at all (`closed`),
55 with hypotheses. Nothing was refuted: `stmt-invalid` is 0, so no existential statement failed to
elaborate.

## Two-machine comparison (`SAT_COMPARISON`)

John ran the same instrument on `~/lean/paperL_john` at the same pin (`../sat_john/`), 394 of 584
certified.

| | count |
|---|---|
| declarations sat-run on **both** machines | **577** |
| same verdict class on both | **560 (97.0%)** |
| disagreement | **17** — 14 john-only certificates, 3 jack-only certificates |
| certified by **at least one** machine | **397 of 577 (68.8%)** |
| certified by neither | 180 |

The 17 disagreements are witness-search luck, not contradiction: in each the other machine reported
`unresolved`, never a failed statement. Examples of john-only certificates: `finite_bad`,
`norm_t_eq_one`, `onCircleM_iff_lineOf`, `kernelCircle_eq_dist`, `hc_of_genPos`, `lineOf_iff`,
`EptInf_eq_infty`, `exists_line`. Jack-only: `chain3_of`, `stepEven_alg`,
`oddCircleEq_five_degenerate`.

Declarations run on one machine only: 19 are jack-only (determinant/cross-product restatements that
are not in john's tree copy or are outside its file set: `det4_eq_det`, `det5_eq_det`, `mD_eq_det`,
`mN_eq_det`, `cD_eq_zero_iff`, `crossVec_eq_crossProduct`, `miquel_eq_det_div`, …) and 7 are
john-only (`N1_BR`…`N7_BR`, the layer-13 bridge targets that live in john's scratch copy).

## What layer 8 can and cannot be quoted as

Certified means the instrument found a concrete instance and Lean accepted the certificate for
`∃ <binders>, True` — i.e. the declaration's hypotheses are simultaneously satisfiable. Unresolved
means the search failed (deterministic patterns plus at most three model proposals); it is **not** a
refutation and must not be read as "vacuously true". So the honest two-machine claim is: **397 of the
577 shared declarations (68.8%) have a machine-checked satisfiability witness, and the remaining 180
are unresolved on both machines.** The curated witness-table pass (`paperL_sat_witness`, started
2026-11-26 02:21Z) attacks those 180; it has not reported yet.

## Files

- `results.jsonl` — 607 rows (596 `sat` + 9 `baseline` + 2 `satlinkset`).
- `unresolved_names.txt` — the 196 unresolved declarations, sorted.
- `summary.md` — harness summary (01:29Z, pre-final).
- `sat_jack.log` — full run log.
- `SHA256SUMS`.
