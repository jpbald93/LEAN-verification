# Layer 8 (satisfiability) on john — independent pass

Collected 2026-11-25 21:05 ET (2026-11-26 02:05Z) from `john@[second host]` (`joshs-mac-mini`).
Tree: `~/lean/paperL_john`, pin `dce7b011…`, same generator as jack (`~/lc_sat.py`, a copy of
jack's `~/lc_mod/lc_sat.py`), `WORKERS=3`, `TRIES=3`, `SAT_BUDGET=72000`.

## Result

| | declarations |
|---|---|
| theorem/lemma declarations in the tree | 584 |
| **SAT-CERTIFIED** | **394 (67.5%)** — 356 deterministic, 3 deterministic-pattern, 35 model-witness |
| unresolved | **190 (32.5%)** — 93 hypothesis-free, 97 with hypotheses |
| stmt-invalid / llm-error | 0 / 0 |
| baseline (9 files) | 9 ok |
| layer 8b witness links | 0 (no `*_sat` declarations in the tree) |

Run: 07:12 PST → 17:29 PST 2026-11-25 (10 h 17 min), log ends `ALL DONE`. `summary.md` is the
harness's own; its per-machine line reads `SAT 394 / unres 190`.

Certification by statement class: 209 of the hypothesis-free declarations, 119 with no bound slots
at all (`closed`), 66 with hypotheses. Nothing was refuted: `stmt-invalid` is 0, so no declaration's
existential statement failed to elaborate.

## Machine-only results

577 of john's 584 declarations are also sat-run on jack. 560 of the 577 agree on the verdict class,
17 disagree (14 john-only certificates, 3 jack-only), and 397 of the 577 are certified by at least
one machine; the full per-declaration comparison is in `../sat_jack/REPORT.md` (`SAT_COMPARISON`).

## Files

- `results.jsonl` — 594 rows (584 `sat` + 9 `baseline` + 1 `satlinkset`).
- `unresolved_names.txt` — the 190 unresolved declarations, sorted.
- `summary.md` — harness summary (07:29 PST).
- `sat_john.log` — full run log.
- `SHA256SUMS`.
