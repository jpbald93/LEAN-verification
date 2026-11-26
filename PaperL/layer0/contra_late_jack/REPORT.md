# Layer 5 (contradiction probes) for the late block of `Clifford/MorleyKernel.lean` — jack

Collected 2026-11-25 23:50Z from `jackagent@[build host]`. Tree: `~/paperL_jack`,
`Clifford/MorleyKernel.lean` sha `dce7b011a8f22469…` (pin unchanged).

## What ran

| run | script | log | output | result |
|---|---|---|---|---|
| contradiction probes, lines 816–5592 (257 declarations) | `~/lc_mod/lc_mod_contra.py`, `ONLY_NAMES=~/lc_mod/late_names.txt`, WORKERS=3 | `contra_late.log` (started 17:31Z, `ALL DONE` 19:09Z) | `contra_late_results.jsonl` (267 rows: 257 probes + 9 baseline + 1 satlinkset) | **0 CONTRADICTORY** — 163 `ok`, 93 `no-hyp`, 1 `probe-invalid` |
| the 16 `error-unattributed` battery rows (14 declarations) | `~/lc_mod/lc_mod_requeue.py`, `ONLY_NAMES=~/lc_mod/requeue_names.txt` | `rerun16b.log` (started 19:32Z, `ALL DONE` 19:42Z) | `battery_results.jsonl` (935 rows) | **0 `error-unattributed`** |

The probe is the layer-5 instrument: it tries to derive `False` from a theorem's own hypotheses with a
fixed tactic list (`first | omega | decide | simp_all; done | norm_num | linarith | nlinarith | tauto`),
with a `True` control inserted first. `ok` means the limited search failed — **not** that the
hypotheses are certified satisfiable (that is layer 8, §5.2). `no-hyp` means the statement has no
hypothesis binder to probe.

## Probe-invalid declaration

`subfamily_P0_zero_gen` (`Clifford/MorleyKernel.lean`, late block). The row is `probe-invalid`
because the **control** failed to compile, so the probe never ran:

```
work/da54284812e50e18c7fab9fd28cdf54d.lean:5080:45: error: Function expected at
  conj
but this term has type
  ?m.1
```

`conj` is unknown in the probe's namespace and `autoImplicit` binds it as an implicit variable, so
the `True` control is ill-typed. The instrument refuses the row rather than reading it as a pass.
This is the same declaration john's probe run marked invalid; the gap is in the instrument's binder
reconstruction, not in the theorem. No contradiction claim is made for it, and it is excluded from
the `ok` count.

## Final battery tallies (935 rows)

| step | rows | decls | outcome |
|---|---|---|---|
| baseline | 9 | 8 files | 9 ok |
| 4 — mutation | 631 | 259 | 535 killed, 95 killed by heartbeat/wall-clock timeout, 1 SURVIVED, **0 unattributed** |
| 5 — contradiction probes | 294 | 294 | 147 `ok`, 125 `no-hyp`, 22 timeout, **0 CONTRADICTORY, 0 unattributed** |
| 8b — witness linkage | 1 | 1 | 1 ok |

The re-run moved every previously unattributed row into a decisive class: the nine mutation rows are
now `killed` (mutant row total 631, kill total 535 instead of 525 + 9 unattributed), and the seven
contradiction rows are now `ok` (147 instead of 140 + 7 unattributed). The 22 contradiction timeouts
are unchanged and were never unattributed — they are wall-clock limits, not load kills.

## Coverage of the eight audited files

| | declarations | note |
|---|---|---|
| theorem/lemma declarations, 8 audited files (all but `BridgeL10.lean`) | 577 | 343 in `MorleyKernel.lean` |
| with a probe row after this run | **551** (95.4%) | 294 battery + 257 late block; disjoint |
| without a probe row | 26 | the six primed names jack's collector skips (`d7_children_gcircleS'`/`''`, `hodd_inf'`, `hodd_inf_all'`, `hodd_one_P0_line'`, `p0_levelpts_collinear'`) plus 20 `GenPosN`/determinant corollaries and definitional restatements (`cliffordChainS_inf`, `cliffordChainS_of_corner`, `cliffordChainS_of_inf`, `evenCornerQL_proof`, `EvenCorner_proof`, `parent_on_child_line`, `child_det_M7`/`child_det_MN`/`parent_det_MN`, `c5_genPosN`/`c6_genPosN`/`d7_genPosN`, `stepEven_gen`, `stepOdd_core`, `blockRev_val`, `child_line_P0`/`child_line_P0N`, `p0_levelpts_gcircleS`, `evenCorner_of_cornerQL`) |

Per-file probe coverage inside `MorleyKernel.lean`: 317 of 343 declarations (60 from the first
battery, all before line 816, plus the 257 of this block).

## Honest limits (unchanged)

A failed tactic search is not a satisfiability certificate: layer 5 can only report "no
contradiction found in 20 s of tactics", and layer 8 is a separate instrument (§5.2). The 22
timeouts are limits, not results. The 26 unprobed declarations are not probed, and the paper says so.

## Files

- `contra_late_results.jsonl` — 267 rows of the late-block run (257 probes + 9 baseline + 1 satlinkset).
- `battery_results.jsonl` — the full battery file after the re-run (935 rows).
- `summary.md` — the harness's own summary (generated 19:09Z by the late-block run; its probe line
  is contra-only, 163 `ok` / 93 `no-hyp` / 1 invalid).
- `contra_late.log`, `rerun16b.log` — both end `ALL DONE`.
- `SHA256SUMS`.
