# John's second-machine receipt — status (2026-11-25 02:20Z)

John (`joshs-mac-mini`, `john@[second host]`) came back online at ~01:55Z on 2026-11-25
(18 cores, 48 GB, macOS). Tree `~/lean/paperL_john` is at the paper's pin:
`Clifford/MorleyKernel.lean` sha `dce7b011a8f224699f7ea1e879a159fc8066e15f3cb8c6e7664c03a779990a76`.
Seven of its eight library files are byte-identical to jack's; the root `Clifford.lean` differs
(john's is `80aabb5e…`, jack's `8bb0f5f0…`) and jack has `BridgeL10.lean` which john does not.
Neither difference touches `MorleyKernel.lean`.

## 1. His 19 Nov battery — collected (was never copied over)

`BATTERY.md` / `BATTERY.log` are the report as produced on john at 2026-11-19 14:39Z, and
`RESULTS_20261119.jsonl` (2,130 rows, sha `15139e66…`) is the raw row file behind it. Verdict:

| check | john, 2026-11-19 |
|---|---|
| gate (layer 1) | PASS (36 declarations, standard axioms only) |
| tamper (layer 2) | 8/8 rejected |
| baseline build | 8 of 8 files ok |
| mutation (layer 4) | 1,527/1,544 rejected; 17 SURVIVED; 0 unattributed |
| contradiction (layer 5) | 0 contradictory (347 ok, 229 no-hyp, 1 probe-invalid) |
| linter (layer 7) | 0 warnings |

Scope caveat: that run audited the whole tree as it then stood — 577 declarations — not the
259-declaration scope of jack's battery, so it is corroboration, not a like-for-like receipt.

## 2. The "seven unexplained ~120 s rows" — resolved

They were not an anomaly class. From the raw rows:

- 1,900 of the 2,130 rows carry a wall-clock time; median **121.3 s**, mean 88.7 s, min 4.6 s,
  max 177.6 s. **1,303 rows** fall in the 100–140 s band; none exceed 180 s.
- ~120 s is simply what one check costs on john: the harness re-elaborates the whole
  5,611-line `MorleyKernel.lean` for every mutant, so almost every row lands at the same cost.
- The 13 rows john recorded as `killed-timeout` are heartbeat limits, not wall-clock
  cut-offs — the same class jack reproduces on the same declarations.

So john's earlier "7 rows at ~120 s that jack cannot explain" were ordinary rows read in
isolation. Nothing about them was machine- or harness-specific beyond that fixed cost.

## 3. Survivors reconciled: 17 on john = 13 on jack + 4 explained

John's 17 SURVIVED rows, by declaration: `child_line_of_parent_mid_zero` ×4, `dX_cD` ×5,
`polyF_natDegree_le` ×2, `ins_eval`, `kpe_P0`, `cliffordChain_one`, `hodd_inf_zero`,
`p0_children_gcircleS_false`, `p0_children_gcircleS_genPos`.

Jack's targeted re-run of the five uncovered declarations (2026-11-24 21:26Z) produced 13, all
of which appear in john's list. John's other four are consistent with jack's own findings:

- `cliffordChain_one` — jack's first battery's single survivor, caught downstream by
  `cliffordChain_iff`; a true-but-weaker mutant, not a hole.
- `p0_children_gcircleS_genPos` — jack's layer-6 ablation lists its `_hP0` as **UNUSED**.
- `p0_children_gcircleS_false`, `hodd_inf_zero` — same family (mutant provable as stated).

No survivor is an unproved hole.

## 4. Layer 13 — second-machine reproduction DONE (2026-11-25 02:15Z)

`layer13/BlindCompareFull.lean` (sha `32dfa1b2…`, the file jack compiled clean) was copied to
john as `~/lean/paperL_john/layer13_receipt.lean` and elaborated in john's tree at the pin:

```
$ lake env lean layer13_receipt.lean
warning: mathlib: repository ... has local changes
warning: batteries: repository ... has local changes
real 5.41   user 2.54   sys 2.49
rc=0
```

Clean on the second machine, no errors, no `sorry` warnings — john 5.41 s, jack 2.8 s. The two
warnings are about the local `.lake/packages` checkouts, not about the proof.

## 5. Like-for-like battery — running (started 2026-11-25 02:06Z)

`john:~/lc_mod_receipt.py` is jack's `lc_mod.py` with `OUT=~/leancheck/out/paperL_john_receipt`,
`REPOS=('lean/paperL_john',)` and a file filter to `MorleyKernel.lean`, so the scope matches the
paper: **all 343 declarations, 1,426 mutant jobs plus the contradiction probes**, `WORKERS=10`,
`CTIMEOUT=900`. Materialised tree at the pin, baseline `1 ok of 1`.

State at 02:13Z: 21 rows, run live. At that rate it lands early morning 2026-11-25; the
collection-and-verdict job is scheduled for 07:30 ET (`rem_4cc14234…`) and will write
`RECEIPT_VERDICT.md` plus the draft wording change.

Nothing in this batch changed the Lean tree; the receipt is a second-machine reproduction of
results already on jack, so no claim in the paper moves until the battery numbers are in.
