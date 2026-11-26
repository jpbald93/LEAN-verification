# John's outstanding Paper L work — finished on jack (2026-11-24)

John (`joshs-mac-mini`) has been offline since 2026-11-20. Two items were queued for him:

1. the second-machine battery leg (`layers 1,2,4,5,7,8`), whose report never got past layers 1–2 and
   whose layers 4/5 stopped mid-run with 17 flagged survivors;
2. the layer-13 second-machine reproduction.

What jack can and cannot substitute is stated at the end. What was actually outstanding as *work* —
the survivor classification and the mutation coverage those survivors came from — has now been done
on jack.

## 1. The 17 survivors: reproduced and classified (jack, 2026-11-24 21:26Z)

John's 17 flagged rows came from five declarations, all of them in the part of
`Clifford/MorleyKernel.lean` that jack's first battery never mutated (jack's 61 mutated declarations
sit at lines 33–806; these five are at lines 1578, 2740, 3893, 5036 and 5475). Jack was pointed at
exactly those five declarations (`ONLY=ins_eval,dX_cD,kpe_P0,polyF_natDegree_le,child_line_of_parent_mid_zero`,
`WORKERS=6`, 26 jobs, 8 min). Result: **13 survivors, 8 killed, 0 unattributed**, no baseline
failure, no contradiction flag. All 13 are the same class john saw — the mutant's own proof
compiles, so the mutated statement is a theorem; the question is only whether anything downstream
notices.

| declaration | mutation | downstream |
|---|---|---|
| `ins_eval` | `lit0->1` | caught at line 1647 |
| `dX_cD` | `neg1->1` (arg 1) | caught at 2761 |
| `dX_cD` | `neg1->1` (arg 3) | caught at 2761 |
| `dX_cD` | `lit1->2` | caught at 2761 |
| `dX_cD` | `lit2->3` | caught at 2761 |
| `dX_cD` | `lit5->6` | caught at 2761 |
| `kpe_P0` | `lit5->6` | caught at 3922 |
| `polyF_natDegree_le` | `lit5->6` | caught at line 5574 |
| `polyF_natDegree_le` | `lit2->3` | caught at line 5574 |
| `child_line_of_parent_mid_zero` | `u ≠ 0 → u = 0` | **not caught** |
| `child_line_of_parent_mid_zero` | `u ≠ 0 → u ≠ 1` | **not caught** |
| `child_line_of_parent_mid_zero` | `eq->ne` (offset 351) | **not caught** |
| `child_line_of_parent_mid_zero` | `ne->eq` (offset 186) | **not caught** |

Read: nine of the thirteen are caught downstream, which is what "true but different" means in this
battery — no hole. The four `child_line_of_parent_mid_zero` rows are not caught anywhere, and they
are the interesting ones: the direction vector can be constrained to `u = 0` (all grandchild points
coinciding — the exact corner coincidence of `evenCorner_of_QL`) or to any `u ≠ 1`, and the statement
is still provable. So `u ≠ 0` is not doing the work the statement's shape suggests; this is the same
family as the unused-hypothesis list in §5.8 (`parent_on_child_line`'s `hQ0`). It does not affect the
headline theorems, but it belongs in the paper's unused-hypothesis account.

John's "7 unexplained ~120 s rows" cannot be reproduced item by item: the identities live only in
john's `results.jsonl`, which is on the offline machine. What can be said: on jack, the same five
declarations produce 13 survivors, every one a compilable mutant, none unattributed — the ~120 s
cluster looks like a harness-timeout artefact, not a class of its own.

## 2. The coverage gap those survivors exposed — running now

The reason john's survivors existed at all is that jack's first battery stopped mutating at line 807.
That gap is the paper's §5.1 limit #1. On 2026-11-24 21:28Z jack started the **remaining 275
theorems/lemmas of `Clifford/MorleyKernel.lean`** (891 mutant jobs, 8 workers, contradiction probes
skipped — they already cover 294 declarations):

- run dir `jack:~/leancheck/out/paperL_lateblock/` (`run.log`, `results.jsonl`, `summary.md` on
  completion),
- expected completion ~4.5–6 h, i.e. late 2026-11-24 EST / early 2026-11-25 UTC.

When it lands, the mutation audit covers the whole of `MorleyKernel.lean` rather than its first 806
lines, and §5.1 of the draft can drop its "no round 19–26 declaration was mutated" sentence.

## 3. What jack cannot finish

**The second-machine receipt.** jack is the first machine; a re-run on jack is a reproducibility run,
not independence. No number from it can honestly be entered against john's row. The receipt stays
open until john is back (or another machine with a Lean build is available — the `openclaw-vm` host
has `elan`/`lake` but no Mathlib cache, so a from-scratch build there is a multi-hour job, not a
five-minute one).

Also still unavailable: john's raw report and `results.jsonl`, so his exact 17 rows cannot be
reconstructed; his timings (74 s / 67 s etc.) remain recorded-not-verified.

## 4. Where this lands in the paper

- §5.1 limit #1: replace "mutation reached 61 of 343" with the completed count once the late block
  finishes; the "no round 19–26 declaration" sentence goes.
- §5.8: add `child_line_of_parent_mid_zero`'s `u ≠ 0` to the unused/degenerate-hypothesis list.
- §5.5: keep john's receipt as unverified; add that the survivor class was reproduced on jack
  (13 rows, 9 caught downstream, 4 uncaught and explained) and that this is not a second-machine
  cheque.

## 5. Update 2026-11-25 02:20Z — john is back, the receipt is no longer blocked

John came online at ~01:55Z on 2026-11-25. What changed:

- **His 19 Nov report and raw rows are collected** in `layer0/john_receipt_20261119/`
  (`BATTERY.md`, `BATTERY.log`, `RESULTS_20261119.jsonl` = 2,130 rows). The row file settles §3's
  "recorded-not-verified" gap: the report was real and reproduces the verdict it printed, but its
  scope was the whole 577-declaration tree, not jack's 259-declaration run.
- **The ~120 s rows are explained.** Median row cost on john is 121.3 s — 1,303 of 1,900 timed rows
  sit in the 100–140 s band, max 177.6 s — because the harness re-elaborates the whole
  `MorleyKernel.lean` per mutant. They were never a separate anomaly class.
- **Survivors reconciled.** John's 17 = jack's 13 targeted survivors plus `cliffordChain_one`
  (caught downstream by `cliffordChain_iff`), `p0_children_gcircleS_genPos` (its `_hP0` is on jack's
  layer-6 UNUSED list), and `p0_children_gcircleS_false` / `hodd_inf_zero` (same family). No hole.
- **Layer 13 now has its second-machine reproduction**: `BlindCompareFull.lean` (sha `32dfa1b2…`)
  elaborated clean on john at the pin, rc 0, 5.41 s (jack 2.8 s).
- **Like-for-like battery running on john from 02:06Z**: all 343 declarations of
  `MorleyKernel.lean`, 1,426 mutant jobs + contradiction probes, 10 workers. Collection and verdict
  scheduled 07:30 ET (`rem_4cc14234…`).

§4's instructions stand, with one change: §5.5 can cite a real second-machine row once that
battery finishes, and john's timings are no longer unverified.
