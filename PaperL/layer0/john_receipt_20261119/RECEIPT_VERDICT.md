# Second-machine receipt — verdict (john, 2026-11-25)

> **Correction notice (2026-11-26, v0.11).** This report describes the four surviving mutants of
> `child_line_of_parent_mid_zero` as mutations of an "unused hypothesis" `u ≠ 0`. That reading was
> wrong: `u ≠ 0` is a conjunct of the existential conclusion, the lemma's hypotheses are inconsistent
> on purpose, and two of the four mutants touch `u ≠ 0` while one flips the finiteness antecedent and
> one the incidence equation. The paper's §5.1/§5.8 and Appendix C carry the corrected account.

**Reproduced.** John audited the same file at the same pin with the same generator as jack's late
block, and returned the **identical sixteen survivors** and **zero contradictions**.

## What ran

- Host: `john@100.101.160.66` (Mac mini, macOS), tree `~/lean/paperL_john`, pin `dce7b011…`.
- Script: `john:~/lc_mod_receipt.py` — jack's `lc_mod.py` patched only in `OUT`, `REPOS` and the file
  filter; `WORKERS=10`, `CTIMEOUT=900`.
- Scope: all 343 `theorem`/`lemma` declarations of `Clifford/MorleyKernel.lean`, mutation **and**
  contradiction probes (`--fast` mode for satisfiability, as on jack).
- Wall clock 2026-11-24 18:05 → 23:40 local (PST) = 2026-11-25 02:05 → 07:40Z, **5 h 35 min**.
  Verdict line: `2026-11-24 23:40:30 ALL DONE`.
- Note on the job count: the run generated **1,083 mutants** plus **343 contradiction probes** =
  1,426 jobs. The earlier shorthand "1,426 mutants" was wrong; the mutant figure is 1,083.

## Numbers

| | declarations | mutants | killed | killed-timeout | SURVIVED | unattributed | kill rate |
|---|---|---|---|---|---|---|---|
| john (2026-11-25) | 324 | 1,083 | 1,058 | 9 | **16** | 0 | 97.7% |
| jack, MorleyKernel total (battery + late block) | 318 | 1,060 | 941 | 94 | **16** | 9 | 88.8% |

Contradiction probes: john **0 CONTRADICTORY** over 343 (228 `ok`, 114 no-hypothesis, 1
probe-invalid `subfamily_P0_zero_gen`, 0 timeout) — jack **0 CONTRADICTORY** over 294 (140 `ok`, 125
no-hyp, 22 timeout, 7 unattributed). Same verdict on every declaration both probed.

## Comparison

- **Survivors: identical set.** The sixteen `(declaration, mutation)` pairs match exactly — no
  survivor on either side that the other lacks. This is the reproduction that matters: the survivor
  list is a property of the statements, not of the machine or the load.
- **Declaration coverage:** 318 shared, 6 audited by john only —
  `d7_children_gcircleS'`, `d7_children_gcircleS''`, `hodd_inf'`, `hodd_inf_all'`,
  `hodd_one_P0_line'`, `p0_levelpts_collinear'`. All six are primed names, which jack's collector
  skipped; john's run mutates them and kills every mutant (including the headline `hodd_inf_all'`).
  Jack has no declaration that john lacks.
- **Mutant labels:** 1,060 shared; john produced 23 extra mutations on the shared declarations (the
  newer generator is slightly denser). No jack-only mutation.
- **Kill rates** differ only through timeouts: john's box ran the whole file in 5 h 35 min with 9
  heartbeat timeouts, jack's first battery hit 94 timeouts and 9 unattributed rows during the
  overload event. Decisive kills as a share of decisive outcomes: john 1058/1058, jack 941/941.
- Declarations with no mutant: 19 on john, 25 on jack — the difference is exactly the six primed
  names. Both machines agree that `evenCornerQL_proof`, `EvenCorner_proof` and `cliffordChainS_inf`
  have no mutable conclusion.

## What this does and does not establish

- **Establishes:** the layer-4 mutation result and the layer-5 contradiction result of the paper are
  machine-independent for `MorleyKernel.lean` — same pin, same generator, same 16 survivors, zero
  contradictions on either box.
- **Does not establish:** layers 6 (ablation) and 9 (bridge inventory) were never run on john;
  satisfiability certification is disabled on both (`--fast`); and the 16 survivors remain survivors
  — the receipt reproduces them, it does not explain them (that is §5.1/§5.8 of the draft: 9 caught
  downstream, 3 vacuous, 4 an unused hypothesis).

## Artifacts (this directory)

| file | sha256 |
|---|---|
| `john_receipt_summary.md` | `511f3755…` |
| `john_receipt_results.jsonl` | `6483365e…` |
| `john_receipt_run.log` | `5eb17414…` |
| `jack_battery_results.jsonl` (comparison baseline) | — |

Originals: `john:~/leancheck/out/paperL_john_receipt/`.
