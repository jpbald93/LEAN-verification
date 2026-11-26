# Late-block mutation run on jack (2026-11-24 21:28Z → 2026-11-25 03:41Z)

> **Correction notice (2026-11-26, v0.11).** This report describes the four surviving mutants of
> `child_line_of_parent_mid_zero` as mutations of an "unused hypothesis" `u ≠ 0`. That reading was
> wrong: `u ≠ 0` is a conjunct of the existential conclusion, the lemma's hypotheses are inconsistent
> on purpose, and two of the four mutants touch `u ≠ 0` while one flips the finiteness antecedent and
> one the incidence equation. The paper's §5.1/§5.8 and Appendix C carry the corrected account.

Purpose: close the layer-4 mutation gap in `Clifford/MorleyKernel.lean` that john's survivors exposed —
the 2026-11-19 battery mutated only its first 61 declarations (lines 33–806).

## Run

- Script `jack:~/lc_mod/lc_mod_late.py` (same harness as the battery, `WORKERS=4`, `CTIMEOUT=900`,
  contradiction probes skipped, satisfiability job list empty = `--fast` mode).
- Scope: 275 declarations of `Clifford/MorleyKernel.lean` at lines 816 onward; 257 of them took
  mutants. File sha `dce7b011…` (the promoted pin).
- Wall clock 6 h 13 min (restarted once at 22:26Z with WORKERS=4 after the 8-worker version thrashed).
- Verdict line: `2026-11-25 03:41:07 ALL DONE`.

## Counts

| | mutants | killed | killed-timeout | SURVIVED | unattributed |
|---|---|---|---|---|---|
| late block | 891 | 872 | 3 | 16 | 0 |

Coverage after this run: **318 of `MorleyKernel.lean`'s 343 `theorem`/`lemma` declarations** (61 from
the battery + 257 here, disjoint). 25 declarations have no mutant: the generator found nothing to
change in their conclusions (`evenCornerQL_proof`, `EvenCorner_proof`, `cliffordChainS_inf` are of
that kind; so is `hodd_inf_all'`).

Round 19–26 material now mutated: `heven_kernel` (4697), `heven_line_of_P0` (5137),
`evenCorner_of_QL` (5287), `polyF_coeff_top` (5499), `heven_inf_all` (5586).

## The 16 survivors

Nine are caught downstream (own mutant proof compiles, a later declaration then fails):

| declaration | mutation | caught at line |
|---|---|---|
| `ins_eval` | `lit0->1@35` | 1647 |
| `dX_cD` ×5 | `neg1->1@5`, `neg1->1@30`, `lit1->2@6`, `lit5->6@8`, `lit2->3@11` | 2761 |
| `kpe_P0` | `lit5->6@14` (`2*k+5 → 2*k+6`) | 3922 |
| `polyF_natDegree_le` ×2 | `lit2->3@25`, `lit5->6@33` | 5574 |

Seven are caught nowhere:

- `p0_children_gcircleS_false`, `p0_children_gcircleS_genPos`, `hodd_inf_zero` — each `lit2->3@…`
  changing `Fin (2*0+5)` to `Fin (3*0+5)`. At `k = 0` both are `Fin 5`, so the mutant is the **same
  proposition**: a vacuous mutant, not a survivor in any meaningful sense.
- `child_line_of_parent_mid_zero` ×4 — `eq->ne@351`, `ne->eq@18`, `ne->eq@186`, `lit0->1@20`
  (`u ≠ 0 → u ≠ 1`) — all mutations of the hypothesis `u ≠ 0`, none caught anywhere: the hypothesis
  does no work in that lemma. Not a hole; the lemma is auxiliary. Recorded in DRAFT §5.8.

**No survivor is a hole in a headline statement.**

## Artifacts

`summary.md` (harness output), `run.log`, `results.jsonl` (893 rows incl. 2 baseline) — all copied
here, sha256 in `SHA256SUMS`. Original paths on jack:
`~/leancheck/out/paperL_lateblock/`.
