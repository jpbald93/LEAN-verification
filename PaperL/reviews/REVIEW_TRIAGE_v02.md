> **Status 2026-11-24:** all nineteen rows below are applied in `DRAFT.md` **v0.3**. Per-row
> dispositions, with where each fix landed and the two new check files, are in `REVIEW_TRIAGE_v03.md`.

# Paper L draft v0.2 — independent review round (2026-11-24)

Three independent reviews of the frozen v0.2 draft (`DRAFT.md`, 40,441 B, 11:31 EST) plus the
evidence packet (L11 name gate, L12 review+triage, L13 report and comparisons, L14 restatements,
L15 prior art, ANCHORS, REPORT_L10, jack battery) and read access to `jack:~/paperL_jack`.

| reviewer | model | verdict | findings |
|---|---|---|---|
| Astra | `gpt-6-astra` | MAJOR REVISION | 5 MAJOR / 9 MINOR / 0 NOTE |
| Argon | `gemini-4-argon` | MINOR REVISION | 0 MAJOR / 5 MINOR / 2 NOTE |
| Opus 5.5 | `claude-opus-5-5` | MAJOR REVISION | 3 MAJOR / 10 MINOR / 11 NOTE |

Files: `REVIEW_gpt-6-astra_v02.md`, `REVIEW_gemini-4-argon_v02.md`, `REVIEW_claude-opus-5-5_v02.md`.
All three agree the Lean mathematics is sound; every major finding is about what the paper says
about its evidence.

## Triage (merged; my own check recorded)

| # | finding | raised by | sev | check | disposition |
|---|---|---|---|---|---|
| 1 | `UniqEven` is not merely open — it is FALSE under the current definitions. The draft presents it as the missing theorem that would make the prose and the code equivalent. | Astra R-01 | MAJOR | **Verified**: re-ran the Lean counterexample on jack (`c = 2t−2it²`, t=1..6): both `ChainS 6 c {4i}` and `{∞}` hold, `not_UniqEven` compiles rc=0, axioms std (27.6 s). | Rewrite §2.4/§5.1: uniqueness fails. The two readings are not equivalent — the named-point form is stronger. Do not present `UniqEven` as a possible theorem. |
| 2 | The layer-13 comparison did not preserve the blind writer's types: the writer wrote `∃p ∧ ∀p` (existence + universal incidence), the comparison used `∃p`; "structure untouched" and "strictly stronger" as a comparison result are unsupported. The draft also says the prose read "a point" where the blind text says "the point". | Astra R-02, Argon R-03, Opus R-05 | MAJOR (Astra) | **Verified** in `reformal/PaperLBlind.lean` (`blind_2`, `blind_3`) vs `scratch/BlindCompare.lean`; `DRAFT_blind.txt:43` says "the point". | Rewrite §5.1 and correct `L13_REPORT.md`; state what was actually compared and that only 3 normalized rows were checked. |
| 3 | Layer 8 is described as having no certification candidates; in fact `--fast` replaces the satisfiability job list with `sat = []`, layer 8b links hand-written witnesses, and layer 5's `ok` is failed proof search, not an unsatisfiability certificate. | Astra R-03 | MAJOR | **Verified** in `leancheck/mkmod.py:12`, `lc_mod/lc_mod.py:851`; no `sat` rows in `results.jsonl`. | Correct §4/§5.1: layer 8 disabled, layer 8b unrecorded, layer 5's meaning. |
| 4 | Battery coverage is much narrower than "at every declaration": mutation/contradiction covered 61/60 of `MorleyKernel.lean`'s 343 declarations, all before line 807; no round 19–26 or headline theorem was mutated or probed. | Astra R-04, Opus R-01 | MAJOR | **Verified**: 577 theorem declarations in the 8 audited files vs 294 contradiction rows; 294−234=60 in MorleyKernel; Opus's 61/60 count and line range match. | Disclose the coverage limit in §5 and the §4/App. B rows, or rerun on the later declarations. |
| 5 | Second-machine and numerical receipts are unverified: john's build/gate/tamper/axioms and 74 s/67 s timings, the john snapshot and six ssh attempts, `notes/math-papers.md`, and `RANK_ROUTE_COUNTEREXAMPLE.json` are not in the package. | Astra R-05/R-14, Argon R-04, Opus R-10 | MAJOR (Astra) | Partly verified: the notes exist in the author's workspace and record "58 s jack / 67 s john"; the JSON is absent from jack; john is unreachable. Grandchild coincidence in the exact corner is proved (`evenCorner_of_QL`). | Supply the notes and JSON, or label these as external/unverified. Say grandchildren coincide in the corner, not merely collinear. |
| 6 | The name-gate claim is overstated: the gate counts 66 citations but the draft has ~67 distinct/71 occurrence-level `file:line` cites; `ChainS`, `CliffordChainS`, `lineS`, `IsGCircleS` are not anchored; `Mobius.lean:651`, `:119,152` and seven bare "line N" cites are missed. The gate checks names, not signatures, so L12-05 is not closed. | Astra R-09, Argon R-01, Opus R-02 | MINOR (Astra/Argon) / MAJOR (Opus) | **Verified**: 71 occurrences; 2 name-gate rows mention those names (not the definitions). | Fix the §3 claim, add the missing anchors/signatures, re-run `namegate.py`, and mark L12-05 partly closed. |
| 7 | Six identifiers (`GenTriple`, `second`, `EptInf`, `KP`, `crossVec`, `levelPointN`) are used but never defined for a referee; the roles of `h4_pt_inf` and `cliffordChainS_all_of` are missing, and `GenTriple` has two conjuncts (also excludes a level-3 line). | Astra R-06, Argon R-02, Opus R-11 | MINOR | Verified against source. | Add the definitions and the induction bridge to §2; state the second conjunct. |
| 8 | §1.2 says Paper D "proves C₄, C₅, C₆ in the finite plane", but §2.2 of this paper proves finite-plane C₆ false; Paper D's n=6 result carries an extra non-degeneracy premise. | Astra R-08, Opus R-03 | MAJOR (Opus) | **Verified** against §2.2 and the Paper D record. | Qualify C₆, drop "reused as base cases" above n=5, and name the theorem for n≥6 failure. |
| 9 | No declaration in the tree states `∀ n, CliffordChainS n`; the headline is n≥3, and the base cases come from `cliffordChainS_of_le_five` (not `chainS_of_chain_pt`). | Argon R-05, Opus R-04 | MINOR | **Verified** at `Mobius.lean:178`; the composition is proved in `scratch/allN.lean` (rc 0, std axioms). | Add a named all-n corollary or state the composition, and make §1.1/§2.5 agree. |
| 10 | Carver is cited as §6/Theorem 13 for the key-matrix criterion; the criterion is §5, pp.160–161, and §6 treats limiting figures including a point-circle at infinity that `IsGCircleS` excludes. | Astra R-07 | MINOR | Not independently checked (OCR read by reviewer). | Correct the citation and scope "exactly the reading Carver gives". |
| 11 | Layer 9's 24/113/75 is a heuristic inventory flag, not a semantic Mathlib bridge count; the "has-bridge" list includes internal lemmas (`IsGCircleS.infty_mem`, `chainS_six_iff`) and misses `GenTriple`. §5.2 does not actually mention `IsGCircleS`. | Astra R-10, Opus R-09 | MINOR | **Verified** in `inventory.md` and §5.2. | Relabel as heuristic; fix the §5.2 cross-reference. |
| 12 | The surviving mutant `cliffordChain_one` is a level change (`CliffordChain 1` → `2`) proved by the same term, not a weaker statement; `cliffordChain_iff` needs the n=1 instance. | Astra R-11, Opus R-08 | MINOR | **Verified** (`lit1->2@15`). | Reword the survivor explanation; drop "weaker"/"not counted". |
| 13 | Macro inlining: 13 use sites, not 15 (15 identifier occurrences include 2 definitions); the "prefix" edits are module comments, not docstrings. | Astra R-12, Argon R-07, Opus R-07 | MINOR | **Verified** (`fin_idx` 9 + `fin_idxO` 6 occurrences, 2 definitions). | Fix the count and wording. |
| 14 | "No layer in this appendix was run twice" is false (name gate and blind writer were rerun), and layer 12 reviewed v0.1, not v0.2. | Astra R-13, Opus R-13 | MINOR | Verified from our own records. | Remove the blanket assertion; give each layer's input version. |
| 15 | §2.5's definite article ("**the** point", "**all** n circles") implies unique lower-level objects; `ChainS` is existential at every level and odd-level circles are not unique in the `children_eq_of_P3_zero` branch. | Opus R-06 | MINOR | Verified against `ChainS`. | Rephrase with "some level-(n−1) object of the i-deleted family". |
| 16 | Artifact paths `layer13/…` cited in App. B do not exist on jack; comparisons are in `~/paperL_jack/scratch/` and blind files in `~/reformal/`. | Argon R-03, Opus R-12 | MINOR | **Verified** on jack. | Fix the paths or create the directory before publication. |
| 17 | `EvenCornerQL` itself does not use the grandchild-finiteness hypothesis; layer 6 could not ablate it because the hypotheses sit in a `Prop` definition. | Argon R-06 | NOTE | Accept (`REPORT.md` records the unused `_hall`). | Note it in §2.4/§5.5. |
| 18 | Toolchain and manifest are not recorded (`leanprover/lean4:v4.33.1`, Mathlib pin `0df444a3…`). | Argon R-07 | NOTE | **Verified**. | Record in §3. |
| 19 | Receipt/wording notes: `TAMPER_RC=0` and "--fast skipped" are not in the cited log; 6 linter failures are 3 stale copies + 3 broken fragments; the log is cut at line 17 only for the mutation/contradiction child; scratch-leg figure is from `REPORT_L10.md`, not the battery report; 95 timeouts are not decisive kills; the bridge file post-dates the battery; corner wording; promoted-file line numbers are not byte-identical to scratch; `SCOUT.md` §3 item 18 is §0 row 18; Clifford 1870 vs 1871/1882; "level-5 objects forced to be lines" is explanation, not a theorem. | Opus R-14–R-24 | NOTE | Spot-checked: log continues to line 60; 95 timeout rows exist; bridge dated 21:18Z. | Apply as wording/citation corrections. |

## Verified locally (not just reported)

- `ReviewCheck.not_UniqEven` compiles on jack at the pinned tree, rc=0, 27.6 s, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- 577 theorem declarations across the eight audited files vs 294 contradiction rows; 60 of `MorleyKernel.lean`'s 343 are probed.
- `sat = []` in the `--fast` harness; no satisfiability rows in the battery.
- The blind writer's `blind_2`/`blind_3` are universal-incidence; the comparison's are existential.
- 66 name-gate citations vs 71 file:line occurrences in the draft.
- 13 macro invocations, not 15.
- `cliffordChainS_of_le_five` (`Mobius.lean:178`) is the n≤5 base-case theorem.

## Next step

If Josh wants v0.3: fix items 1–9 first (they change what the paper claims about equivalence,
coverage and Paper D), then 10–19 (citations, counts, paths, wording), rerun `namegate.py`, and
refresh the packet. No Lean proof change is implied by any finding: the defects are in the paper's
statements about the formalisation and its evidence.
