# Paper K — round-3 review triage (v4 → v5)

Two reviews of v4 (`paperk.tex` `49920863…`, `paperk.pdf` `bf01d137…`, 16 pp), run 2026-11-17 09:17–10:57
EST after Josh asked for "another review with Astra and Opus as there were still major revisions":

- `REVIEW_v4_astra.md` — `gpt-6-astra`, fix-check of its own round-2 findings: **0 open MAJOR**; 14 of 16
  CLOSED, 2 PARTIAL (A11, A12), 3 new MINOR (N1–N3).
- `REVIEW_v4_opus.md` — `claude-opus-5-5`, fresh read: **2 MAJOR + 14 MINOR**; "not depositable as it stands",
  both MAJORs text-only.

All 35 rows are dispositioned below; every accepted change is in v5. Nothing in the Lean development changed.

v5 = `paperk.tex` `a400e66a…`, `paperk.pdf` `7131a78f…`, **17 pp**, 0 errors, 0 undefined refs, 0 `\PH`,
name gate PASS 57 / 18.

## Opus's two MAJORs

### 1. Cited evidence files are not in the published folder — ACCEPTED
Verified: the published `LEAN-verification/PaperK` tree contains no `EXTENSION.md` and no `k0/FORMULA.md`,
and the paper cites internal workspace paths (`AFM/PaperK/...`) that a reader cannot resolve. The record
behind one of the two headline negative results was therefore unreachable. Fix: `EXTENSION.md` published as
`numerics/EXTENSION.md`, `k0/FORMULA.md` as `numerics/FORMULA.md` (the K0 script was already there as
`numerics/k0_formula.py`), and every citation in the paper re-pointed to a path relative to the published
folder (`numerics/...`, `layer13/...`, `layer15/...`, `SCOUT.md`). No claim changed textually; only the
pointers did.

### 2. `§11 "What is new here"` is a first-ness claim the scout does not support — ACCEPTED
The scout searched prior *formalisations*; it did not search the mathematical literature. The equal-power
characterisation is the Laguerre radical centre of the oriented cycles, and the determinant formula is
Cramer's rule for that system. The section is retitled "Our contributions relative to the source", opens
with the Laguerre-radical-centre expectation and the scout's scope, and calls the square configuration "an
observation about the source's hypotheses, checked here among affine cycles" instead of "a mathematical
remark independent of any formalisation".

## Opus's 14 MINOR findings

| # | finding | disposition |
|---|---|---|
| 3 | battery reports 148 theorems while the five files hold fewer; linter scanned a scratch file | **Applied as disclosure, not re-run.** §9 now says the tool reports 148 theorem declarations and scores 127, against 121 `theorem`/`lemma` declarations on a direct count of the five files; that the report does not itemise the extras; that the linter also scanned `scratch/paperK_l14b.lean` (nonzero exit); and that the mutation/satisfiability/ablation figures are the tool's counts over its scan set, not a per-declaration audit of the gate's 73. Re-running the battery was rejected: the run would be a new measurement, not evidence about the deposited one, and could not be quoted without a fresh receipt |
| 4 | the `unnecessarySeqFocus` warning comes from the L15 recompile | applied: provenance and the file's hash added |
| 5 | "four powers agree to 10⁻¹⁵" is not in the cited file | applied: replaced by the K1 report's common value −3.2906, and the 1.3×10⁻¹⁵ agreement with the cofactor vector on 2000 configurations from `numerics/FORMULA.md` |
| 6 | the (1.266,−4.738) instance is unseeded | applied: labelled unseeded, and the structural point plus the L13 record cited instead of relying on the instance |
| 7 | `hsum` is redundant given equal norms; "regular" overstates the general-n family | applied: §7 says the centroid hypothesis is redundant, that the Lean keeps it, and that equidistant centres do not make the simplex regular for `n ≥ 3`; the abstract now says "simplices whose centres are equidistant from the origin" |
| 8 | "neither spanning vector is null" sits inside Theorem 5 but is no Lean theorem | applied: clause moved into the paragraph as a direct computation (`B`-values 1 and −1) |
| 9 | "four intended mutations are false" had witnesses for only two | applied in the v4→v5 tamper edit: two tests fail because a deleted hypothesis is still used, one counterexample and one reason are recorded, the other two are said to be checked by direct computation during review, not by Lean |
| 10 | signature attribution: both negative directions assigned to `(v,w)` | applied: the `r` slot and one direction of the `(v,w)` plane are negative, the other supplies the `(n+1)`-st positive |
| 11 | "every cycle" over-reads Theorem 3 (`v=0` has no power) | applied: "every finite cycle (`v≠0`)", and the normalisation reference now points at the affine chart of §3 |
| 12 | "the first is present in our files" over-reads the cycle condition on `A,A'` | applied: the vocabulary is present (`B_self_eq_zero_iff`), but no theorem uses it on `A,A'` |
| 13 | appendix silently substitutes the renamed theorem | applied: caption says rows 12–13 use the current name and L15 lists `tetra_thm36` |
| 14 | the name gate checks base names, not namespaces | applied: preamble comment says so; `L11_K_ANCHORS.md` records 57 base names / 67 qualified |
| 15 | Mathlib commit not printed | applied: `0df444a3…` from `lake-manifest.json` |
| 16 | `INDEX.md` reviews row is stale | applied: row now covers both rounds and triages |

## Astra's fix-check

- **14 CLOSED** (its v3 findings 1–10, 13–16), verified against v4 wording and the code; its independent
  re-derivations of the plane sign, the cofactor rank, the equilateral counterexample, the `s19_RB` link
  and the square's `B`-values agree with mine.
- **A11 PARTIAL** — "rather than one being stronger" and the present-tense "never introduces $P$" — applied:
  the sentence now says those comparisons need bridges or a change of configuration and that the audit
  establishes no strength ordering; the prose-gap sentence is in the past tense.
- **A12 PARTIAL** — the tamper paragraph still claimed all four witnesses and ended "not merely a compile
  failure" — applied as in Opus 9.
- **N1** (the L13 writer was given the frozen TeX, not pre-sanitised prose) — **accepted and applied**: §9
  now says the writer was instructed not to look at the development, that it stripped the markup itself and
  recorded the prose it used, and that this is source-isolation by instruction, not a pre-sanitised input;
  the draft it read still contained declaration names.
- **N2** (residual Carver sentence in the kit; stale publication state; abstract metadata over-claim) —
  applied: the sentence is gone, the public revision is `f6cf749` (and now v5), and the description now says
  what the name gate actually checks.
- **N3** (appendix equal-power rows scoped to the instances) — applied: both rows now separate "equal power
  for arbitrary affine families" from the equal-radius / tetrahedral instances.

## Not accepted as worded

1. **Opus 3's implied re-run of the battery.** The numbers are the deposited run's; a fresh run would
   measure a different execution and would need its own receipt and re-review. The paper now states the
   tool's counting scope explicitly instead, which is the honest fix for a report that does not itemise its
   scan set.
2. **Opus 6's suggested replacement instance.** Its exact instance `(11/15, 2/3)` vs `(11/8, 5/4)` was not
   re-derived here, so the unseeded instance is retained with its status stated. A verifiable instance is
   worth doing offline, not in the deposit build.
3. **Astra N1's stronger remedy** (rerun the blinding with a pre-sanitised input) — not done; the paper now
   describes the recorded procedure, which is what the evidence supports.

## Result

- v5: **17 pp** (the additions pushed the references onto their own page), pdflatex twice rc=0, 0 errors,
  0 undefined references, 0 live `\PH`, one cosmetic overfull inherited from v3.
- Name gate PASS 57 / 18; all 18 anchors still resolve at the pin.
- Lean pin and every Lean number unchanged (`464a59d`); no code or gate edit.
- Kit refreshed for v5 (PDF/tex, `numerics/EXTENSION.md`, `numerics/FORMULA.md`, `L11_K_ANCHORS.md`,
  `INDEX.md`, `SHA256SUMS`), reviews copied, supporting folder re-pushed.
