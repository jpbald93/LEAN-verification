# Triage — independent referee pass on draft v0.7 (2026-11-26)

**Input:** `DRAFT.md` v0.7 (1038 lines), frozen copy on jack `~/paperL_review/DRAFT.md`.
**Instrument:** `opencode/big-pickle` (headless `opencode run`, fresh session, draft-only context, one
web lookup of the Bobenko–Schief citation). Full report: `REVIEW_v07_referee_bigpickle.md`.
**Two further instruments** (`opencode/deepseek-v4.1-flash-free`, `opencode/flint-40b-free`) were
launched with the identical brief; both terminated without producing a report (an empty session and a
tool-schema error respectively) and are recorded as failed runs, not as agreement. A third
(`opencode/beam-free`) was launched and is recorded in `layer13/run6/` if it completed.

**Verdict from the instrument:** MAJOR REVISION — 7 MAJOR, 3 MINOR findings.

## Dispositions

| # | sev | finding | disposition |
|---|---|---|---|
| 1 | MAJOR | §1 "first machine-checked treatment" is absolute, with the search gaps three sections away | **APPLIED (scope, not claim).** The claim stays; the sentence now carries its scope — the 26 rows of `SCOUT.md` §0 and the sources §5.10 records as not searched. Rejecting the suggested "first found in the sources searched": the paragraph already states the verdict is the scout's, and the standard phrase is defensible once scoped; the defect was distance, not wording. |
| 2 | MAJOR | §1.1 "The corner is not empty" rests on 1e-8 numerics | **APPLIED.** Now "not vacuous in practice", the search stated as approximate, exact membership explicitly not claimed — and the theorem does not need it. |
| 3 | MAJOR | §5.2 says the certificate assumes the hypotheses, which would make it vacuous (`False ⊢ ∃ x, True`) | **APPLIED — the finding is correct and it was a real defect.** The instrument's goal is `∃ <binders>, True` with each hypothesis a `Prop`-valued *binder* (the curated-table pass failed precisely because it could not inhabit `Transversal c d`), so the certificate exhibits an inhabitant of every hypothesis. The sentence was rewritten to say exactly that. |
| 4 | MAJOR | §5.2 infers non-vacuity from `stmt-invalid = 0` | **APPLIED.** `stmt-invalid = 0` now means only that the statements elaborated; vacuity is claimed from the 397 witnesses, and nothing is claimed for the 180 unresolved. |
| 5 | MAJOR | §5.3 lists S1 among the "definitional" rows while the same item says its hypothesis is strictly weaker | **APPLIED.** Four rows (S4–S7) are definitional; S1 is definitional *plus* a hypothesis-strength gap and is named as the reason it stays open. |
| 6 | MAJOR | §5.11 "Nothing in this appendix was run twice on two machines" contradicts §5.2, §5.3 and §5.5 | **APPLIED.** False as written. §5.11 now names which layers ran on both machines (4, 5, 8, layer 13) and which are jack-only. |
| 7 | MAJOR | §5.11 still describes v0.3 as "this" text and omits the v0.4–v0.7 runs | **APPLIED.** Rewritten as a per-version, per-machine statement; App. B row 11 and App. A's label brought up to date. |
| 8 | MINOR | App. A "`L11_NAMEGATE.md` (regenerated for v0.3)" | **APPLIED.** "regenerated for each draft from v0.4 to v0.8". |
| 9 | MINOR | App. C heading says v0.3 and v0.4 but contains v0.5–v0.7 | **APPLIED.** Heading now v0.3 through v0.8. |
| 10 | MINOR | §1.2 dates Bobenko–Schief "2016" while §1 cites arXiv:1509.04109, and attributes the polytope picture to them | **APPLIED.** Split: the polytope picture is Longuet-Higgins 1972; the cross-ratio/analytic route is Bobenko and Schief, arXiv:1509.04109, published 2016. |

Self-found while triaging, not in the report: §3 still called the tree "a plain directory, not a git
repository" (stale since the pin of 2026-11-25). Corrected to the commit `d15464f` with no remote, and
the sha256 table named as the identity of the audited tree until it is pushed.

**Note accepted as a packaging action, not a draft edit:** `check/allN.lean` must ship in the pinned
upload so a referee can re-run the all-`n` composition. Added to the packaging checklist.

## What the pass did not establish

The instrument had no access to the Lean sources: file:line citations, declaration existence,
compile receipts and hashes were not independently checked by it, and it says so. Those are layer 11's
(citations: PASS 143/98/25/85 on v0.8 after the edits) and the battery's. The pass is a **text**
review; it is not a second-machine reproduction and is not counted as one in §5.11.

## Result

v0.8 differs from v0.7 in nine sentences and three provenance statements, no number, statement,
definition or proof (§ Appendix C, v0.8). `namegate.py` on v0.8 against a fresh dump of the pinned
tree: **PASS — 143 occurrences, 98 distinct pairs, 25 attribution checks, 85 table rows, 0 bare-line
tokens.**
