# FIXES APPLIED — Paper Pascal (review: REVIEW_astra_L1415.md, gpt-6-astra)

Date: 2026-10-23. All work was done inline, with no subagents.
- Backup: `AFM/Pascal/pascal.tex.bak-preastrafix`, made with cp before any edit.
- Edits: one python script, `<oc>/tmp/fixes/Pascal/s/fix.py`. It makes 9 exact-substring replacements and asserts that each old string occurs exactly once.
- Not touched: theorem statements, numbering, `\commit`/`\src` macros. All NEWCOMMIT tokens are kept (3 occurrences, up from 2: one added in 8.1).

## Issue 1 [MAJOR] Integration and namespace claims unsupported — PARTIAL

**Verification.** The reviewer's evidence was correct when the review was written:
- PAPER_UPDATE_REPORT.md:47: "**No INTEGRATE_REPORT.md for Pascal.** … The comparer's scratch file currently uses namespace `PaperPascalClassical`."

Since then, INTEGRATE_REPORT.md exists. I re-read it, including the "Commit" step, and it supports the paper's file and namespace claims:
- :13 `PascalHexagon/L15Classical.lean | 1596 | fc3f7bca…`
- :16 "The namespace is now `PascalHexagon.Classical` (was `PaperPascalClassical`)."
- :28 "`PascalHexagon.lean`: `import PascalHexagon.L15Classical` added as the last line, after the L14 import."
- :31 "published **32** → L14 **59** → final **147**"
- :38 "Gate (system BSD tools, no `-g`): `PASS (147 theorems, standard axioms only)`"
- :39 "`ALL TAMPERING TESTS REJECTED`, 6/6"
- :69 "Commit: `be35ffaa75a3…`, … branch `master` (ahead of `origin/master` by 1)", local only and not pushed.

**Decision.** I rejected the reviewer's "pending integration" rewrite because the library now matches the paper. The present-tense claims about the `PascalHexagon/L15Classical.lean` file and the `PascalHexagon.Classical` namespace stay. Two caveats remain:
- The commit is local and not pushed, so NEWCOMMIT stays a placeholder.
- The 8.1 statement that the commit adds these files is now backed by INTEGRATE_REPORT.md:68–88.

I also brought the text in line with what INTEGRATE_REPORT.md now says:
- the final gate count;
- the gate.sh portability change (:34);
- the remaining GNU-sed dependency of tamper.sh (:43);
- the one proof edit in `cov_Pascal2_b` (:26);
- the library file's differences from the scratch file (:16–20).

The original §8 sentence saying the gate needs GNU tools refers to commit `\commit` (726da4d), where it is still true, so I left it unchanged.

**Edits (old → new):**
- 1a Availability:
  - old: "…in a new commit, \texttt{NEWCOMMIT}. The root import file and \texttt{gate.sh} gain entries for them. The earlier statements and files are unchanged, so the line references hold there as well."
  - new: "…in a new commit, \texttt{NEWCOMMIT}. In that commit the root import file and \texttt{gate.sh} gain entries for them, and \texttt{gate.sh} also gets a portability fix (Section~\ref{sec:l1415}). The earlier statements and files are unchanged, so the line references hold there as well."
  - evidence: INTEGRATE :28, :31, :34; hashes "unchanged" :49–56.
- 1b 8.1 intro:
  - old: "Both are files of the library, \lean{PascalHexagon/L14.lean} and \lean{PascalHexagon/L15Classical.lean} (namespace \lean{PascalHexagon.Classical}). The earlier files are unchanged; the root import file and \texttt{gate.sh} gain the new entries."
  - new: "Both are files of the library in commit \texttt{NEWCOMMIT}, \lean{PascalHexagon/L14.lean} and \lean{PascalHexagon/L15Classical.lean} (namespace \lean{PascalHexagon.Classical}). The earlier files are unchanged; the root import file and \texttt{gate.sh} gain the new entries. The Layer-15 comparison was first checked as a scratch file and then moved into the library."
  - evidence: L15_COMPARE :12; INTEGRATE :15–16, :75–76.
- 1c Gate count (after "…rejects all six defects."), added:
  - text: "With the Layer-15 file added as well, the gate checks 147 theorems (59 + 88) and passes, and the tampering suite again rejects all six defects. In that commit the GNU-only \texttt{mktemp} call in \texttt{gate.sh} is replaced, so the gate also passes with the BSD tools of stock macOS; \texttt{tests/tamper.sh} still needs GNU \texttt{sed}."
  - evidence: INTEGRATE :22, :31, :34, :38, :39, :43.
  - This also closes PAPER_UPDATE_REPORT open item :47 ("the final count is not stated").
- 1d Covered bullet:
  - old: "(\lean{cov\_Pascal2\_b}, from \lean{pappus}), with"
  - new: "(\lean{cov\_Pascal2\_b}, from \lean{pappus}; the library file inlines the one-line proof of \lean{pappus}, \lean{pascal'} applied to \lean{linePair}, so that the tampering test that replaces \lean{pappus} is still rejected by the axiom check), with"
  - evidence: INTEGRATE :26.
- 1e Verbatim sentence:
  - old: "The Layer-15 file reproduces the writer's definitions and statements verbatim."
  - new: "The Layer-15 file reproduces the writer's definitions and statements verbatim; in the library version only the namespace, the header and the imports differ from the scratch file, and two linter options are removed."
  - evidence: INTEGRATE :16–20; L15_COMPARE :14.
- 1f Audit claim. This is not a review issue; it follows the task instruction to cite the audit rather than weaken the claim.
  - old: "paper, and its transcript was audited."
  - new: "paper, and its transcript was audited (a transcript audit archived with the reports)."
  - evidence: BLIND_TRANSCRIPT_AUDIT.md:24–25: "tmp-blindPascal-stmtwriter … PASS", "tmp-blindPascal … PASS".
- Limitations, line ~596: `PascalHexagon.Classical` kept, per INTEGRATE :16. The reviewer's suggested `PaperPascalClassical` is obsolete.

## Issue 2 [MINOR] Universal witness / restatement coverage overstated — ACCEPT

**Evidence.**
- L14_REPORT.md:37: "`l14_apply_eq_coeffs` | yes | (identity, no hypotheses) | —"
- L14_REPORT.md:52: "21 of the 22 Table-1 names have a Mathlib-only restatement (the 22nd, `linePair_ne_zero`, is a proof aid …)"

**Edits:**
- 2a Contributions:
  - old: "Mathlib-only restatements of the main results, each with an explicit non-degenerate witness, and"
  - new: "Mathlib-only restatements of the main results, with explicit non-degenerate witnesses for statements with hypotheses, and"
- 2b 8.1 Layer-14 paragraph:
  - old: "Each main statement of Table~\ref{tab:thms} is restated"
  - new: "The main statements of Table~\ref{tab:thms}, except the proof aid \lean{linePair\_ne\_zero}, are restated"

The abstract (l.61–62, "restatements with explicit non-degenerate witnesses") is not universal, so I left it as is.

## Issue 3 [MINOR] Converse limitation ambiguous — ACCEPT

**Evidence.**
- L15_COMPARE.md:29: "some c ≠ 0 has Vc = 0. That c gives a form through all six points. The form satisfies `QNondeg`". The conic is constructed, not assumed.
- Paper 8.1, l.566–567, already states it unambiguously.

**Edit:**
- old: "The Layer-15 file proves it for six distinct points with no three collinear, which lie on a nondegenerate conic (\lean{cov\_Pascal3\_a} in namespace \lean{PascalHexagon.Classical}, Section~\ref{sec:l1415})."
- new: "The Layer-15 file proves that six distinct points, no three collinear, whose Pascal points are collinear lie on a nondegenerate conic in the writer's sense (\lean{cov\_Pascal3\_a} in namespace \lean{PascalHexagon.Classical}, Section~\ref{sec:l1415})."
- The namespace is kept per Issue 1, and the reviewer's wording "Layer-15 comparison" is replaced by "Layer-15 file", which is consistent with integration.

## Compile
- `pdflatex` run twice in AFM/Pascal: rc1=0, rc2=0.
- `grep -ci undefined pascal.log` = 0. Overfull boxes: 0.
- Output: **12 pages** (was 11; the added gate/integration sentences push past the page boundary).
- `grep -c '\PH{' pascal.tex` = 0, so none was added.
- NEWCOMMIT tokens: 3 (all original ones kept).
- Diff against the backup: 39 changed lines, all confined to the 9 replacements above.

## Open items
- NEWCOMMIT and `\commit` (`% L1415-REPIN`) should be replaced only after `be35ffa` is pushed. INTEGRATE :68 says it is local only.
- The TODO(Josh) hand-check comment is untouched.

## Round-2 item (applied by orchestrator, 2026-10-23 12:55)
- r2 #1 ACCEPT (evidence INTEGRATE_REPORT.md:26 "One proof edit"): §L15 closing sentence now lists the cov_Pascal2_b inlining. Backup pascal.tex.bak-prer2. Compile rc 0, 0 undefined.
