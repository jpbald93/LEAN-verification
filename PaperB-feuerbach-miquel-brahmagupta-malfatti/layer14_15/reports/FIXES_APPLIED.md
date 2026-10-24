# Paper B — fixes applied for REVIEW_astra_L1415.md (2026-10-23)

Backup: `AFM/PaperB/paperb.tex.bak-preastrafix` (taken before any edit). I made 9 exact-substring replacements with python, and asserted that each old string occurred exactly once. No theorem statements, theorem numbering, commit macros or NEWCOMMIT tokens were changed.

## Issue 1 — unsupported audit / source-access claims — PARTIAL
**Evidence.**
- The review relied on PAPER_UPDATE_REPORT:53 ("no separate audit report was found"). That is now out of date. `AFM/L14L15/BLIND_TRANSCRIPT_AUDIT.md` (generated 2026-10-22 18:35) has the row `tmp-blindB-stmtwriter | a6d470cdf6fb | 6 | 0 (own outputs only) | 2 | 0 | — | PASS` and the row `tmp-blindB | 0d450e0b1030 | 12 | 0 (own outputs only) | 0 | 0 | — | PASS`. It closes with "All 21 runs therefore PASS". The writer's pass criterion there is: "no read of any file except its own brief/outputs and its own compiler output; no web access."
- So I kept the audit claim but made it specific, and cited the audit as the user allowed. I did not use the review's "no independent transcript-audit report was available".
- On sources, the review is right, and the statement collector's own log is stronger than the review says. `/tmp/blindsrc_B/stmtwriter/run.log`: "All the statements except the Malfatti radius formula come from memory; I fetched only one source, the Wikipedia "Malfatti circles" page. The page numbers and section references in the sources file are therefore unchecked". The same log ends: "I read only the brief and the Wikipedia page". The text now follows this log rather than the review's "using Wikipedia" wording.
- `/tmp/blindB/CLASSICAL_REPORT.md` "Files read" lists only classical_statements.txt, the directory listing and its own scratch file. It also says "No other files, repositories, notes, or web sources."

**Edits.**
- 1a. Old: "collected textbook statements of the four theorems from the literature (B1--B4, with citations: Feuerbach 1822 and Coxeter--Greitzer \S5.6; Miquel 1838 and Johnson \S184; Brahmagupta and Coxeter--Greitzer \S3.2; Malfatti 1803 and Stevanovi\'c 2003)."
  New: "wrote textbook statements of the four theorems (B1--B4), by its own account from memory apart from one web source, the Wikipedia page on the Malfatti circles. It attached citations (Feuerbach 1822 and Coxeter--Greitzer \S5.6; Miquel 1838 and Johnson \S184; Brahmagupta and Coxeter--Greitzer \S3.2; Malfatti 1803 and Stevanovi\'c 2003), but it did not consult these sources and their section references were not checked."
- 1b. Old: "Its transcript was audited."
  New: "Its tool-call transcript, and that of the statement collector, were audited: neither read the paper or the code, and the writer made no web access (a transcript audit archived with the reports)."
- 1c. Old: "It shared no wording with this paper, but"
  New: "It was not supplied this paper's wording, but" (accepted as the review proposed).
- Unchanged: the description of the 19 statements and four obligations.

## Issue 2 — missing negation in the Miquel row — ACCEPT
**Evidence.** L14_REPORT:67 says "`Dp ≠ 0` replaced by `¬ Collinear ℝ {A,B,C}`". L14_REPORT:91 and :109 say the same.

**Edit.** Old: "$\mathrm{Dp}\ne0$ becomes \mdecl{Collinear}, the parameters"
New: "$\mathrm{Dp}\ne0$ becomes $\neg$\mdecl{Collinear}, the parameters"

## Issue 3 — Feuerbach novelty overstatement — ACCEPT
**Evidence.**
- paperb.tex §"The equilateral case" (around line 373) already says: "For an equilateral triangle $R/2-r=0$, so the incircle and the nine-point circle coincide."
- L15_COMPARE gives only "NEW PROOF" status, under the heading "NEW PROOFS (not in the repositories)". That supports novelty within these libraries, not first-ever status.

**Edit.** Old: "and the two remarks, which the paper does not state and which are proved here for the first time);"
New: "and the two remarks, newly proved in these libraries in version~2; the equilateral coincidence was already described informally in Section~\ref{sec:feuerbach});"

## Issue 4 — area wording — ACCEPT
**Evidence.**
- L14_REPORT:47: "Not expressed as Lebesgue measure of the convex hull (that identification is not in either library ...)".
- L15_COMPARE:36: "its K is the shoelace value, not identified with Lebesgue measure". The identification is carried as the hypothesis `AreaBridge`.

**Edits.**
- 4a (abstract). Old: "(Brahmagupta's area is not Lebesgue measure;"
  New: "(Brahmagupta's shoelace area has not been formally identified with Lebesgue measure;"
- 4b. Old: "The Brahmagupta area is still not Lebesgue measure (Section~\ref{sec:limits})."
  New: "The Brahmagupta shoelace area is still not formally identified with Lebesgue measure (Section~\ref{sec:limits})."

## Issue 5 — version-2 publication status — ACCEPT
**Evidence.**
- INTEGRATE_REPORT "Commit step": "Each copy is on `main`, 1 commit ahead of `origin/main` and 0 behind. **Nothing was pushed.**"
- The re-verification pass agrees: "Each copy is on `main...origin/main [ahead 1]`".

**Edits.**
- 5a. Old: "\emph{Version~2.} Each repository has a new commit ("
  New: "\emph{Version~2.} Each repository has a new local, not-yet-pushed commit ("
- 5b. Old: "given for those commits is unchanged."
  New: "given for those commits is unchanged. The published pins above cover version~1; the new files will become publicly retrievable when the version~2 commits are pushed."
- Unchanged: the NEWCOMMIT tokens and the v1 pins.

## Review side note (not a paper issue)
The review says L15_COMPARE:45 "E 12" should read 13. PAPER_UPDATE_REPORT:41 agrees, and the paper already says 13. I left the paper unchanged. The evidence file was not edited (it is a source of truth, so I did not touch it).

## Compile
- `pdflatex` run twice: rc=0, rc=0.
- 0 lines matching "undefined" in paperb.log.
- Output: "paperb.pdf (26 pages, 605989 bytes)". The page count is unchanged at 26.
- 5 overfull boxes, the same number as before.
- `\PH{` count is the same in the backup and the edited file, so none was added.
- NEWCOMMIT lines: 3 in the backup and 3 after the edits, so the tokens are unchanged.
- The diff touches only the 9 replaced passages (30 changed lines).
