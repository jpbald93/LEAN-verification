# FIXES APPLIED — Paper CaseyFuss (review REVIEW_astra_L1415.md, gpt-6-astra)

Paper: `AFM/CaseyFuss/casey_fuss.tex`. Backup: `casey_fuss.tex.bak-preastrafix` (cp before any edit).
Edits: exact-substring python replacements, each asserted to occur exactly once (`<oc>/tmp/fixes/CaseyFuss/s/fix.py` plus one inline follow-up for issue 2). All work inline, no subagents.
No theorem statements, theorem numbering, commit macros or NEWCOMMIT tokens were touched (NEWCOMMIT count is still 3, counting the L1415-REPIN comment). No `\PH{` was added: the count is the same before and after.

## Issue 1 — contributions bullet mixes up the forward Fuss gap with the converse/Poncelet gap — **ACCEPT**
Evidence:
- L15_COMPARE.md row `classical_CaseyFuss2_a`: "**N** | `cov_CaseyFuss2_a_part` | (i) extra hypothesis `x < R`; (ii) the clause `x = 0 ↔ ABCD square` … for the writer's convex `BicentricWith`".
- Row `classical_CaseyFuss2_b`: "convexity of the produced quadrilateral and contact points on the sides".
- Row `classical_CaseyFuss3_a`: "`BicentricWith` (convex + contact points on segments) is weakened to `Fuss.IsBicentric`".

So the forward result assumes convexity and does not lack it; its gaps are d<R and the square clause.
Old (T:151–152):
> model (Section~\ref{sec:l1415}). The textbook Fuss theorem and its converse and the Poncelet closure
> statement are covered only in a narrower form: convexity and contact on the side segments are not proved.

New:
> model (Section~\ref{sec:l1415}). The forward textbook Fuss statement is covered with the additional
> hypothesis $d<R$ and without the square-characterisation clause; its converse and the Poncelet statements
> are covered only with side-line tangency, without proofs of convexity or contact on the side segments.

## Issue 2 — "its transcript was audited" has no audit record; collector provenance cannot be traced — **PARTIAL**
The reviewer was right that the reports given to them contain no audit record. But the audit exists:
- `AFM/L14L15/BLIND_TRANSCRIPT_AUDIT.md`, line 19: "| tmp-blindCaseyFuss | `27edb36c119d` | 10 | 0 (own outputs only) | 0 | 0 | — | PASS |" (the blind Lean writer).
- Line 18: "| tmp-blindCaseyFuss-stmtwriter | `5b0b68ee7bc8` | 12 | 0 (own outputs only) | 8 | 0 | — | PASS |" (the statement collector).
- Line 33: "All 21 runs therefore PASS."

Collector provenance: `/tmp/blindsrc_CaseyFuss/statements_sources.md` lists exactly the cited sources with editions and pages. Line 4: Casey 1866 and *Sequel*, 5th ed., p. 103. Line 5: Johnson pp. 121–127. Line 16: Dörrie pp. 188–193. Line 17: Yiu pp. 158–164. Line 23: Poncelet pp. 311–317. Line 24: Bos–Kers–Oort–Raven 1987.

So the claim is not weakened. Instead I cite the archived audit, as the task allows, and name the collector's recorded editions and pages. The reviewer's other point stands: the audit file's notes mention voided runs only for Papers D and E, so I did not invent one here.

Old (T:838):
> code nor this paper, and its transcript was audited. It wrote nine Lean statements, two of them

New:
> code nor this paper, and its transcript was audited (a transcript audit archived with the reports; the
> collector's transcript passed the same audit, and the collector recorded editions and pages for each source). It wrote nine Lean statements, two of them

## Issue 3 — size/file-count claims for the original code are unqualified now that version 2 adds files — **ACCEPT** (as suggested)
Evidence:
- INTEGRATE_REPORT.md:13–14: "Casey/L14.lean | 174", "Casey/L15Classical.lean | 394".
- INTEGRATE_REPORT.md:25–26: "Fuss/L14.lean | 354", "Fuss/L15Classical.lean | 418".
- INTEGRATE_REPORT.md:46: "casey/Casey/Bridge.lean | … | same" (Bridge was already in the pinned commit).

So "the whole library is two files and 200 lines" is no longer true. The new-file counts at T:162–164 are unchanged.
- T:83, old "Both\ndevelopments are short (about 200 and 870 lines)" → new "Both\noriginal core developments are short (about 200 and 870 lines)"
- T:167–168, old "The Casey library consists of … (200 lines, plus a 2-line root file). The Fuss library consists of six" → new "The original Casey core consists of … (200 lines, plus its original 2-line root file). The original Fuss core consists of six"
- T:408, old "The whole library is two files and 200 lines." → new "The original Casey core is two files and 200 lines."

## Compile
- pdflatex run twice: rc=0 / rc=0.
- `grep -c -i undefined casey_fuss.log` = 0, and the log has 0 warnings.
- Output: **18 pages** (unchanged from before the fixes).
- `\PH{` count is unchanged (none added).
