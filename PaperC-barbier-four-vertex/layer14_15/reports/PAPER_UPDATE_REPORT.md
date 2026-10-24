# Paper C — update for Layers 14 and 15

Date: 2026-10-22. All work was done inline, with no subagents.
- Paper: `AFM/PaperC/paperc.tex`. Backup: `paperc.tex.bak-prel1415`, made with cp before any edit.
- Edits were made by exact-substring Python replacements; each old string was asserted to occur exactly once. Scripts are in `/tmp/pupdC/edit.py`, `edit2.py` and `edit3.py`, plus one inline table fix.
- Inputs read: L14_REPORT.md, L15_COMPARE.md, INTEGRATE_REPORT.md, /tmp/blindC/CLASSICAL_REPORT.md, /tmp/blindC/classical_statements.txt, /tmp/blindsrc_C/statements_sources.md (and the stmt-writer brief/log), plus PaperF §verify for style.

## Edits (old → new)
1. **Pins:** added a comment above `\newcommand{\commitof}`: `% L1415-REPIN: commitof:barbier commitof:fourvertex (...); also the two NEWCOMMIT tokens in Section~\ref{sec:avail}`. No hashes or macros were changed.
2. **Date:** `10 October 2026` → `10 October 2026; version 2, 22 October 2026`.
3. **Abstract:** "Barbier's theorem: a curve of constant width w has perimeter πw" → "Barbier's theorem, in the form: if h has constant width w, the perimeter of γ_h, defined as ∫|γ_h'|, is πw".
4. **Abstract:** added that the classical statements are not proved for arbitrary C² convex curves or arbitrary convex bodies, and that the theorems are about curves given by support functions. Added that an independent comparison with textbook statements confirms the coverage is narrower, and that the Reuleaux area and Kneser's theorem are out of scope.
5. **Abstract:** "no previous complete formal proof of either theorem" → "… of either theorem, even in this restricted form, …".
6. **Introduction:** "gives complete Lean 4 proofs of both, in a common model" → "… of both for curves given by support functions …; the classical statements for arbitrary convex curves and bodies are not proved".
7. **Contribution 1:** "has perimeter πw" → "has perimeter ∫₀^{2π}|γ_h'| = πw".
8. **What is not claimed:** extended. It now says the following are not claimed:
   - classical Barbier for an arbitrary C² convex curve, or for an arbitrary convex body with its boundary perimeter;
   - perimeter = integral of the speed, identified with Mathlib length only for smooth h and for the Reuleaux triangle;
   - Reuleaux: no identification with the intersection of three discs, no interior angles, no area;
   - four-vertex: not for arbitrary C² ovals and not Kneser's theorem.

   It also points to §Layers 14 and 15, where these are classified as narrower.
9. **Availability:**
   - Added: version 2 adds L14/L15 files in a new commit of each repo (`NEWCOMMIT` ×2), with file names and line counts (290/578, 138/727).
   - Added: earlier statements and files are unchanged (by hash); only the root imports and gate lists are extended.
   - Gate counts: "62 …, 48" → "62 and 48 at the version-1 commits; 96 and 66 in version 2".
10. **Thm barbier statement:** "then P(h)=πw" → "then the perimeter P(h)=∫|γ_h'| of the curve γ_h is πw".
11. **Thm barbierpw statement:** the same change as edit 10.
12. **New paragraph after the junk-values paragraph (§3):** the theorems are about curves given by a support function, with perimeter = integral of the speed. The classical form would also need that every curve or body arises this way, which is not proved.
13. **Reuleaux, after Thm 4:** "say the curve really is the Reuleaux triangle" → "identify the curve with the boundary of a Reuleaux triangle". Added that the body is not proved to equal the intersection of three discs, and that the 2π/3 angles and the area are not proved.
14. **Convex-body paragraph:** "this includes the Reuleaux triangle" → "this includes the body of the Reuleaux support function R_w".
15. **New paragraph after Thm fvtextbook:** arbitrary C² ovals are not covered, because ρ need not be differentiable. It is also not proved that every C³ oval comes from a C³ support function.
16. **Verification, Gates paragraph:** added that version-2 gates pass with 96/66 declarations, and that the tamper suites were re-run and rejected every defect (21–22 Oct 2026, arm64).
17. **New subsection `\subsection{Layers 14 and 15}\label{sec:l1415}`** at the end of §Verification, after "Name gate". It contains:
   - **Layer 14:** 13 main results restated (8 barbier + 5 fourvertex), with no library constants (12 + 7 decls checked mechanically). Thm 5.1 is re-exported. The three strengthened restatements are named. There is a witness table (5 witnesses, with non-degeneracy). No restatement was false or needed an extra hypothesis. Helpers, bridges and examples were not restated. The junk-derivative observation is recorded.
   - **Layer 15:** method (literature agent with citations; blind writer of 17 statements, 7 ambiguities, 0 extra hypotheses, 2 obligations; transcript audited; comparer transported via Mathlib's isometry). Counts: covered 3, narrower 9 (each with what is missing), out of scope 5, writer-false 0.
   - The NEW PROOFS list and the open obligation (perimeter_obligation).
   - Files `Barbier/L15Classical.lean` and `FourVertex/L15Classical.lean`, namespaces `Barbier.Classical` and `FourVertex.Classical`, with the writer text kept verbatim.
18. **Limitations, item 1:** added the C²-curve reparametrisation gap and the gap ∂K_h = trace γ_h with polygon perimeter = P(h); the general form is covered only narrowly. **New item:** Reuleaux (discs identification, angles, area, Blaschke–Lebesgue, polygons).
19. **Limitations, four-vertex item:** added "not arbitrary C² ovals of arbitrary period".
20. **Acknowledgements:** "the verification battery" → "the verification battery (including Layers 14 and 15)".
21. **Witness table:** the column spec `{ll}` → `{l>{\raggedright\arraybackslash}p{0.48\textwidth}}` to remove an overfull hbox.

## Discrepancies fixed
- **D1:** The abstract stated Barbier as "a curve of constant width w has perimeter πw", which reads as the general classical theorem. It is now scoped to γ_h with the perimeter as the integral of the speed (edit 3, edit 4).
- **D2:** The introduction said "complete Lean proofs of both" with no scope. It is now scoped (edit 6).
- **D3:** The theorem statements used P(h) without saying it is the integral of the speed of γ_h. That is now explicit (edits 7, 10, 11).
- **D4:** "the curve really is the Reuleaux triangle" overclaimed. L15 found no identification with the three-disc intersection and no corner angles (edit 13). "includes the Reuleaux triangle" is softened the same way (edit 14).
- **D5:** "What is not claimed" and the limitations did not mention the C² curve and C² oval gaps, the ∂K_h perimeter gap, or the Reuleaux angles and area. These are now added (edits 8, 15, 18, 19).
- **D6:** The gate counts 62/48 are outdated for version 2. Both counts are now given (edits 9, 16).
- **D7:** "No previous complete formal proof of either theorem" is now qualified by "even in this restricted form" (edit 5).

## Theorem numbering
The 20 theorem-like environments are unchanged, and none was added or removed. The new subsection is placed after all theorems, so the numbering is unchanged.

## Compile
- `pdflatex` was run twice: rc=0 both times.
- No undefined references or citations, and no "??" in the PDF text. 0 overfull boxes after edit 21.
- **Pages: 11 before → 14 after.**

## Open items
- **Repin:** fill the two `NEWCOMMIT` tokens in §Availability, and update `commitof:barbier` and `commitof:fourvertex` if the `\src` anchors should point to the version-2 commits. The anchors stay valid at the version-1 commits, because the earlier files are byte-identical.
- **Name gate:** `namegate_c.sh` currently FAILS on the 28 new `\decl` names (19 barbier, 9 fourvertex). The cause is that the local mirrors `~/Projects/*-repo` are still at 7baae04/14d1044. Every one of the 28 names appears in the REQUIRED additions listed in L14_REPORT.md or INTEGRATE_REPORT.md. Re-run the gate after the mirrors are updated to the new commits. The pre-existing names and all 57 anchors pass.
- **Unchecked claim:** the "Layer 15 transcript audited" claim follows the user's brief and the writer's self-report (CLASSICAL_REPORT.md, "Files read"). I found no separate audit report file.
- **Writer model not named:** the paper says "a writer model" without naming it, because no input names it.
- **gate.sh header comment:** it still mentions scratch/Ax.lean, which is removed in the new commit (INTEGRATE_REPORT note). This is a repo-side item and was left as is.
- **Rounding:** the line counts in §Availability ("ten files, 2,746 lines"; "six files, 858 lines") describe version 1 and were left as they are. The new files and their line counts are listed separately.
