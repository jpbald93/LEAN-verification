# PAPER UPDATE REPORT — Paper CaseyFuss (Layers 14 + 15)

Paper: `AFM/CaseyFuss/casey_fuss.tex`. Backup: `casey_fuss.tex.bak-prel1415` (cp before any edit).
All edits were made with exact-substring python replacements, each asserted to occur exactly once (script: `<oc>/tmp/paperupd/CaseyFuss/s/edit.py` plus one inline edit, E15). All work was done inline, with no subagents.
Inputs: L14_REPORT.md, L15_COMPARE.md, INTEGRATE_REPORT.md, /tmp/blindCaseyFuss/CLASSICAL_REPORT.md, classical_statements.txt, statements_sources.md, plus the comparer's Lean files (to check theorem names).

## Edits (old -> new)
- E1 preamble: (nothing) -> `% L1415-REPIN: \commitcasey (a83c43b…) and \commitfuss (671efdc…) -> new Layer-14/15 commits; also the NEWCOMMIT tokens under Availability`, placed right above `\newcommand{\commitcasey}`. Macros and hashes are unchanged.
- E2 `\date{30 September 2026}` -> `30 September 2026; version 2, 22 October 2026 (adds Section 7.1)`.
- E3 Intro: "we do not formalise the converse." -> adds "(Section 7.1 shows that a direct formalisation of it without non-degeneracy hypotheses is false)".
- E4 Contributions: new 4th bullet (version 2: Mathlib-only restatements plus witnesses, and the textbook comparison; Fuss, its converse and Poncelet closure are covered only narrowly: convexity and contact on the side segments are not proved).
- E5 Availability: line refs -> notes that the Casey references also hold at the pinned a83c43b (which adds Bridge.lean and leaves Basic/Main unchanged), and adds a version-2 paragraph: new commit (Casey `NEWCOMMIT`, Fuss `NEWCOMMIT`) adding Casey/L14.lean (174), Casey/L15Classical.lean (394), Fuss/L14.lean (354), Fuss/L15Classical.lean (418); only the root imports, gate.sh and README change; earlier statements and files are unchanged.
- E6 Sec 6.1: "we have not formalised this uniqueness statement, but it is elementary" -> "formalised in the Layer-14 file for Mathlib's IsIntTangentAt (`Casey.l14_center_of_isIntTangentAt`)".
- E7 Sec 6.1 non-vacuity: "We have not stated this instance as a Lean theorem." -> the point-circle instance is still not a Lean theorem, but v2 adds a non-degenerate witness `Casey.l14w_casey`.
- E8 Sec 6.2 "What is not claimed": adds that Layer 15 covers the textbook Fuss converse and Poncelet statements only with `Fuss.IsBicentric` in place of a convex quadrilateral with contact on the side segments.
- E9 Verification: after "both print PASS" -> adds that in the v2 commit the gates check 38 (Casey) and 84 (Fuss) declarations and PASS.
- E10 Limitations / Casey converse: adds that the Layer-15 writer's formalisation is false as written (missing non-degeneracy; `Casey.Classical.not_classical_CaseyFuss1_c`).
- E11 Limitations / Casey representation: "the (easy) statement that every internally tangent circle has this form … not formalised … There is no formal non-vacuity instance." -> the Layer-14 file restates Thm 1 with Mathlib spheres and IsIntTangentAt, proves the tangentCentre form, and gives a non-degenerate witness; the external (signed-radius) case of Thm 2 is not restated; the tangentLength-as-segment identification is still not formalised.
- E12 Limitations / Fuss convexity: adds that for the same reason the Layer-15 converse and Poncelet statements are proved only narrowly, and the forward textbook statement needs the extra hypothesis d<R.
- E13 Acknowledgements: adds that the L14/L15 files were written by AI agents, the L15 statements by a writer that saw neither the code nor the paper.
- E14 New `\subsection{Layers 14 and 15}\label{sec:l1415}` (Sec 7.1, at the end of Verification), covering: the files and namespaces `Casey.Classical`/`Fuss.Classical`; gate counts 38/84 and tamper 6/6; Layer 14 (9 results restated; witnesses; Prop 9 not restated because it is already Mathlib-only; the signed-radius Thm 2 not restated, and why; no false or extra-hypothesis findings; the kite's convexity is not proved); Layer 15 (provenance with citations, blind writer, audited transcript, 9 statements = 4 covered / 4 narrower / 1 false as written; one line per narrower case with what is missing; the writer mis-statement with its counterexample; the full NEW PROOF list).
- E15 Abstract: adds 2 sentences: quadrilaterals need not be convex, and convexity / contact on the side segments are not proved, so the textbook converse and Poncelet closure for convex bicentric quadrilaterals are covered only narrowly; v2 adds the restatements, witnesses and comparison.

## Discrepancies fixed
1. Fuss/Poncelet narrowness (known item): the abstract claimed the "converse … Poncelet's porism" with no convexity caveat; it is now stated in the abstract, contributions, Sec 6.2 and Limitations.
2. Casey converse: the writer's version is false as written (writer error). The paper still does not claim the converse, and this is now stated (intro, limitations, 7.1).
3. "Uniqueness of the tangentCentre form not formalised" (Sec 6.1 and Limitations) is outdated: now proved in L14 (`l14_center_of_isIntTangentAt`).
4. "There is no formal non-vacuity instance" (Casey, Limitations) and "We have not stated this instance" are outdated: now `l14w_casey`.
5. "Circles are given by tangentCentre, not as Mathlib spheres" is now qualified: true of the main files, while L14 restates Thm 1 with spheres.
6. Gate counts 18/34 are true only of the old commits; 38/84 for v2 added.
7. Availability: "Line references to 5f6252c" while the pin is a83c43b (flagged by L14/L15) is now clarified (Basic/Main are unchanged, per the hash table).

## Counts used (with sources)
L14: Casey 2 restatements (+1 bridge, 1 witness), Fuss 7 restatements, 4 witness theorems (+ fuss_iff_reciprocal witness); Prop 9 not restated; Thm 2 external case not restated (L14_REPORT). L15: 4 E / 4 N / 1 D (L15_COMPARE). Gates 38/84, tamper 6/6, files and lines (INTEGRATE_REPORT).

## Compile
pdflatex twice: rc 0 / rc 0. No undefined references, no LaTeX warnings, 0 overfull boxes. Pages **15 -> 18**. Theorem/lemma/definition numbering is identical to the backup (aux label diff empty). The new subsection is 7.1.

## Open items
- Replace the two `NEWCOMMIT` tokens and update `\commitcasey`/`\commitfuss` once pushed. The local, unpushed commits are casey 8e90588…, fuss c5a5915… (INTEGRATE_REPORT); if they are pushed unchanged, these are the hashes.
- namecheck.py reports FAIL. That is **pre-existing**: before this update it already failed on 5 Bridge names (`Casey.tangentCentre_mem_line`, etc.), because its local tree `~/Projects/casey` lacks Bridge.lean. The 40 new L14/L15 names also show as MISSING because that tree predates the new files. Every new name was checked by hand against the comparer's Lean files and the L14/INTEGRATE reports. Run namecheck against the v2 checkouts after pinning.
- Theorem-table links (`\src`) still point at the old pinned commits; after repinning they resolve in the new commit (the old files are byte-identical, so the line numbers hold).
- Mathlib name `EuclideanGeometry.Sphere.IsIntTangentAt` was verified in the local pinned-Mathlib tree.
