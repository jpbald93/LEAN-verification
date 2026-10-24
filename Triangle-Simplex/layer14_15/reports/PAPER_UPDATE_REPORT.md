# Paper TriSimplex — paper update for Layers 14 and 15

Paper: `AFM/TriangleSimplex/trisimplex.tex`. Backup: `trisimplex.tex.bak-prel1415` (cp before any edit).
Edits: python exact-substring replacements, each asserted to occur exactly once (`<oc>/tmp/paperupd/TriSimplex/edit.py` + two follow-up fixes). All work was inline, with no subagents.
Inputs: L14_REPORT.md, L15_COMPARE.md, INTEGRATE_REPORT.md, /tmp/blindTriSimplex/CLASSICAL_REPORT.md, classical_statements.txt, /tmp/blindsrc_TriSimplex/statements_sources.md, Paper F §verify (style model).

## Edits (old -> new)
1. Preamble, above `\newcommand{\commitcarnot}` -> added `% L1415-REPIN: \commitcarnot \commitviviani \commitdegua \commitjapanese \commitponceletthree (and the short hashes 98e5614, 029aa3d, d46e6b2, 34fd0a9, 9affe62 in Availability; NEWCOMMIT tokens there and in sec:l1415)`. Commit macros and hashes are unchanged.
2. `\date{30 September 2026}` -> same + `\\ Version 2, October 2026: adds Layers 14 and 15 (Section~\ref{sec:l1415})`.
3. Abstract: "pairwise orthogonal, together with the projection form" -> "pairwise orthogonal (with $k$-volume defined by a Gram determinant), together with …" (De Gua overclaim, L15 narrower).
4. Abstract: "(plus about 900 lines of verbatim copies)" -> "…copies; the Layer-14/15 check files added in version 2 have about 2,200 more)". The new files total 2,169 lines (INTEGRATE_REPORT).
5. Contributions: "De Gua in every dimension and in every real inner product space;" -> "…, with volume given by Definition~\ref{def:volsq};" (De Gua overclaim).
6. Availability: appended "Version 2 … adds the Layer-14 and Layer-15 files … in a new commit of each repository: NEWCOMMIT (Carnot), NEWCOMMIT (Viviani), NEWCOMMIT (De Gua), NEWCOMMIT (Japanese), NEWCOMMIT (Poncelet). The earlier statements and library files are unchanged (only the root file gains two import lines, and gate.sh and the README are updated), so the line references above are valid at both commits."
7. §Poncelet, incircle paragraph: "This argument is not a formal output: …only Euler's relation." -> "In the main files this argument is not a formal output: … Version 2 proves it in the Layer-15 file, for I inside Γ: three tangent side lines make ω Mathlib's insphere (`Poncelet3.Classical.insphere_eq_of_isTangent`)."
8. §Correctness (Carnot): "we have not restated it that way." -> "the main files do not, but the Layer-14 file does (`Carnot.l14_carnot`)."
9. Limitations, Carnot item: "…is a two-line corollary that we have not written." -> "Theorem 2 is stated directly with signedInfDist only in the Layer-14 file (`Carnot.l14_carnot`), not in the main files."
10. Limitations, Volumes: appended "The Layer-15 comparison classifies the textbook De Gua statements, written with Lebesgue measure on the hull, as covered only in this narrower Gram-determinant sense."
11. Limitations, Dissections: appended "For this reason the Layer-15 comparison classifies the textbook polygon statement (triangulations as dissections, convexity by side lines) as covered only in the narrower sense."
12. Limitations, Convex position: appended "For quadrilaterals only, the Layer-15 file derives the orientation hypotheses of Theorem 17 from strictly crossing diagonals (`Japanese.Classical.quad_signs`)."
13. Limitations, Poncelet: "The formal outputs assert side-line tangency only. We have not proved, as a theorem, that the resulting triangle has ω as its insphere … not packaged as an Affine.Triangle …" -> "The theorems of the main files assert side-line tangency only. The Layer-15 file proves, for 0<r and d<R−r, the statements with an Affine.Triangle whose vertices lie on Γ and whose Mathlib insphere is ω; that the points of tangency lie on the side segments is not stated separately. Two tangents from every point of Γ, each meeting Γ again, is proved only under d²=R(R−2r) (Lemma 32)."
14. Acknowledgements/AI: added a sentence that the Layer-14/15 material (the classical statements, the writer's Lean statements, the comparison proofs, the restatements) was produced by AI models.
15. §Verification: "…51 (Japanese) and 22 (Poncelet) declarations." -> same + "(at the version-2 commit, 28, 28, 23, 81 and 53; Section 10.1)".
16. New `\subsection{Layers 14 and 15}\label{sec:l1415}` at the end of §Verification (before Limitations). It covers: the file names `<Lib>/L14.lean` and `<Lib>/L15Classical.lean`, NEWCOMMIT, gate counts, unchanged library files and the portable gate (macOS mktemp fix; tamper `wrap` still needs GNU sed). **Layer 14**: 18 numbered results restated with Mathlib-only types, with their bridges, and the witnesses with distinctness facts. It names what was not restated and why: Thm 19 and Props 21/22 (tree/combinatorial model; Thm 23 covers the geometric statement), the §8 correctness lemmas and `carnot_poly` (time box). **Layer 15**: the pipeline (sources from memory with citations, page numbers unchecked; blind writer; transcript audited; comparer), counts 25 = 17 covered / 6 narrower / 2 false as written / 0 out of scope only (the rectangle is also outside scope), the list of NEW PROOFS, the 3 narrower items with what is missing, the 2 writer mis-statements, and namespace `<Lib>.Classical`.
17. Follow-ups: the namespace phrase became `\code{<Lib>.Classical}, i.e. \code{Carnot.Classical}…`, because `\lean{}` is for declarations. "Every declaration in them is listed in gate.sh" -> "Every theorem and lemma…", because the writer's defs are not in REQUIRED (INTEGRATE_REPORT: "all theorems/lemmas in REQUIRED").
Names use the paper's `\lean{}` macro (name-gated). All 26 new `\lean{}` names occur in the REQUIRED lists of L14_REPORT/INTEGRATE_REPORT.

## Discrepancies fixed
- Overclaim: De Gua "in every dimension" in the abstract and contributions did not say the volume is the Gram-determinant definition. L15 classes all 4 De Gua statements as narrower. Fixed (edits 3, 5, 10).
- Japanese n-gon: the abstract, contributions and §6 already say "maximal sets of non-crossing diagonals/chords", so there was no overclaim. Limitations now record the L15 narrower classification (edit 11).
- Outdated: "two-line corollary that we have not written" / "we have not restated it that way" (Carnot with signedInfDist). L14 `l14_carnot` now exists (edits 8, 9).
- Outdated: "have not proved, as a theorem, that … ω is its insphere … not packaged as an Affine.Triangle". L15 proves `insphere_eq_of_isTangent` and the cov_TriSimplex6_* statements with `Affine.Triangle` and `insphere`. Fixed with honest scope: the main files are unchanged, the segment tangency points are not stated, and the two-tangent fact is proved only under Euler (edits 7, 13).
- Outdated: gate declaration counts (edit 15) and the availability text (edit 6).
- The writer mis-statements are reported as writer errors (`not_classical_TriSimplex4_b_obligation`, `not_classical_TriSimplex4_b_rectangle`). They are not paper errors, and no paper claim was affected.
- The macOS gate failure (GNU mktemp) is disclosed, with the portable gate in the new commit (subsection).

## Compile
- pdflatex ×2: rc 0 both times. 0 undefined references/citations, 0 overfull boxes.
- Pages: **17 before -> 20 after**.
- Theorem numbering is unchanged (Def 1 … Lemma 32, checked against the .aux labels). The new subsection is 10.1. No sections were renumbered, since the subsection sits inside §10.
- gate_names.py: 126/152 found. The 26 "MISSING" names are exactly the new L14/L15 names: the gate scans `~/Projects/<repo>` (old commit), which lacks the new files. All 26 were verified against the REQUIRED lists in the reports.

## Open items
- Fill the 5 NEWCOMMIT tokens (Availability + §10.1) and update the macros named in `% L1415-REPIN`. Commits per INTEGRATE_REPORT (local, unpushed): carnot fa8c379…, viviani e71460f…, degua daa8952…, japanese-theorem be4503b…, poncelet-triangles aa9da6c…. Verify after push.
- gate_names.py needs its TREES pointed at the new commits to name-check the 26 new names mechanically.
- Pre-existing, not touched: anchor mismatch for `Affine.Simplex.sum_dist_eq_height` in the combined Table 1 row (Equilateral.lean:62 is `Equilateral.height_eq`; the row lists two names).
- `tests/tamper.sh` `wrap` still needs GNU sed (INTEGRATE_REPORT); disclosed in the paper; port later.
- The literature collector's citations were written from memory and page numbers are unchecked (statements_sources.md); disclosed in the paper.
- The corrected (distinct-vertex) incentre-rectangle statement and the general two-tangent case remain unproved; stated in the paper.
- The date line still reads 30 September 2026, with a Version-2 line; set the exact v2 date at publication.
