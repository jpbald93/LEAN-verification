# Paper E — update for Layers 14 and 15 (2026-10-22)

Paper: `AFM/PaperE/papere.tex`. Backup: `papere.tex.bak-prel1415` (cp, made before any edit).
Edit script: `/tmp/pe_scripts/edit.py`. Every edit is an exact-substring replacement, asserted to occur exactly once.

## Inputs used
- `AFM/L14L15/E/INTEGRATE_REPORT.md`: final file names, namespace `<Lib>.Classical`, gate counts 81/104, new commits c3a4ce5 / 4089a97, nothing dropped, no counterexamples.
- `AFM/PaperE/layer14/L14_REPORT_{newton,miquel}.md`: the two files are identical. This is the L14 report; there is no `L14E/L14_REPORT.md`.
- `AFM/PaperE/layer15/PAPERE_L15_COMPARE.md`, `CLASSICAL_REPORT.md`, `classical_statements.txt`, `writer_brief.txt`, `comparer_brief.txt`.
- **Not found:** `/tmp/blindE/*`, `/tmp/blindsrc_E/*`, `L14L15/E/L14_REPORT.md` and `L15_COMPARE.md`. I used the copies in `AFM/PaperE/layer15/` instead. For E there is no sources file, because the orchestrator wrote the statements.
- Checked on jack: the REQUIRED lists in `~/pubE_{newton,miquel}/gate.sh` contain every new `\decl` name I used. The line and file counts of the new trees are 2,328 lines / 8 files (newton) and 3,169 lines / 10 files (miquel), measured with `wc` over the non-.lake `.lean` files.

## Edits (old -> new)
1. Pins comment block: (nothing) -> `% L1415-REPIN: commitof:quadnewton (48e94cf9...) commitof:quadmiquel (011c9ecd...); also the two NEWCOMMIT tokens and the literal hashes in Section Availability (sec:avail)`, placed right above the `\commitof` definitions. No hash or macro was changed.
2. `\date{15 October 2026}` -> `\date{15 October 2026; version~2, 22 October 2026 (adds Section~\ref{sec:l1415})}`.
3. Abstract, before "In the sources we searched": added "Version 2 adds two checks: every main theorem restated with Mathlib-only types and shown non-vacuous on two explicit configurations; all twelve Lean statements written by another model from textbook statements alone were proved from the developments, two of them with new proofs."
4. Abstract: "...orthocentres, as Mathlib affine subspaces." -> "...as Mathlib affine subspaces (whose parallelism allows the two lines to coincide)."
5. Contributions: added a bullet for the version-2 content (Mathlib-only restatements of all 10 Lean statements with 2 witnesses each; 12 writer statements proved).
6. What is not claimed: added "exact radical locus = line is not stated in the main files; it is proved in the Layer-15 file" and "Steiner parallel is in Mathlib's sense (allows coincidence); distinctness not proved".
7. Availability: added a version-2 paragraph. It covers the new commit of each repo (literal `NEWCOMMIT` in two places), the four new file names, two import lines per root file plus the gate lists and README, that earlier files and statements are unchanged (same SHA-256) so source links stay valid, and the new file/line counts. The table still counts version 1.
8. Bodenmiller prose (after Thm 3): "the points of equal power ... form a line, and" -> the same plus "(an elementary fact not stated in the main files; it is proved in the Layer-15 file as `QuadNewton.Classical.radical_eq_line`)".
9. After Thm 8: added "Mathlib's `AffineSubspace.Parallel` includes the case of equal lines; we do not prove that the Simson line differs from the orthocentre line."
10. Limitations: replaced the "Local notions" item ("we did not restate every theorem in Mathlib terms (we did for Thms 3 and 4 ...)") with "the Layer-14 files restate every one of them with Mathlib-only types". Extended the "Coaxality" item to say the exact-line radical locus is proved only in L15. Added a new item "Parallel, not strictly parallel".
11. New `\subsection{Layers 14 and 15}\label{sec:l1415}` at the end of the Verification section, before Limitations. It has two paragraphs:
    - **Layer 14:** all 10 Lean statements of Thms 1–8 restated and proved (all 10 `l14_*` names listed with `\decl`); none left out. Also: the Mathlib-only setting; the `l14_triangles_exist` statements; the restatement of `diag_midpoints_ne` for all three pairs; the namespace-free check of 32 declarations; 20 witnesses (generic and L1⊥L2) with the non-degeneracy proved for each; no Mathlib-only statement false or needing an extra hypothesis.
    - **Layer 15:** the statements E1–E8 were written by the orchestrator, not collected by an agent with citations (disclosed). The writer was of a different model family (GPT-based) and saw no code or paper. It produced 12 statements and 2 construction obligations with 0 errors, marked 2 ambiguities and no extra hypotheses. Disclosed: it read one generic procedure file with no content of this paper. The comparer was an Opus model, worked from verbatim copies, and proved both obligations. Counts: 10 covered outright, 2 narrower in the library but fully proved with NEW PROOFS, 0 different, 0 out of scope, 0 writer statements false.
      - NEW PROOF E3(b) `cov_E3_b`: missing from the library was that the equal-power locus is exactly a line. Proved via the new lemma `radical_eq_line`.
      - NEW PROOF E7(b) `cov_E7_b`: missing was feet not all equal for arbitrary M (library: only M = Miquel point, `cov_E7_b_part` ← `simson_feet_ne`).
      - Ambiguities: E5's ∃! is also proved (`cov_E5_a_unique`). E8: only Mathlib parallelism is proved; strict parallelism is not.
      - It also lists the other covered `cov_*` theorems, the file names and namespaces `QuadNewton.Classical` / `QuadMiquel.Classical`, gates 81/104 with standard axioms only, tamper suites rejecting every defect, and earlier files unchanged.

## Discrepancies fixed
- **Limitations, "Local notions"**: said not every theorem was restated in Mathlib terms. That is now outdated (L14 restates all 10). Fixed (edit 10).
- **Bodenmiller prose**: treated "equal-power points of two circles with distinct centres form a line" as if it were given. The library never states it (L15 E3_b was N). Fixed: now says it is proved only in L15 (edits 6, 8, 10).
- **Steiner parallel (abstract, Thm 8 prose, not-claimed, limitations)**: the paper did not say that Mathlib `Parallel` allows coincident lines, and strict parallelism is not proved (L15 E8). Caveats added (edits 4, 6, 9, 10).
- **Verification gate counts (35/62)**: correct for version 1. The new subsection says they refer to the first-version files and gives the new counts 81/104. The original paragraph was left unchanged.
- **Availability**: now names the version-2 commit (NEWCOMMIT) and the new files, and says earlier files and statements are unchanged (edit 7).
- No overclaim was found about E5 (the paper already proves uniqueness) or E7 (the paper claims distinct feet only for M).

## Compile
- Before: 10 pages (pdflatex ×2 on the backup, rc 0).
- After: pdflatex ×2, rc 0 / rc 0. 0 undefined references or citations. **12 pages.**
- One overfull hbox (5.1pt, Table 1). It was already present before the edit.
- Theorem numbering unchanged (thm:newton..thm:par = 1..8 in both .aux files).

## Open items
1. At publication, replace both `NEWCOMMIT` tokens. Presumably they become quadnewton c3a4ce513eb8789f5f0de4ae02efe707a718466c and quadmiquel 4089a974d5f56663be3daa5203ec856c28b793c3, if these are the commits actually pushed; they have not been pushed yet. Decide whether to repin `\commitof` (see the `% L1415-REPIN` comment). The old source links stay valid either way, because the earlier files are unchanged.
2. `namegate_e.sh` checks `~/quadnewton` / `~/quadmiquel` and john's `~/lean/...`, which still hold the version-1 REQUIRED lists. The new `\decl{...l14_*}` and `\decl{...Classical.*}` names are only in `~/pubE_*` on jack. Re-run the name gate after the new commits are deployed or pushed, and refresh the `src/` mirror.
3. Writer transcript audit: the paper does not claim one. The only source for the writer's file access is its self-report in CLASSICAL_REPORT.md. If an audit is done, add a sentence.
4. The statements E1–E8 have no per-item page citations. This is disclosed in the paper; the paper's existing references (Johnson, Coolidge, Steiner) cover them only in general.
5. The Verification paragraphs on the battery, contradiction probe and Layers 1–8 refer to the version-1 files; there was no battery run on the version-2 files. This is stated in the subsection ("refer to the first-version files").
6. The Availability table and the "14 files and 2,980 lines" figure are version 1. The version-2 counts are given in the text (my `wc` measurement on jack).
