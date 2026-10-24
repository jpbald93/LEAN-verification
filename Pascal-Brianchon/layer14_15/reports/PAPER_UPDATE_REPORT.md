# PAPER UPDATE REPORT — Paper Pascal (Layers 14 + 15)

Paper: `AFM/Pascal/pascal.tex`. Backup made with cp before any edit: `pascal.tex.bak-prel1415`.
Edits were exact-substring python replacements, each asserted to occur exactly once. Script: `<oc>/tmp/paperupd/Pascal/s/edit.py` (E1–E14; the new subsection text is in `s/l14.tex`), plus four small follow-up replacements (E15–E18). All work was done inline, with no subagents.
Inputs read: L14_REPORT.md (final), L15_COMPARE.md (final, 18:52; it was marked IN PROGRESS when this update started, and I waited for it), the comparer's `L15_compare.lean` (to check theorem names), /tmp/blindPascal/CLASSICAL_REPORT.md, classical_statements.txt, /tmp/blindsrc_Pascal/statements_sources.md, BLIND_TRANSCRIPT_AUDIT.md (Pascal rows: PASS). **INTEGRATE_REPORT.md does not exist** for Pascal (see Open items).

## Edits (old -> new)
- E1 preamble: (nothing) -> `% L1415-REPIN: \commit (726da4d = 726da4dbcc…) -> new Layer-14/15 commit; also the NEWCOMMIT token in the Availability paragraph`, placed right above `\newcommand{\commit}`. Macro and hash are unchanged.
- E2 `\date{28 September 2026}` -> `28 September 2026; version 2, 22 October 2026 (adds Section 8.1)`.
- E3 Abstract: (end) -> adds 2 sentences: v2 adds Mathlib-only restatements with non-degenerate witnesses, and a comparison with blind textbook formalisations, which proves (outside the main development) Brianchon for tangent lines in char ≠ 2, the five-point form and the converse.
- E4 Contributions: new last bullet (v2: restatements + witnesses; blind comparison proves all 20 textbook statements, incl. tangent-line Brianchon, the tangent form and Braikenridge–Maclaurin).
- E5 Availability: after "Apache 2.0." -> v2 adds `PascalHexagon/L14.lean` and `PascalHexagon/L15Classical.lean` in a new commit `NEWCOMMIT`; the root import file and gate.sh gain entries; earlier statements and files are unchanged, so line references hold.
- E6 Thm 13 (Brianchon) statement: "…additionally assumes that the first two diagonals are distinct." -> adds "(the Layer-14 restatement drops this assumption, Section 8.1)".
- E7 §6 tangency paragraph: "…only under this standard identification." -> adds: v2 proves Brianchon for six distinct tangent lines of a nondegenerate conic in char ≠ 2 separately (polarity + `pascal'`, Layer-15 file), not using Thm 13; the Gram-matrix description of the dual conic is still not formalised.
- E8 §8 Verification: after "prints PASS (32 theorems…)" -> adds: gate.sh needs GNU tools; `mktemp --suffix` is GNU-only, so with stock macOS BSD tools it stops with `FAIL: axiom report`.
- E9 Limitations/Tangents: "limiting cases … are not formalised. Stating them needs a definition of the tangent line…" -> not part of the main development (no Mathlib tangent); with the writer's tangent definition, the five-point form and the pentagon Brianchon form are proved in the Layer-15 file, for nondegenerate conics only; other limiting cases are not formalised.
- E10 Limitations/Converse: "would follow from the same identity. We have not formalised it." -> "follows from the same identity. It is not part of the main development. The Layer-15 file proves it for six distinct points, no three collinear, which lie on a nondegenerate conic (`cov_Pascal3_a` in namespace `PascalHexagon.Classical`)".
- E11 Limitations/Tangency and dual conic: (end) -> adds: the tangent-line form is proved in the Layer-15 file through the polarity (char ≠ 2), but the correspondence with the dual conic is not.
- E12 New `\subsection{Layers 14 and 15}\label{sec:l1415}` (Sec 8.1, at the end of §8 Verification, after the TODO comment). Contents:
  - files and namespaces;
  - L14: 16 theorems restate 21/22 Table-1 names; `linePair_ne_zero` is not restated (proof aid, about `linePair`; used in the proof of `l14_pappus`); mechanical check found no `PascalHexagon` constant; `l14_pascal`/`l14_pappus` mention no `cross` (bridge `l14b_cross_ne_iff`); `l14_brianchon` drops h₁₂ (bridge `l14b_common_point`); witness table (5 witness theorems); `l14_apply_eq_coeffs` needs no witness; no false or extra-hypothesis restatements; Brianchon tangency in the witness checked only numerically; the §5 necessity example is not formalised; gate 59 = 32 + 27 PASS; tamper 6/6 rejected;
  - L15: provenance (literature with citations, blind writer, audited transcript; writer's own definitions of nondegenerate conic, tangent and polar); 20 statements (12 theorems + 8 obligations); all 20 proved from the library with no added hypotheses and no library change. Classes: Covered 6 (Pascal1_a, Pascal2_b + 4 obligations; the library is strictly more general); Narrower 1 (Brianchon1_a: the library lacks the tangent ↔ dual-conic link; NEW PROOF `cov_Brianchon1_a`); Out of scope, now proved 13 (all NEW PROOFS, listed one per line); writer statement false as written: none.
- E13 Acknowledgements: adds that the L14/L15 files were written by AI agents, and the L15 statements by a model that saw neither the code nor the paper.
- E14 Bibliography: new `\bibitem{Coxeter}` (Coxeter, Projective Geometry, 2nd ed., Springer 1987), cited in 8.1 (source: statements_sources.md).
- E15 8.1: long `PascalHexagon.…` / `PascalHexagon.Classical.…` prefixes -> short names plus one sentence giving the namespaces (matches the paper's Table-1 convention; this removed the overfull boxes). The polarity names were condensed to `cov_Brianchon2_a_`X for X = polarIsLine, tangent, vertex, incidence, diagonal.
- E16 8.1 witness table: column spec `ll` -> `lp{0.62\textwidth}` (overfull fix); last sentence -> "The Layer-15 file reproduces the writer's definitions and statements verbatim."
- E17 8.1: "the rest need characteristic ≠ 2" -> "the others are stated and proved in characteristic ≠ 2" (the comparer verified only that `tangent` does not use hK; polarIsLine is said to use it; the rest are stated with hK).
- E18 Availability wording: "The only other changes…" -> "The root import file and gate.sh gain entries for them."

## Discrepancies fixed
1. **Converse** ("would follow… We have not formalised it", Limitations) is outdated: now proved in L15 (`cov_Pascal3_a`, any characteristic). Fixed in Limitations, Abstract, Contributions and 8.1.
2. **Tangent limiting cases** ("are not formalised", Limitations) is outdated: the five-point form (`cov_Pascal2_a`) and the pentagon Brianchon form (`cov_Brianchon2_b`) are proved, with the writer's tangent definition and for nondegenerate conics only. Qualified.
3. **Brianchon only under the dual-conic identification** (§6, Limitations): still true of Thm 13, but the tangent-line Brianchon is now proved separately (`cov_Brianchon1_a`, char ≠ 2). Added in §6 and Limitations; the L15 "narrower" classification is stated in 8.1.
4. **Brianchon concurrency needs h₁₂** (Thm 13 statement, §6): the L14 restatement shows the hypothesis is unnecessary (L14 FINDING 3). Noted in the theorem statement and in 8.1. The library theorem `brianchon_concurrent` is unchanged, so the sentence "This extra assumption is needed only for the chosen cross-product witness" remains correct.
5. **Gate portability** (L14 FINDING 1, L15 note 4): "it prints PASS (32 theorems…)" holds only with GNU tools. Added a disclosure in §8.
6. **Gate count**: 32 holds at 726da4d; 59 after L14 (L14_REPORT) is stated in 8.1. The final count with L15 is unknown (no INTEGRATE_REPORT) and is not claimed.

Not changed: the Abstract and Intro claims about the main theorem (L15 confirms that Pascal1_a and Pappus are implied by the library with weaker hypotheses); "32 named theorems in about 670 lines" (true of the cited commit); "What is not claimed" (the paper has no such section; Limitations was used instead).

## Pages / compile
- Before: 9 pages (backup compiled in /tmp/pupd_pascal). After: **11 pages**.
- pdflatex twice: rc 0 / rc 0. No undefined references, no LaTeX warnings, 0 overfull boxes (4 mild underfull lines).
- Theorem/section numbering: the sorted label diff against the backup's aux is exactly one added line, `sec:l1415 = 8.1`. All theorem, lemma and table numbers are unchanged.
- PDF copied to `AFM/Pascal/pascal.pdf`.

## Open items
- **No INTEGRATE_REPORT.md for Pascal.** The file names `PascalHexagon/L14.lean` (from L14_REPORT) and `PascalHexagon/L15Classical.lean` and the namespace `PascalHexagon.Classical` follow the task brief's `<Lib>` convention. The comparer's scratch file currently uses namespace `PaperPascalClassical`. Check after integration, and make sure the gate lists all L15 declarations (8.1 says only that the L14 gate gives 59; the final count is not stated).
- Replace `NEWCOMMIT` (Availability) and update `\commit` after the push (see the `% L1415-REPIN` line). The `\src` links keep pointing at 726da4d, which is correct because the old files are byte-identical.
- The writer's char-free `QNondeg` vs. the classical nondegeneracy: the L15 claims "in any characteristic" are relative to the writer's definition, as the paper says.
- The TODO(Josh) hand-check comment in §8 is untouched.
- Brianchon tangency in the L14 witness is numerical only (stated in the paper).
