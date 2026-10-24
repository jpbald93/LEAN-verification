# PAPER UPDATE REPORT — Paper Conics (Layers 14 and 15)

Paper: `<ws>/AFM/Conics/conics.tex`.
Backup: `conics.tex.bak-prel1415`, made with cp before any edit.
Method: exact-substring replacements in Python. Each old string was asserted to occur exactly once, and all 18 replacements passed. Work was done inline, with no subagents.
Inputs:
- `L14_REPORT.md`, `L15_COMPARE.md`, `INTEGRATE_REPORT.md`
- `/tmp/blindConics/CLASSICAL_REPORT.md`, `classical_statements.txt`
- `/tmp/blindsrc_Conics/statements_sources.md`
- style reference: `PaperF/paperf.tex`

## Edits (old -> new)
- **E1** (pin block): none -> `% L1415-REPIN: \commitD and \commitM (...also replace NEWCOMMIT in the Availability paragraph)`, placed right above `\newcommand{\commitD}`. The macros themselves are unchanged.
- **E2** (`\date`): "30 September 2026" -> the same, plus "Version 2, 22 October 2026: adds the Layer-14 and Layer-15 checks (Section 7.1)".
- **E3** (abstract end): none -> one sentence. It says v2 restates the main theorems with Mathlib-only types and non-degenerate witnesses, and compares them with independently formalised textbook statements; the comparison adds proofs and finds no false statement.
- **E4** (Contributions, bullet 1): "unique within the family of axis spheres" -> the same, plus a parenthesis: in R^3 a Layer-15 lemma extends this to every sphere meeting each generator in exactly one point. Source: L15 `l15_tangent_cone_iff`.
- **E5** (Contributions): none -> a new bullet "(Version 2.) Layer 14 / Layer 15 …, Section 7.1".
- **E6** (Availability): "Line references are to commits a366dcc and bd2cd3c" -> "…205e480 and bd2cd3c". This is the KNOWN ITEM, and the text now matches `\commitD`. Also added:
  - v2 adds `Dandelin/L14.lean`, `Dandelin/L15Classical.lean`, `Marden/L14.lean`, `Marden/L15Classical.lean` in a new commit (Dandelin `NEWCOMMIT`, Marden `NEWCOMMIT`);
  - that commit also adds 2 import lines per root file and updates `gate.sh` and the README;
  - the earlier Lean files and statements are unchanged, so line references stay valid.
- **E7** (Conventions, Cone): "All uniqueness statements … in this paper are about this family; we do not classify arbitrary centres and radii" -> "…in the main files…". Added: the Layer-15 file proves the R^3 classification (`Dandelin.Classical.l15_tangent_cone_iff`).
- **E8** (§4.2 metric tangency): "Both the tangency equivalence and this containment argument are informal … not formalised" -> the tangency equivalence is still informal, but containment in the closed triangle is now proved (`Marden.Classical.l15_marden_steiner`). Also added: "the side line meets the curve only at the midpoint ⇒ (ii)" (`Marden.Classical.l15_strict_of_inter`).
- **E9** (Remark mathlibtangent): "We have not restated them with IsTangentAt" -> "In the main files we have not…; the Layer-14 file restates them with Mathlib spheres, IsTangent and IsTangentAt."
- **E10** (Verification, gate): none -> "In the version-2 commits the gates also list the L14/L15 declarations (158 Dandelin, 56 Marden); both PASS, standard axioms only."
- **E11** (Verification, tamper): none -> "The same holds for the version-2 commits."
- **E12** (new `\subsection{Layers 14 and 15}\label{sec:layers}`, end of §7): Layer 14 and Layer 15 in full; details below.
- **E13** (Limitations, Tangency): "connected to IsTangentAt only in the normalised version" -> "In the main files…; the Layer-14 restatements use IsTangent/IsTangentAt throughout."
- **E14** (Limitations): none -> a new item "Not formalised". It names the Steiner inellipse area (π/(3√3)·area) and its maximality among inscribed ellipses (KNOWN ITEM: now explicitly not claimed), and the planar standard-form converse (Conics3_c).
- **E15** (Acknowledgements): none -> "AI agents carried out the Layer-14 and Layer-15 checks, including collecting the classical statements from the literature, which no human has yet checked against the sources."
- **E16** (§5 Non-vacuity): none -> "In version 2 the Layer-14 witness theorems also prove the hypotheses on explicit configurations in R^3 and C."
- **E17/E18** (layout): `\begingroup\sloppy` … `\par\endgroup` around the new subsection. This removes 4 overfull boxes caused by long `\lean{}` names.

### Content of the new subsection (E12)
- **Layer 14:** 9 main results are restated with Mathlib-only types.
  - 7 Dandelin restatements:
    - `l14_dandelin_ellipse` (Thm 2)
    - `l14_dandelin_hyperbola` (Thm 4 plus the double-cone iff of Thm 8(b))
    - `l14_directrix_ellipse` (Thm 6 plus 8(a))
    - `l14_parabola` (Thm 7 plus 8(a))
    - `l14_regime_R3` (Thm 9(b)–(d))
    - `l14_apex_R3` (Thm 10)
    - `l14_inscribed` (Lemma 19)
  - 2 Marden restatements: `l14_marden` (Thm 11) and `l14_steiner_unique` (Thm 15, strict form).
  - Mathlib types used are listed, and the mechanical namespace check is stated.
  - 6 witness theorems, each with its distinctness facts.
  - Not restated, with reasons: Cor 16 (the conjunction of the two Marden restatements), the weak form of Thm 15, Thm 9(a),(e) and the general-dimension versions, the one-nappe counterexample of Thm 8(b), and internal lemmas (Lemma 20 has the bridge `l14_isTangent_plane_iff`).
  - No restatement was false or needed an extra hypothesis.
- **Layer 15:** the statement collector cited its sources. The writer saw no code and no paper, and its transcript was audited. It wrote 13 statements (12 theorems plus 1 obligation), with 3 ambiguities and no extra hypotheses.
  - Totals: **11 covered, 1 narrower, 1 out of scope, 0 writer statements false as written.**
  - Covered (11): `cov_Conics1_a`, `1_b`, `2_a`, `2_b`, `3_obligation` (proved), `3_a`, `3_b`, `3_parabola_unique`, `4_a`, `5`, `5_double_root`.
  - Narrower: `classical_Conics4_b`. Only the centre clause is proved (`cov_Conics4_b_part`); the area formula and strict max-area clause are missing.
  - Out of scope: `classical_Conics3_c`, the planar standard-form converse. It is not proved; the comparer checked by hand that it is true.
  - Writer mis-statements: none.
  - New proofs (one line each in the paper):
    - `l15_tangent_cone_iff`
    - `l15_gen_segment`
    - `l15_isGreatest`
    - transverse axis in `cov_Conics2_b`
    - `l15_span_circle` / `l15_directrix_eq`
    - `l15_planeAxisAngle`
    - `l15_strict_of_inter`
    - `l15_marden_steiner`
    - `l15_equilateral_iff`
  - Files and namespaces: `Dandelin/L15Classical.lean`, `Marden/L15Classical.lean`; `Dandelin.Classical`, `Marden.Classical`.
  - Gate counts: Dandelin 85 + 17 + 56 = 158; Marden 18 + 6 + 32 = 56. Both PASS, and tamper tests reject every planted defect.
- Declaration names use the paper's existing `\lean{}` macro.

## Discrepancies fixed
1. Availability text said `a366dcc` but `\commitD` = `205e480` -> text now says 205e480 (E6).
2. Steiner inellipse area / maximality: the paper never claimed it. It is now explicitly listed as not formalised (E14) and as missing in Layer 15 (E12).
3. "We do not classify arbitrary [inscribed] spheres" was outdated: L15 proves the R^3 classification. Qualified to "main files", and the new result is cited (E4, E7).
4. "The containment [of the Marden ellipse in the triangle] is … not formalised" was outdated: L15 `l15_marden_steiner` proves it (E8).
5. "We have not restated them with IsTangentAt" (Remark) and the Limitations tangency item were outdated by L14 (E9, E13).
6. Gate counts 85/18 described only the published commits. The v2 counts are added without altering the historical statement (E10).
7. AI disclosure did not cover the L14/L15 agents. Now it does, including the unchecked literature collection (E15).

No claim was invented; each new sentence maps to a line in L14_REPORT, L15_COMPARE, INTEGRATE_REPORT or CLASSICAL_REPORT.

## Compile
- `pdflatex` run twice: rc 0, rc 0. No undefined references or citations, 0 overfull boxes.
- Pages: **before 15, after 19**.
- Theorem, lemma, corollary, remark and section numbers are identical to the backup build (checked by diffing `.aux` label numbers; only page numbers shift). The new subsection is 7.1.

## Open items
- At publication, replace the two `NEWCOMMIT` tokens in Availability: Dandelin local commit `8930918`, Marden `b4fbe75` per INTEGRATE_REPORT. These are not pushed yet, so the hashes may change.
- Update `\commitD`/`\commitM` only if line links should point at the new commits. Per the `% L1415-REPIN` comment, old line numbers stay valid either way, since the earlier files are unchanged.
- The Abstract's line counts ("about 2170 and 760 lines") describe the v1 developments and were left unchanged. If they should include the L14/L15 files, the numbers must be recounted; Dandelin adds 732 + 1555 lines and Marden 213 + 666.
- The owner should decide on keeping `scratch/` and `ax.log` (INTEGRATE note); the paper still cites them.
- A human check of the Layer-15 classical statements against the cited literature is still outstanding (now disclosed).
