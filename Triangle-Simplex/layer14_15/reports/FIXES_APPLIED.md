# FIXES_APPLIED — TriSimplex (review REVIEW_astra_L1415.md, gpt-6-astra)

Paper: AFM/TriangleSimplex/trisimplex.tex. Backup: trisimplex.tex.bak-preastrafix (made before any edit).
All edits are exact-substring replacements, each asserted to occur exactly once. No theorem statements, numbering or commit macros were touched. NEWCOMMIT count is 4 before and 4 after.

## Issue 1: signed-distance bridge omits the affine-span restriction. **ACCEPT**
Evidence:
- L15_COMPARE.md:55: "`signedDistLine_face_eq` … equals Mathlib's `Affine.Simplex.signedInfDist` **on the span**, for any simplex."
- scratch/carnot.lean:57–59: `theorem signedDistLine_face_eq {n : ℕ} [NeZero n] (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) {p : P} (hp : p ∈ affineSpan ℝ (Set.range s.points))`. Here `[NeZero n]` means the simplex is positive-dimensional, and `hp` restricts the point to the affine span.

Old (P:1029): `(also in Viviani): the writer's side-of-line signed distance equals \lean{signedInfDist}, for any simplex.`
New: `(also in Viviani): for any positive-dimensional simplex and any point in its affine span, the writer's signed distance to a facet equals \lean{signedInfDist}.`
(This is the reviewer's text. Only the first letter is lower-cased because it follows a colon.)

## Issue 2: crossing diagonals alone do not give the orientation hypotheses. **ACCEPT**
Evidence:
- scratch/japanese.lean:109–112: `lemma quad_signs [Fact (Module.finrank ℝ V = 2)] … (h1 : Sbtw ℝ A X C) (h2 : Sbtw ℝ B X D) (hpos : 0 < o.areaForm (B -ᵥ A) (C -ᵥ A)) : 0 < … (C-A)(D-A) ∧ 0 < … (B-A)(D-A) ∧ 0 < … (C-B)(D-B)`. The lemma is planar, assumes `hpos`, and concludes the other three signs.
- L15_COMPARE.md:38: "crossing diagonals (`IsConvexQuad`) give the four orientation signs (`quad_signs`), after choosing the orientation that makes ABC positive. Degenerate cases (A=B or B=C) are 0 = 0."
- L15_COMPARE.md:39: "`IsConvexQuad` (two `Sbtw`) does not force distinct vertices."

Old (P:1034): `strictly crossing diagonals give the orientation hypotheses of Theorem~\ref{thm:jq}`
New: `in the plane, strictly crossing diagonals together with positive orientation of $ABC$ give the other three orientation hypotheses of Theorem~\ref{thm:jq}`

Old (P:1077–1078): `For quadrilaterals only, the Layer-15 file derives the orientation hypotheses of Theorem~\ref{thm:jq} from strictly crossing diagonals (\lean{Japanese.Classical.quad_signs}).`
New: `For planar quadrilaterals, the Layer-15 lemma \lean{Japanese.Classical.quad_signs} derives the other three orientation hypotheses from strictly crossing diagonals and positive orientation of $ABC$; the full quadrilateral proof chooses this orientation in the non-degenerate case and treats degenerate cases separately.`

## Extra (per brief): transcript-audit claim now cites the archived audit
The reviewer noted that the audit claim was "reported second-hand, not independently re-audited". The brief allows the paper to cite the audit instead of weakening the claim.
Evidence: BLIND_TRANSCRIPT_AUDIT.md:16–17:
- `| tmp-blindTriSimplex-stmtwriter | ba6ea9d32a14 | … | PASS |`
- `| tmp-blindTriSimplex | add7f9966579 | … | PASS* |`

The `*` flag is explained at line 30: "the flagged `head -60` reads the writer's own compiler output". The flag is benign.
Old (P:1016–1017): `Its transcript and self-reported file list were audited.`
New: `Its transcript and self-reported file list were audited (a transcript audit archived with the reports; the writer's run passed).`

## Integration check
Both affected declarations are in the committed REQUIRED lists in INTEGRATE_REPORT.md:
- `Carnot.Classical.signedDistLine_face_eq`: line 45 (and Viviani, line 81)
- `Japanese.Classical.quad_signs`: line 154

No text about integration needed changing.

## Compile
- `pdflatex` run twice: rc=0 and rc=0.
- `grep -c undefined trisimplex.log` = 0.
- Output: **21 pages** (442174 bytes). This is one page more than the 20 pages before the fixes, caused by the longer sentences.
- `grep -c '\PH{' trisimplex.tex` = 0 (none added).
- `diff` against the backup shows only the 4 edited places (lines 1017, 1029, 1034, 1077).
