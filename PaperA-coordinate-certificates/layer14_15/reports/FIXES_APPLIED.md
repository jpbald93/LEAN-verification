# Paper A — fixes applied for REVIEW_astra_L1415.md

Date: 2026-10-23. Paper: `AFM/CoordCertificates/paper.tex`. Backup: `paper.tex.bak-preastrafix` (byte-identical copy, taken before any edit).
Edits: python exact-substring replacement, each old string asserted to occur exactly once (`<oc>/tmp/fixes/A/scripts/apply.py`, `apply2.py`).
Theorem environments, theorem numbering, the `\commit*`/`\urlcommit*` macros and the NEWCOMMIT tokens are unchanged. Checks: the theorem blocks diff empty, the macro definitions diff empty, and NEWCOMMIT occurs 7 times in both files.

## Issue 1 (MAJOR) — Napoleon degenerate cases vs. "restated, no extra hypothesis": **ACCEPT**
Evidence:
- paper Thm napoleon: "For all $A,B,C\in\CC$, the centres $G_a,G_b,G_c$ … satisfy $|G_aG_b|=|G_bG_c|=|G_cG_a|$". There are no hypotheses.
- L14_REPORT.md:380-382 (printed type of `l14_napoleon_outer`): "`… ∧ AffineSubspace.SOppSide line[ℝ, B, C] Xa A →`". The inner form uses `SSameSide`. A strict side needs A off line BC, so collinear or coincident vertices are excluded. The overstatement is in L14_REPORT.md:86-88: "All six main theorems restate with exactly the paper's hypotheses". The printed types, not that summary line, are the controlling evidence.
- The reviewer's suggested text was applied verbatim. The summaries were qualified the same way. The Layer-15 "none narrower" classification (L15_COMPARE.md: "N: none.") was left unchanged and stays separate.

Edits:
1. Abstract/intro (l.114): `Version~2 adds to each library a file restating the main theorems with\nMathlib-only types, each with a non-degenerate witness,` → `Version~2 adds to each library a file giving Mathlib-only formulations of the main theorems\n(for Napoleon's theorem, of its non-degenerate configurations), each with a non-degenerate witness,`
2. Contributions (l.179): `Mathlib-only restatements of the six numbered theorems, each with a\nnon-degenerate witness,` → `Mathlib-only formulations of the six numbered theorems (for Napoleon, of the\nnon-degenerate configurations), each with a non-degenerate witness,`
3. §Layer 14 opening (l.1111): `Each of the six numbered theorems is\nrestated in \path{L14.lean} with Mathlib-only types and proved from the library theorem through\nbridges.` → `Each of the six numbered theorems has a\nMathlib-only formulation in \path{L14.lean}, proved from the library theorem through bridges; for\nNapoleon it covers only non-degenerate configurations (see below).`
4. (l.1142): `All six theorems were restated; none turned out false or needed an extra hypothesis.` → `Layer~14 gives Mathlib-only formulations associated with all six numbered theorems. For Napoleon, the strict-side formulation covers non-degenerate geometric configurations in either orientation; it is not a restatement of the degenerate cases allowed by Theorem~\ref{thm:napoleon}, which remain covered by the original rotation-based statements.`

## Issue 2 (MAJOR) — external-centre existence/uniqueness omits unequal radii / distinct centres: **ACCEPT**
Evidence: L15_scratch/L15_compare_monge.lean:25-27: "`def classical_A2_obligation_ext : Prop := ∀ (s t : Sphere Plane) (_hs : 0 < s.radius) (_ht : 0 < t.radius) (_hc : s.center ≠ t.center) (_hr : s.radius ≠ t.radius), ∃! E : Plane, IsExtSimCenter s t E`". `_int` (l.30-33) has `_hc` and no `_hr`. `classical_A2_a` has `_hr₁₂ _hr₂₃ _hr₁₃`. (L15_COMPARE.md says the centre-distinctness hypotheses are unused *in A2(a)*. That is about the collinearity theorem, not the obligation, so the obligation still has to be stated with them.)

Edits:
1. §Monge Scope (l.506): `for circles with positive radii given as\nMathlib spheres, a point … exists and is unique (…obligation_ext}), it is the point\n\decl{Monge.ext} (…ext_eq_of_isExt}), and the three such points are\n\mdecl{Collinear} (…cov_A2_a}).` → `for two circles with distinct centres and positive\nunequal radii given as Mathlib spheres, a point … exists and is unique (…obligation_ext}), it is\nthe point \decl{Monge.ext} (…ext_eq_of_isExt}), and for three circles with\npairwise distinct radii the three such points are \mdecl{Collinear}\n(…cov_A2_a}).`
2. New-proofs list (l.1176): `existence and uniqueness of the external and internal centres of similitude of two circles.` → `existence and uniqueness for two circles with positive radii and distinct centres, with unequal\nradii additionally required for the external centre.`
3. Limitations (l.1201): `for\ncircles with positive radii given as Mathlib spheres, that the homothety maps one circle onto the\nother at a unique external centre and that the three external centres are collinear` → `for\ncircles with distinct centres and positive unequal radii given as Mathlib spheres, that the\nhomothety maps one circle onto the other at a unique external centre and, for three circles with\npairwise distinct radii, that the three external centres are collinear`. The following sentence ("All equal-radius cases are excluded …") was kept.

## Issue 3 (MINOR) — "by exactly this instantiation" vs. r₃ ↦ −r₃: **ACCEPT**
Evidence: the paper prose says "replacing $r_2$ by $-r_2$ turns $S_{12}$ and $S_{23}$ into the internal centres". L15_COMPARE.md (A2_b row): "Proved here as `Monge.monge … s₁.radius s₂.radius (-s₃.radius)`". L15_scratch/L15_compare_monge.lean:177,181 instantiate `(b := -s₃.radius)` and `(a := -s₃.radius)` for I₂₃ and I₁₃. The statement (l.54-56) is `E₁₂, I₂₃, I₁₃`.
Edit (l.491): `by exactly this instantiation, as` → `by the same sign-change argument, using $r_3\mapsto-r_3$ to obtain $E_{12},I_{23},I_{13}$, as`.
(The new-proofs bullet "the instantiation $r\mapsto-r$ in prose" is generic and still accurate, so it was left alone.)

## Issue 4 (MINOR) — "checked by the Lean kernel" scope in Acknowledgements: **ACCEPT** (wording merged to avoid a duplicated phrase)
Evidence: L15_COMPARE.md:3: "blind writer file … (namespace `PaperAClassical`, 14 sorried declarations)". The same file, A4_obligation row: "**D** — false as written … Writer error: `U ≠ V` is omitted". The kernel checks proof terms, not source fidelity or classifications.
Edit (l.1238): `…the collection of the\nclassical statements, their Lean formulation and the comparisons were produced by AI agents; they\nare checked by the Lean kernel but are not part of the author's hand check.` → `…the collection of the\nclassical statements, their Lean formulation and the comparisons were carried out by AI agents and\nare not part of the author's hand check. The resulting\nformal proofs and counterexample are checked by the Lean kernel; fidelity to the textbook sources\nand the comparison classifications require separate semantic review.`
(The reviewer's text repeated "carried out by AI agents" right after "produced by AI agents". The two sentences were merged. The content is unchanged.)

## Additional edit (authorised in the brief) — transcript-audit citation
The reviewer noted "This review did not independently audit the writer transcript." Evidence: BLIND_TRANSCRIPT_AUDIT.md row "`| tmp-blindA | 2a9989b4c627 | 10 | 0 (own outputs only) | 0 | 0 | — | PASS |`" (and `tmp-blindA-stmtwriter … PASS`). Its pass criterion: "no read of any file except its own brief/outputs and its own compiler output; no web access."
Edit (l.1157): `Its transcript was audited.` → `Its transcript was audited: a transcript audit archived with the reports found no file read\nbeyond its own brief and outputs and no web access.`

## Integration / NEWCOMMIT check
INTEGRATE_REPORT.md "Commit step" (re-read): local commits exist (desargues 086ca71, monge 82dd27d, simson e3d2c46, napoleon 0829a14, lami e692d1a) — "Nothing was pushed." The paper text does not claim the commits are absent or published. It only describes the content of the version-2 commit, and that matches the Commit step's staged files: root file, L14.lean, L15Classical.lean, README.md, gate.sh, scratch deletions. Gate counts 34/15/21/45/23 and tamper "ALL TAMPERING TESTS REJECTED" also match. No text change was needed. The NEWCOMMIT tokens stay until the commits are pushed.

## Compile
- `pdflatex -interaction=nonstopmode paper.tex` ×2: rc=0, rc=0.
- `grep -c undefined paper.log` = 0.
- Pages: **26** (`Output written on paper.pdf (26 pages, 516567 bytes)`). The backup gives 25 pages when compiled the same way, so the added qualifications take one more page.
- `grep -c '\PH{'`: paper.tex 0, backup 0, so none was added.
- One existing warning is unchanged: "Float too large for page by 144.02682pt" (the backup has the same warning).
- Diff vs backup: 49 changed lines, all in the passages listed above.
