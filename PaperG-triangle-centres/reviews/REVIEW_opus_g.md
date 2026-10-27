VERDICT: MINOR. BLOCKER 0 / MAJOR 0 / MINOR 10

Independent referee review of Paper G (`paperg.tex`, 909 lines; PDF 17 pp.), against the public repos cloned into
<clone dir> at `paperg_nagel@e40ee54f…` and `paperg_brocard@ebb35755…` (both verified as the checked-out HEAD, one
commit each). Line numbers below refer to the current paperg.tex. Nothing was edited apart from this file.

## Findings

1. MINOR (lines 19–22, 125, 705, 737). The theorems and definitions share one counter, so the "18 numbered theorems"
   print as Theorems 3–20 (paperg.aux: def:nagel=1, def:brocard=2, thm:gergonne=3 … thm:droz=20). A reader who sees
   "the eighteen numbered theorems" and then finds a Theorem 20 will stop and count. Fix: give definitions their own
   counter (line 22 `\newtheorem{definition}{Definition}`), so the theorems print as 1–18.

2. MINOR (line 812). "a script checked all 108 names" counts occurrences, not names: there are 108 `\decl{…}`
   occurrences but only 102 distinct names. I checked all 102 against the published `gate.sh` REQUIRED lists
   (151 + 147 entries) and none is missing; the three `\texttt` names (brocardPoint₁/₂_angles, inradius_sq) are also in
   REQUIRED. Fix: "all 102 distinct names (108 occurrences)".

3. MINOR (lines 626–629). Same files, two machines, but the ablation stage ran 32 jobs on arm64 and 41 on x86-64
   (arm64_…_20261025_154123: `jobs 33 | NEEDED 32`; x86_…_20261025_214511: `jobs 42 | NEEDED 41`). The paper reports
   the gap but does not explain it. The arm64 report also shows "uncommitted entries: 11", so the trees may not have
   been identical. Fix: add one clause giving the cause (different tree, or a harness difference), or drop the x86
   ablation figure.

4. MINOR (lines 615–666). Two sets of battery runs are in `reports/battery/` but are not reported in the text:
   paperg_nagel with 140 theorems (4 runs) and paperg_brocard with 109 theorems (2 runs, which have one survivor).
   Several runs also report uncommitted working-tree entries (11 or 3). Line 616 says every run's report is in the
   supporting material, which is true, but a referee comparing the files with the text will find these runs missing.
   Fix: add a sentence such as "Intermediate runs after the Layer-14 files (140 and 109 theorems) are also in
   `reports/battery/`; some early runs were on trees with uncommitted changes."

5. MINOR (lines 591–592). "The extensions added files and import lines only and changed no earlier statement" cannot
   be checked from the public artefacts, because each repo is a single squashed commit (line 805). The extensions also
   changed `gate.sh` (REQUIRED list) and `tests/tamper.sh` (falsehyp_ext / falsehyp2), so "files and import lines only"
   is not literally true. Fix: "added library files, import lines, REQUIRED entries and one tampering test, and
   changed no earlier statement (the development history is not published; see the integration reports)."

6. MINOR (line 529). The lean-genius file also defines the Gergonne point, the excentres and the contact feet, and it
   proves `gergonne_on_cevian_A` and `excenterA_on_bisector_A` (I fetched it at 470a7df). "It defines the Nagel point
   and the incentre" understates what it does, although the classification as PARTIAL (lines 532–535) is right. Fix:
   "It defines the incentre, excentres, Nagel and Gergonne points and the contact feet by Ravi-barycentric formulas…".

7. MINOR (Section 7, lines 516–575). A JAR/ITP referee will ask about automated geometry theorem proving. All the
   identities in Theorems 3–11 and 19–20 are standard benchmarks for Wu/Gröbner and area-method provers (Chou,
   *Mechanical Geometry Theorem Proving*, 1988; Chou–Gao–Zhang, *Machine Proofs in Geometry*, 1994; Narboux's area
   method in Coq, 2004, already searched as rocq-archive/area-method). The novelty claim, which is about Mathlib-tied
   statements, survives, but the omission looks like a gap. Fix: add two or three sentences citing this line of work and
   saying what is different here (Mathlib's incentre, touchpoints and unoriented angles, rather than coordinates).

8. MINOR (lines 578–740, whole Verification section). Terms such as "Layer 13/14/15", "the battery of our earlier
   papers", "heartbeat limit", "satisfiability certified" (by an LLM-backed certifier, per the reports' `llm-error`
   field) and the two machines are used without a self-contained definition; the reader is sent to earlier Zenodo
   papers. The section is also about a third of the paper. Fix: add a short table that defines each layer in one line,
   say that the satisfiability certifier is model-assisted with kernel-checked output (if that is correct), and
   consider moving the per-run battery figures to an appendix.

9. MINOR (line 69 abstract; line 340). The abstract says "the Brocard points are isogonal", but the Lean statement
   (Extensions:21) proves three angle equalities only, and line 340 says so. The abstract should be equally precise.
   Fix: "that the Brocard points satisfy the three isogonality angle equalities".

10. MINOR (housekeeping, not visible in the PDF). (a) Lines 36–37: the comment "No commit is pinned yet…" is stale,
    because lines 39–40 pin both commits; the .tex is published in the supporting repo, so delete or update it.
    (b) The published `PaperG-triangle-centres/reports/HAND_CHECK_SHEET.md` still says "The repositories are **not
    public yet**, so the links are placeholders"; update it now that the repos are public. (c) Table caption line 205
    says starred rows come from `Extensions.lean`, but part of Thm 11 (the inradius form) is in `Inradius.lean`; add
    "(and `Inradius.lean` for Thm 11)".

No finding on mathematical truth, on prose-vs-Lean fidelity, or on any number in the Verification or Availability
sections. Details below.

## Checks completed

**Mathematics** (sympy, exact arithmetic, own code in <clone dir>/scripts/check*.py). Triangles (0,0),(4,0),(1,3);
(0,0),(7,0),(2,5); (−1,2),(5,−3),(3,4); obtuse (0,0),(6,0),(−1,2); 3-4-5. All passed on every triangle: N−G=2(G−I);
Spieker = mid(I,N); incircle/A-excircle contacts = feet of I and J_a, midpoint = mid(B,C); N on A–T_e, Gergonne on A–T_i;
medial Nagel = I; N = anticomplementary incentre; L=H+2(O−H) = anticomplementary orthocentre; G,O,L collinear;
r²=(s−a)(s−b)(s−c)/s; all three Spieker powers = (s²+r²)/4; six symmedian angle equalities; K = pedal centroid and the
unique solution of "X = centroid of its pedal triangle"; Brocard angle equalities for Ω, Ω′ (stated weight orders);
isogonality; cot ω = Σcot = S/(4Δ); cot ω ≥ √3; |MΩ|=|MΩ′|=|OK|/2 (M=mid(O,K)); |OΩ|=|OΩ′|; six Lemoine points (line 182)
equidistant from M and on the parallels through K as at line 186; Droz-Farny midpoints collinear for d₁=(1,2),(2,1)
(configurations with a direction parallel to a side, the excluded case, skipped). Symbolically: |OK|², |OΩ|², |KΩ|²
each contain a⁴+b⁴+c⁴−a²b²−b²c²−c²a² (line 497); foot parameter (−a²+3b²+c²)/(2S) (line 468) correct. Every Layer-14
witness value at lines 681–696 reproduced (I, G, N, Ge, Sp, excentres, power 37/4; O, H, L; K, Ω, Ω′, cot ω=11/6, Δ=6;
Droz-Farny midpoints).

**Prose vs Lean.** All 31 `\src` targets and the extra line numbers land on the named `theorem` (Main 170/179/188, 290,
328, 334, 357, 362, 373, 385, 408; Ext(N) 201, 228, 237, 249, 261, 274, 297, 308, 319, 332, 357; Inradius 19, 40; Brocard
Main 22, 100, 115, 150, 233, 280, 327, 366, 402; Ext(B) 21, 85, 116, 175, 183, 231, 314, 353, 439, 449). Hypotheses match:
only the triangle, except `[Fact (finrank ℝ V = 2)]` on the pedal converse and Droz-Farny, Droz-Farny's hperp and six
non-direction hypotheses, and the two equalities on `brocard_eq_circumcenter_of_equilateral`. Quantifiers match; the
degenerate cases are honest (iff at Ext:231; π/2 convention at lines 493–496). Definitions 1–2 match the Lean
definitions exactly. Cited Mathlib names exist at 0df444a3. No over-claim found.

**Numbers.** Line counts (mine): nagel 6+285+414+362+45+408+741=2,261 (7 files); brocard
7+57+338+463+384+546+522+723=3,040 (8 files). REQUIRED 151/147; Lean v4.33.1 and Mathlib 0df444a3 in both manifests.
Receipts: PASS 151/147 on both hosts at both commits, all tampering rejected, digests 201feb97…/bd4e777b…. Gate counts
48/77/38/67/88/91/149/147/151 all in the reports; tamper.sh has the 7 tests and the stated falsehyp targets. All 22
battery reports agree with lines 617–666 (78/105/40/68/180/182/147-theorem stages, both machines, published-commit runs,
the 8 unused binders and 10 survivors as classified). Layer 14: 16+9 restatements, 5+5 witnesses. Layer 13: 36
statements, 35 equivalent, pair 18 blind-stronger then repaired (FIX18_REPORT). Layer 15: 23 statements (10 N + 13 S).
Hand-check sheet: 67 statements.

**Related work and references.** Novelty wording matches PRIORART_RERUN.md and SCOUT.md (lean-genius and Certified ETC
both PARTIAL; gaps disclosed). DOI 10.1007/s11786-016-0254-4 resolves and Crossref matches (vol 10, pp. 57–73, 2016);
PR #44230 is by Weiyi Wang, opened 2026-09-26, still OPEN; the lean-genius blob at 470a7df, the ETC URL, all six Zenodo
DOIs and LEAN-verification/PaperG-triangle-centres return 200. Not verified: the Wayback CETC snapshot (Internet Archive
offline during this review).
