MINOR REVISION — BLOCKER: 0; MAJOR: 0; MINOR: 5.

# Independent review, round 2 / layer 12 — Paper F

The substantive new mathematics survives this review. In particular, **C4_b really proves uniqueness of the geometric focus/directrix pair with no additional hypothesis**, and **D3/D4 really include orthocentric configurations**. Removing the old Lambert/uniqueness caveat is justified. The remaining issues concern the scope and consistency of verification claims, a table caption, and small qualifications—not a discovered false Lean theorem.

Reviewed the revised TeX, the final L14/L15 sources, all specified comparison/scope reports, the four extended battery reports, the round-1 report, and the prior-art report. I performed independent textual comparisons of definitions and theorem signatures and checked declaration/gate membership. I did **not** run a new Lean build or battery, re-audit agent transcripts, or repeat the round-1 numerical experiments. Kernel-build/axiom results below remain the supplied receipts, not a new execution by me.

**Version note:** `paperf.tex` changed during this review: repository names and the availability counts were filled in. This report uses the final observed 898-line version, SHA-256 `60a9c1f198a47e0f59a254cee8b9bdbf3f2804b35edab6a1f1c4a45504d8fd5a`. Its PDF has 17 pages. There are now **5**, not 10, actual `\PH{...}` uses: date, two URL/commit entries, fresh-clone receipts, and hand check. Expected publication placeholders are not defects.

## Numbered issues

1. **MINOR — Explicitly exclude L14/L15 from the reported battery, and distinguish historical gates from the final gates.** Paper **609–619, 669–700, 755–756, 790–792**.

   The numerical battery figures are correct, but the paper never explicitly says that the reported batteries **did not cover `L14Parabola.lean`, `L14Quadrangle.lean`, or either `L15Classical.lean`**. “Extended developments (110 and 106 gated declarations)” lets an informed reader reconstruct this, but is insufficient beside the new main results and the final 12-file repository table. “The four new files” at 699 also now needs an explicit historical referent: there are eight added files across the two final repositories.

   Evidence: all four `_ext.md` receipts say 110/106 gated declarations and 194/266 audited theorem declarations. The final REQUIRED lists contain **240/220** distinct names. The paper reports the historical 92→110 / 94→106 gates and L14's 168/148, but not the final 240/220 totals.

   **Fix:** add: “These battery runs cover the developments through ParabolaPoints/QuadrangleSym only; they do not test the subsequently added L14 or L15 files.” Name the four earlier added files at 699. Separately record final gates at 240/220 with their receipts. If the new final-repository batteries finish, replace or clearly separate the tables; do not carry forward the old survivor/unused-binder/no-mutant claims without checking the new results. This is a coverage disclosure, not a request to doubt the completed final gates.

2. **MINOR — “Every main theorem” overstates the scope of the Mathlib-only restatement/non-vacuity exercise after the starred results were added.** Paper **68–70, 163–166, 702–704, 723–734, 822–824**.

   Table 1 now explicitly includes the starred L15 results among the main theorems. L14 does not restate classical uniqueness, general triangle Lambert, the rectangular-conic results, or the new orthocentric pedal/diagonal branches. L13's 23 blind statements likewise concern the original numbered theorem environments, not those added results. L15 is a separate, valid comparison, but its types deliberately use the independently written local `Parabola`, `Quadrilateral`, `RectangularConic`, etc.; they are not the 27/19 QuadMiquel-free types checked at L14.

   There is a smaller literal-completeness problem even within the original statements: `L14Parabola.lean` has vertex locus/distance/minimization restatements but no standalone Mathlib-only restatement of `vertex_mem_axis` or `axis_perp`, which are components of the vertex theorem/table row. The corresponding general classical facts are instead proved in L15 (`cov_classical_C7_a`, `cov_classical_C5_a`). The L14 results and witnesses I inspected are genuine; the problem is the universal wording.

   **Fix:** describe L13 as covering “the original numbered theorem statements” and L14 as providing “Mathlib-only formulations and non-vacuity witnesses for the original geometric results listed in the Layer-14 table,” explicitly excluding the later starred additions and identifying the axis facts as covered by L15. Alternatively add the missing restatements/witness mappings and rerun the type audit. Do not silently extend the 27/19 audit to the final enlarged theorem set.

3. **MINOR — The Table 1 caption still assigns non-orthocentricity to an explicitly orthocentric starred row.** Paper **134–143**; related wording **420–427**.

   The round-1 exception for Theorem `thm:ortho` was fixed, but the caption now says that all Part-B results except that theorem assume non-orthocentricity, while row 134 is “pedal, diagonal circles: orthocentric case.” The later sentence “with that file's hypotheses” points toward the correct reading but conflicts with the preceding blanket statement. D1_c/D1_d also do not assume non-orthocentricity. The prose “All later theorems assume” at 420 should similarly be explicitly restricted to the numbered main-file theorems, not the L15 results discussed immediately afterward.

   **Fix:** “For the unstarred rows of Part B, all except Theorem [ortho] assume non-orthocentricity… The starred rows use the classical hypotheses described below and include the orthocentric case.” Restrict “All later theorems” to “The remaining numbered theorems of this section.”

4. **MINOR — Keep the limiting-case scope statements as narrow as the evidence and intended configurations.** Paper **793–799, 815–819**; related **402–403**.

   X3/X4 are correctly identified as numerical and not formalised. However, the limitations shorten the careful “exactly one pair” wording at 477 to “one pair,” and X4 says simply “If three points are collinear.” The latter includes four collinear points or repeated points, for which there are not three remaining genuine triangles. The scope report's B4 examples have **three distinct collinear points and a fourth point off their line**. Its Part-A rank/directrix observations are exact/numerical checks on specified configurations, not a formal universal classification of every degeneracy; 795–796 can currently be read as that stronger classification.

   **Fix:** retain “exactly one pair of opposite sides is parallel” in the limitations; state X4 with three distinct collinear points and the fourth off their line. Say “In the tested parallel/concurrent degenerations…” for the scope experiment, or distinguish the general classical argument from what was actually checked. Also qualify 402–403 as “in the main files the formula is a definition and no rectangular hyperbola appears,” since it now does appear in L15. These are small scoping corrections; X3's quoted residual and experimental counts are accurate.

5. **MINOR — The corrected prior-art account has not been propagated to its supporting report.** Paper **563–600** versus `reports/priorart.md` **25, 54, 88**.

   The paper now correctly cites the AFP Steiner-line theorem and explains its ingredient-level relevance, including the sweep's failure. But the supplied prior-art report still labels A1/AFP `NOTHING`, says the triangle Steiner line was “Not found as a standalone theorem in any source,” and concludes from the two controls that “the search method works.” This is a stale evidence artifact, not a renewed objection to the paper's corrected scoped novelty claim.

   **Fix:** preserve the original search receipt but append a dated correction recording AFP `Steiner_Line_Theorem` as FOUND-PARTIAL/ingredient for A1, with the entry/source links and the distinction between the triangle and four-line statements. Mark the original negative entry superseded. No new exhaustive search is required to make this correction.

## What I verified

### Disposition of all six round-1 issues

| Round-1 issue | Round-2 finding |
|---|---|
| False rectangular-hyperbola pencil paragraph | **Fixed.** Lines 383–386 distinguish the pencil of all conics, its unique rectangular member outside the orthocentric case, possible perpendicular-line degeneration, and the orthocentric pencil with moving centres. |
| Missing AFP Steiner-line prior art | **Fixed in the paper.** Abstract, reflection discussion, related work and bibliography now acknowledge it; GeoGebra/Coq and kernel-checked algebraic methods are handled correctly. Supporting report still needs issue 5's correction. |
| Battery scope/interpretation | **Fixed for the old batteries.** No-mutant declarations, unresolved satisfiability, skipped no-hypothesis declarations, heartbeat kills and proof-relative ablation are disclosed. New L14/L15 coverage needs issue 1. |
| Non-orthocentricity in abstract/introduction | **Fixed.** Lines 58–59 and 96–99 qualify the claims before making them. |
| Table caption's orthocentric exception | **Fixed for the original rows; regression for the new starred rows**, issue 3. |
| Replacement quadrangle battery | **Resolved.** The paper no longer says it is pending; completed two-machine extended runs supersede the earlier runs. It does not rely on the excluded OOM attempt. |

### L15: definitions, statements, and proof content

Independent exact-string checks found **30 relevant original definitions/structures/abbreviations in each final L15 file, all byte-identical declaration blocks to `layer15/Classical.lean`**. The shared prelude is included in both counts. No classical definition present in either setting was altered. The source classical file's SHA-256 is exactly `afe16593f65ef05be32ba0cab87257fb82b0c76509eca6930fc2095d68441062`.

I compared the full binder/type text before `:=`: **all 12 Setting-A and all 10 Setting-B `cov_classical_*` signatures are byte-identical to the corresponding classical theorem signatures after the theorem-name substitution**. Both construction-lemma signatures also match exactly. Proofs, namespace, headers and placement necessarily differ; “verbatim” is correct for the definitions and theorem statements, not for the entire files.

| Cited result | Final source evidence | Verdict |
|---|---|---|
| `l15_lines_not_parallel_axis`, C4_a | A:595–631; classical `Tangent` at 109–111 includes genuine line, nonparallel axis, unique intersection. The proof transfers `line_not_perp` and `parabola_tangent`. | Full classical tangency, not merely the weaker local predicate. |
| C4_b | A:1046–1056: `∃! fd : Point × ALine, IsInscribedFocusDirectrix Q fd`; the only parameter is `Q : Quadrilateral`. `IsInscribedFocusDirectrix` at 255–256 quantifies over **any** classically inscribed `Parabola`, not only the constructed one. | Genuine geometric focus/directrix uniqueness; no extra orthocentre-line or focus-identification hypothesis. |
| C6_a / C6_b | A:925–927 and 1020–1022. C6_a quantifies over any Mathlib triangle and genuine parabola tangent to all three full side lines. C6_b derives Miquel incidence for every inscribed parabola. | General Lambert is proved. C1/setup uniqueness then identifies that focus with M. |
| C5_b | A:1059–1066. Assumes only `Inscribed Q P` and supplies a Newton–Gauss line parallel to P's axis. The extra-directrix `_part` lemma is **not** the cited final result. | Correct universal inscribed-parabola claim. |
| D3_a / D3_b | B:942–960. Only Q, common point P, index i, and omitted-point-off-circumcircle hypothesis; no non-orthocentricity. `d3_cosph` at 933 explicitly splits the orthocentric case; 915–931 uses the nine-point circle itself. | Orthocentric pedal branch genuinely covered. D3_a gives unique positive-radius centre/radius data; `d3_feet_ne` supplies distinct feet. |
| D4 | B:964–1016. Assumes finite opposite-side intersections and common-point incidence, not non-orthocentricity; explicit orthocentric branch identifies the diagonal points with altitude feet. | Orthocentric diagonal branch genuinely covered. This is incidence for **any common point**, not the totalised formula's junk value. |
| D1_c / D1_d | B:1042–1059 and 1146–1161. D1_c constructs a rectangular conic at every common point, in both branches. D1_d adds exactly `¬ IsDegenerateRectangularCenter Q P` and obtains `k ≠ 0`. | Correct centre/proper-hyperbola statements. They do not themselves assert uniqueness of the conic; the prose's pencil uniqueness is classical background. |
| Construction obligations | A:223–232, B:362–370. Actual proofs of the originally admitted affine-independence obligations. | Not hidden hypotheses or retained admissions. |

The uniqueness proof uses general Lambert to identify the focus and `l15_inscribed_directrix` to identify the directrix via two distinct reflections. It does not smuggle uniqueness into the definition of `Inscribed` or into `Parabola`.

**Lambert caveat removal:** justified throughout the abstract, introduction, theorem discussion and limitations. Lines 254–260, 365–376 and 809–814 remain candid that the main-file `Tangent` is weaker. The paper correctly labels the weak-tangency counterexample comment as informal, not a Lean counterexample.

### L13 and L14

- L13's **23 statements**, **11 A pairs / 12 B pairs**, the safe `blind_8` generality difference, and the genuine `miquelPt_spec` dependence match the reports. The 23-statement run did not independently establish M-definition agreement by unfolding.
- Both disclosures appear: the void first attempt and the guessed missing Newton–Gauss conjunct. The archived first blind text and rebuilt text are present; the writer explicitly reports the truncated conjunct. Transcript-audit and aborted-L15-attempt claims were not independently re-audited from raw transcripts in this review.
- L14 contains exactly **27 A / 19 B** `l14_*` plus `l14w_*` declarations, consistent with the reported elaborated-type audits. I inspected the Mathlib configuration binders, main restatements, witness statements and key proof connections. The universal restatement wording needs issue 2, but the listed results themselves are supported.
- The witness-table data check out: distinct reflections/contact points; positive focus/directrix distance; nontrivial vertex; nonzero Newton–Gauss directions; M distinct from six vertices; P=`1−i` on four distinct nine-point circles; two distinct common points in the orthocentric example; distinct pedal feet/diagonal points and P. The unique nearest-point statement is genuinely stronger than the original non-strict inequality (`l14_vertex_closest`, A:569).
- The changed-meaning restatements of the denominator and S4 are disclosed correctly. L14's 168/148 gates match its reports.

### Battery figures

Every quoted headline number matches the four specified extended reports:

| Quantity | Part A | Part B |
|---|---:|---:|
| Mutants rejected, both machines | 393/394 | 552/553 |
| Heartbeat kills included above | 2 | 29 |
| Contradiction probes / additional hypothesis-free skips | 157 / 37 | 201 / 65 |
| Satisfiability, Jack | 98/194; 96 unresolved | 146/266; 120 unresolved |
| Satisfiability, John | 101/194; 93 unresolved | 161/266; 105 unresolved |
| Ablation: existing proof broke / still compiled | 251 / 17 | 378 / 17 |
| Library linter warnings | 0 | 0 |

The named no-mutant examples and original main-result unresolved entries match. The inherited survivor is `orthocentres_not_all_eq'`; the 17 unused binders belong to inherited auxiliary algebra. The Layer-14 witnesses are separate evidence, not retroactively credited battery certificates: each `_ext` report still records **zero linked Layer-8b witness certificates**.

### Names, final repository counts, and remaining presentation

- **100 distinct `\decl{QuadMiquel...}` citations**, all found in the relevant final source and REQUIRED list. No missing cited L15 declaration.
- REQUIRED: **240 A / 220 B**, each without duplicate names. Each L15 file contains **72 explicit theorem declarations**, all gated, including the construction obligations and all cited coverage theorems.
- Final library counts, including root import files: **A 12 files / 5,250 physical lines; B 12 / 4,977**. The newly updated availability table is exact. Individual L14/L15 counts 1,321/1,132 and 637/1,167 also match.
- Scope report X3 supports the quoted three configurations, 60 digits and maximum normalized residual `6.0e−62`. X4 is correctly marked unformalised; sharpen its configuration as in issue 4.

**Optional cuts, not additional defects:** the paper can lose substantial length without losing evidence. Move most of 621–667 (detailed builder residuals and exact sample arithmetic) to an appendix/receipt table. Compress the repeated L15 summary across the abstract, introduction, contributions, “What is not claimed,” Lambert discussion and verification paragraph: keep one full theorem-to-declaration account and short cross-references elsewhere. A compact stage table—main files / L14 / L15 / battery coverage—would both shorten the historical gate narrative and prevent issues 1–3. The five numbered corrections above are small and do not require changing the established main Lean proofs.
