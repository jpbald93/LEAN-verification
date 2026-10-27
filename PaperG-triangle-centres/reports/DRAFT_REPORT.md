# Paper G draft report (2026-10-25)

`paperg.tex` → `paperg.pdf`: **15 pages**. pdflatex run twice: rc 0, 0 errors, 0 undefined references, 0 overfull boxes.
The `\commitof` / `\src` pin macros are defined, but **no pins are set**, so `\src` prints file:line only.
File:line references are to the local commits the arm64 machine `16b07eb` (paperg_nagel) and the x86-64 machine `e23b8c3` (paperg_brocard), read via ssh on 2026-10-25.

## Placeholders (\PH{}), 13 in total
| line | placeholder |
|---|---|
| 47 | date |
| 545 | re-run of the prior-art search with web search before submission |
| 580 | fresh-clone receipts at the published commits, both machines (build, gate, tamper, hash digest) |
| 609 | final battery runs on the published repos (with L14/L15 files), both machines |
| 642 | Layer 13 blind restatement + comparer results |
| 645 | Layer 15 classical blind formalisation + comparer results (Classical.lean exists in layer15/, comparers not yet run) |
| 648 | hand check paragraph |
| 685 | Limitations: human checks done before submission |
| 704 | final file/line counts of the published repos |
| 705 | repo URL + commit for paperg_nagel |
| 706 | repo URL + commit for paperg_brocard |
| 708 | supporting-material folder in LEAN-verification |
| 710 | name gate against the published REQUIRED lists (already passed against the local lists, see below) |

## Mechanical checks done
- **Name gate (local):** all 105 distinct `\decl{}` names are in the REQUIRED lists of the arm64 machine `~/lean/paperg_nagel/gate.sh` or the x86-64 machine `~/paperg_brocard/gate.sh` (both now include L14). Two names were first written wrongly as `NagelLine.deLongchampsPoint` / `NagelLine.anticomplementary`. The real namespace is `Affine.Triangle.*`, and both are now fixed.
- **Mathlib names:** all 15 `\mdecl{}` names were found by grep in the Mathlib package on the arm64 machine (`~/lean/clifford/.lake/packages/mathlib`, same manifest).
- **PR #44230:** `gh pr view` gives title "feat(Geometry/Euclidean): prove Euler's theorem in geometry", author Weiyi Wang (wwylele), created 2026-09-26, OPEN.

## Claim → evidence
| claim in paper | evidence |
|---|---|
| Definitions and weights (Nagel, Gergonne, Spieker) | the arm64 machine `NagelLine/Basic.lean:267/271/276` (read directly); REPORT_A |
| de Longchamps, anticomplementary defs | the arm64 machine `NagelLine/Extensions.lean:24/30` (read directly); REPORT_C |
| symmedian / Brocard₁ / Brocard₂ / area / lemoinePoints defs | the x86-64 machine `Brocard/Basic.lean:18–53`, `ExtLemmas.lean:22` (read directly); REPORT_B, REPORT_D |
| Thms 1–4 statements, lines | REPORT_A table, plus `grep ^theorem` on the arm64 machine (lines match) |
| Thms 5–9 statements, lines | REPORT_C table, plus grep on the arm64 machine (lines match) |
| Thms 10–13 statements, lines | REPORT_B, plus grep on the x86-64 machine (lines match) |
| Thms 14–18 statements, lines | REPORT_D, plus grep on the x86-64 machine (lines match) |
| "r² = (s−a)(s−b)(s−c)/s not stated in library" | Verified: `grep inradius` in NagelLine/*.lean finds only the docstring (Extensions.lean:200). There is no theorem. |
| only hypothesis is t (Nagel); finrank only in B2 converse and Droz-Farny | REPORT_A ("No Fact(finrank) needed"), REPORT_B Hypotheses, REPORT_D D4 |
| s−a>0 from height_pos via Heron | REPORT_A bridge lemmas |
| incentre weights a/(2s), excentre weights | REPORT_A, Basic.lean:219/238 |
| touchpoint bridges via coe_orthogonalProjection_eq_iff_mem; candidates (s−b)/a, (s−c)/a | REPORT_A; Main.lean:94–104 (read) |
| Ravi lemma a=y+z, b=x+z, c=x+y | Main.lean:48–49 (read) |
| excircle contacts strictly inside side | REPORT_A sbtw lemmas |
| angle reduction (squared cosines + sign), cot formula, gram_det_pos | REPORT_B Method; Lemmas.lean:66–75, 115–127, 184–190 (read) |
| foot parameter (a²−b²+3c²)/(2S) | REPORT_B Method |
| B2 converse by linear_combination | REPORT_B Method |
| Droz-Farny certificate (Q = κ⟨d₁,d₂⟩) | REPORT_D Notes |
| degenerate factor a⁴+b⁴+c⁴−a²b²−b²c²−c²a²; ∠=π/2 convention | REPORT_D Notes |
| gate 48→77 (nagel), 38→67 (brocard) | REPORT_A, REPORT_C, REPORT_B, REPORT_D |
| tamper: 7/7 per final suite; falsehyp targets | REPORT_C (nagel: falsehyp, falsehyp_ext), REPORT_D (brocard: falsehyp, falsehyp2) |
| section-variable binder incident | REPORT_A Tamper note |
| cross-machine brocard: build ok, PASS 67, tamper 7/7, hashes identical | CROSSRUN.md |
| battery nagel pre-ext 210/210 (7 tout), contra 0/12, sat 2/78, ablation 29/1 unused, lint 0/2 | the arm64 machine `~/leancheck/reports/paperg_nagel_20261024_193651.md` (read via ssh) |
| battery nagel with ext 282/282 (7 tout), contra 0/14, sat 4/105, ablation 32/1, lint 0/3 | the arm64 machine `paperg_nagel_20261025_154123.md`; the x86-64 machine `paperg_nagel_20261025_214511.md` has the same summary JSON line |
| battery brocard pre-ext 97/97, contra 0/13, sat 8/40, ablation 54/0, lint 0/2 | the x86-64 machine `paperg_brocard_20261024_200205.md` |
| battery brocard with ext 152/152, contra 0/28, sat 7/68, ablation 111/0, lint 0/4; other machine identical | the x86-64 machine `paperg_brocard_20261025_164034.md`; CROSSRUN.md (the arm64 machine run 20261025_213509) |
| unused binder sub_pos_aux (_hyz : 0 < y+z) | the arm64 machine battery reports, "unused hypotheses" line |
| L14: 16+9 restatements, 5+5 witnesses, pp.fullNames grep 0, witnesses and coordinates, gates 91/88, tamper | L14_REPORT.md |
| Mathlib content (Euler line, touchpoint, medial, Ceva); no hits for nagel etc.; atlas-lean EulerOI | SCOUT.md |
| lean-genius partial (CevasTheoremOQ04OQ04OQ02.lean, 2026-06-25, 0 sorry) | SCOUT.md table |
| other systems none found; brocard hits are number theory | SCOUT.md |
| search gaps (no web search; ProofAtlas sitemap, 752 URLs) | SCOUT.md Sources |
| file/line counts 1064 / 1793; L14 408 / 522 | REPORT_C Size, REPORT_D Size, L14_REPORT; the x86-64 machine `wc -l` confirms Brocard files |

## Not used / notes for the orchestrator
- **Post-L14 battery runs exist, are NOT in the paper, and need classification.** the arm64 machine nagel `20261025_224501` and the x86-64 machine nagel `20261026_002825`: 140 thms, 376 mutants, **368 killed, 8 SURVIVED**. All 8 survivors are in L14 witness helper lemmas (`l14b_tri345`, `l14b_tri_anti`, `l14b_tri2`, `l14b_tri2_anti`: non-collinearity of explicit integer triangles, where changing a coordinate keeps the statement true). That is expected and harmless, but it must be reported when the final battery \PH is filled. The the arm64 machine brocard run `20261026_011841` had no summary line yet.
- The leancheck verdict table misparses gate/tamper (CROSSRUN note); the paper uses the verbatim lines only.
- Layer 15 (`layer15/Classical.lean`, CLASSICAL_REPORT.md) exists, but the comparers have not run, so it is left as \PH.
- References: only Lean 4 (CADE-28), Mathlib (CPP'20), PR #44230 (verified via gh), Kimberling ETC, Johnson (Dover 1960 republication of Modern Geometry 1929), Coxeter–Greitzer (MAA 1967), Honsberger Episodes (MAA NML 37, 1995), Papers A–E with DOIs, Paper F "(2026, preprint)". Lean 4, Mathlib, ETC and Coxeter–Greitzer entries were copied from the author's earlier papers. Johnson's and Honsberger's bibliographic details are from memory, so **check the year and series** before submission.
- The AI disclosure says "parts of the checking were done by a different model". This holds for the earlier papers' L15 writer; confirm it for Paper G once L13/L15 run, or rephrase.
