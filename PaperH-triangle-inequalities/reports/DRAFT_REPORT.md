# DRAFT_REPORT — Paper H

**Title:** Classical triangle inequalities and the Fermat–Napoleon configuration in Lean 4
**Files:** `paperh.tex`, `paperh.pdf` (in AFM/PaperH/). Drafted 2026-10-28, inline (no subagents). The file was written section by section to disk and compiled every two sections.
**Build:** pdflatex run twice (plus a third pass as a check). The PDF has **21 pages**, **0 errors**, **0 undefined references/citations** and **0 overfull boxes** of any size.

## Sections
1. Abstract, Introduction (prior art stated up front), Contributions
2. Setting, conventions, and the two basic tools: the barycentric (Leibniz) distance formula, and certificates modulo Heron
3. The Euler family: Thms 1–4 (OI², R ≥ 2r and its equality case, excircles, OG²/OH²/IG²), plus the longtable of all 33 theorem rows (Lean name, File:line)
4. Fundamental quartic, Gerretsen, Kooi (Thms 5–7)
5. Weitzenböck, Hadwiger–Finsler, isoperimetric, Leibniz (Thms 8–11)
6. Neuberg–Pedoe (Thm 12)
7. Ptolemy: the inequality (reproof) and the equality characterisation (Thms 13–14)
8. Erdős–Mordell: key lemma, inequality and equality case; Barrow (Thms 15–17)
9. Fermat–Torricelli (Thms 18–19); the Fermat–Napoleon lines (Thm 20) and Napoleon (Thm 21)
10. Verification: layer table, gate/tamper table, battery table with all 6 survivors explained, cross-machine builds
11. Related work and prior art (detailed, with dates; search gaps; classical sources)
12. Limitations
13. Data availability; Acknowledgements and use of AI; References (34 items)

## Facts checked against the sources (read-only, via ssh)
- Every theorem is stated in prose with all of its hypotheses: the closed triangle as nonnegative weights; strict interior for Barrow; angles < 2π/3; `Fact (finrank = 2)` and the orientation `o` for H4; the six distinctness hypotheses for Ptolemy.
- I checked all 88 distinct `\decl{}` names against the union of the three gate.sh REQUIRED lists (155 = 60 + 48 + 47 names). All are present.
- I checked all 43 File:line references by printing the line from the source. Each line starts the named declaration.
  - paperh_euler and paperh_fermat were checked on the x86-64 machine.
  - Mordell was checked in `~/x_paperh_mordell` on x86-64. Its library-file SHA-256 digest equals that of the arm64 copy `~/lean/paperh_mordell` (854b5850…).
- Battery figures come from the reports in `~/leancheck/reports/`:
  - paperh_euler_20261028_151758 and paperh_fermat_20261028_223117 on x86-64;
  - paperh_mordell_20261028_164005 on arm64.
  - The exact survivor mutations were copied from those reports.
  - **Note:** the euler report says 225/228 rejected, of which 2 were by timeout. The paper says so.
- Pinned Mathlib is 0df444a3. It has `mul_dist_le_mul_dist_add_mul_dist` and `mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`. It does **not** have `dist_lineMap_circumcenter_centroid_sq`, and the paper says that lemma was merged after the pin.
- In the Ptolemy proof, the source does not call `EuclideanGeometry.inversion`, even though the docstring mentions it. The paper says this.

## Citations and how each was verified
| key | how verified |
|---|---|
| lean4 | Crossref 10.1007/978-3-030-79876-5_37 (200; title and pages 625–635 match) |
| mathlib | Crossref 10.1145/3372885.3373824 (200; pages 367–381) |
| bottema | Crossref has reviews of the book (Math. Gazette 10.2307/3613814; AMM 10.2307/2316604) confirming authors, title and 1969 Wolters-Noordhoff. No DOI for the book itself, and none is cited |
| weitzenboeck | Crossref 10.1007/BF01203160 (Math. Z. 5 (1919) 137–146) |
| finslerhadwiger | Crossref 10.1007/BF01214300 (Comment. Math. Helv. 10 (1937) 316–326) |
| erdos1935 | Crossref 10.2307/2301373 ("Problems for Solution: 3739–3743", AMM 42 (1935) p. 396, author Erdős first) |
| mordellbarrow1937 | Crossref 10.2307/2300713 ("3740", AMM 44 (1937) p. 252, authors Erdős, Mordell, Barrow) |
| kazarinoff1957 | Crossref 10.1307/mmj/1028988998 (Michigan Math. J. 4 (1957) 97–98) |
| pedoe1941 | Crossref 10.2307/3606570 (Math. Gazette 25 (1941) 310–311, Note 1562) |
| pedoe1942 | Crossref 10.1017/S030500410002209X (Proc. Camb. Phil. Soc. 38 (1942) 397–398). **The brief said "Pedoe 1943"; Crossref dates it 1942.** |
| blundon1965 | Crossref 10.4153/CMB-1965-044-9 |
| coxetergreitzer | taken from Paper G's bibliography (book, no DOI); not re-verified |
| wwylele, pr44230, atlaseuler, plby, formalconj, lgmordell, lg898, lgweitz, lghf, lgptolemy, compfiles, principia, wiedijk100, afpnapoleon, tanrikolu, shadowbench, atlasnapoleon, guilhot | every URL returns HTTP 200 with curl (2026-10-28). Dates and statements come from SCOUT.md, which downloaded and read each file. For Napoleon the sources are Paper A's prior-art section, the AFP page (fetched: Ramos, Hulak, de Queiroz, 24 August 2026, complex coordinates, both orientations) and the atlas-lean NapoleonTheorem.lean (fetched; it has no Fermat/concurrence theorems). guilhot: the GitHub API lists `point_napoleon.v` |
| kovacs2017 | arXiv API id 1708.02993 (title and authors match); URL 200 |
| paperA, paperD | DataCite: the DOI titles match; doi.org returns 200 |
| paperG | **no DOI available**, so this is a \PH |

**Not cited (could not be verified):** Euler 1765, Gerretsen 1953 and Kooi 1958 originals. Crossref found nothing usable for them, so Gerretsen and Kooi are cited through Bottema, and the paper says the originals were not obtained. Euler's original is not cited. I dropped a claim about Neuberg's priority because I could not verify its source.

## \PH placeholders (13, all shown in red in the PDF)
1. line 47: date
2. §Verification: gate counts at the published commits (after Layer-13–15 files)
3. §Verification: fresh-clone receipts (both machines, digest of sorted file hashes)
4. §Verification: final batteries on fresh clones (both machines)
5. Layer 13 (blind restatement)
6. Layer 14 (Mathlib-only restatements plus witnesses; suggested witnesses listed)
7. Layer 15 (classical statements)
8. Hand check
9. External review (Gemini / Argon)
10. §Availability: publish the repos, add commit hashes and the `commitof` pins (the preamble has none; `\src` prints plain File:line), recount lines
11. §Availability: LEAN-verification folder name `PaperH` and its contents
12. §Availability: run the name-gate script against the published REQUIRED lists
13. Bibliography: DOI of Paper G

## Novelty positioning (as written)
- **Reproofs with credit (marked R in the table):**
  - Euler OI², R ≥ 2r and excircle Euler (wwylele 2026-01-27; PR #44230 2026-09-26; atlas-lean 2026-10-05)
  - Ptolemy's inequality (Mathlib 2022)
  - the Erdős–Mordell inequality and key lemma (plby 2026-05-07; lean-genius 2026-06-19). The paper claims only the mild closed-triangle, any-dimension extension.
  - Napoleon (AFP Aug 2026; Tanrıkolu; ShadowBench 2026-06-12; atlas-lean 2026-10-05; our own Paper A)
- **Partial prior art:** Weitzenböck and Hadwiger–Finsler, which exist only in algebraic Heron form (Compfiles; lean-genius). The paper claims only the geometric packaging.
- **"No earlier formal proof found":**
  - the equality case of Euler's inequality
  - Gerretsen and Kooi
  - OG², OH², IG²
  - Neuberg–Pedoe with its equality case
  - the Leibniz minimum and the isoperimetric inequality, with equality cases
  - a proof of the Erdős–Mordell equality case
  - Barrow
  - Fermat–Torricelli existence and minimality
  - the Ptolemy equality characterisation
  - the Fermat–Napoleon lines (Thm 20 (i)–(iv))

## Open questions for the editor
1. **Cross-build digests.** I verified the Mordell digest agreement myself. For euler and fermat, the paper states only the PASS counts you gave on arm64 and does not claim digest equality. Should I add the digests?
2. **Tamper count for paperh_fermat.** The brief says "all rejected"; tamper.sh has 9 default tests (5 generic + falsehyp, falsehyp2, falsehyp3, falsestmt). The paper says 9 of 9. Please confirm from the log.
3. **The arm64 machine is macOS in Paper G.** I wrote only "an arm64 machine". Please confirm the OS if you want it stated.
4. **"Independent" proofs of Euler.** paperh_euler adapts bridges from our own Blundon development (cited as Paper D). I found no sign in the sources that wwylele or PR #44230 were used, but PROGRESS.md was not read. Please check it before calling the work independent.
5. **SCOUT was only partly re-run.** The Napoleon/Fermat–Napoleon search was not repeated in SCOUT. I checked only the AFP page, the atlas-lean file and a GitHub code search (`fermat napoleon`, `torricelli` in Lean found nothing relevant). The Isabelle Napoleon entry and the HOL Light sources were not searched for the Fermat-point concurrence.
6. **Unverified Paper G numbering.** The cite to Paper G (as `paperG`) is unverified until its DOI exists.
7. **Possibly redundant hypothesis.** `kooi_of_quartic` may not need `2r ≤ R`. The paper mentions this as a remark.
8. **Mordell repository commit.** paperh_mordell on arm64 has no commits yet ("does not have any commits yet"). The euler and fermat repos have local commits "H1 complete" / "H4 complete" (90c1950 / 0225b4d; the euler HEAD message says H1, but the tree contains H3 files, so the H3 work may be uncommitted). Please commit before publishing.

DONE
