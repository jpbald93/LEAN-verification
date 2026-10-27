# Paper G: prior-art re-run (live web + GitHub)

- **When:** 2026-10-27, 12:43–13:50 UTC. Single inline session, no subagents. Read-only: `paperg.tex` was not edited.
- **Baseline:** `SCOUT.md` (sweep of 2026-10-22/24) and `paperg.tex` §"Related work and prior art" (lines 516–561).
- **Cut-off used for "predates":** 2026-10-26.
- **Tools:** `gh` 2.x (authenticated), GitHub REST `search/code` and `search/issues`, shallow clones at HEAD, WebSearch, WebFetch, curl, and the Wayback Machine (HAL and unistra.fr refused connections from this host, so archived copies were used).

## VERDICT: CHANGE NEEDED (citation and wording only; no claim about the Lean results is defeated)

- **Lean: no change.** No Lean formalisation of any of our statements was found, in Mathlib, in open or merged PRs, or anywhere on GitHub. The only Lean partial is still the lean-genius file the paper already cites.
- **Non-Lean: one new relevant hit, which the paper must cite.** Narboux & Braun, *Towards a Certified Version of the Encyclopedia of Triangle Centers*, Math. Comput. Sci. 10 (2016) 57–73, doi:10.1007/s11786-016-0254-4, plus its "Certified ETC" website with Coq files.
  - It works in Coq, with points defined by ETC barycentric/trilinear formulas in homogeneous coordinates, and proves facts with `field`.
  - It proves "X(1) is the complement of X(8)", which is our Nagel-line ratio N−G = 2(G−I) in barycentric form. It also proves X(10) = complement(X(1)), the Spieker centre's position on the Nagel line, and X(20) = anticomplement(X(4)), the de Longchamps point as the orthocentre-image under the anticomplement map. It proves X(6) = isogonal conjugate of X(2) as well.
  - All of these are *algebraic* forms (barycentric formulas, no tie to geometric incentre, contact points or angles), so the classification is **PARTIAL**. It still contradicts the current sentence in §Related work, "In GeoCoq and the Coq high-school geometry library … we found no Nagel, Gergonne, Spieker, symmedian … results there". That sentence is literally true about GeoCoq, but it leaves the reader thinking no Coq work covers these points.
  - This hit predates 2026-10-26 by ten years.

## Exact queries run

### A. mathlib4 PRs (`gh search prs --repo leanprover-community/mathlib4 <term> --limit 30`)
Terms: `nagel`, `gergonne`, `spieker`, `longchamps`, `anticomplementary`, `symmedian`, `lemoine`, `brocard`, `droz`, `isogonal`, `nine-point`, `incenter`, `excenter`, `touchpoint`, `medial`.
Date-bounded: `"Geometry/Euclidean created:>=2026-10-01"`, `"Geometry/Euclidean merged:>=2026-10-01"`, `"triangle created:>=2026-10-01"`, `"Geometry/Euclidean updated:>=2026-10-20"`.
Raw output: `<work dir>`, `prs2.txt`.

### B. GitHub code search (`gh api -X GET search/code -f q=...`)
- **Per language** `language:Lean|Isabelle|Coq`: `nagel`, `gergonne`, `spieker`, `longchamps`, `anticomplementary`, `symmedian`, `lemoine`, `brocard`, `droz farny`, `DrozFarny`. `language:HOL` is rejected by the API (422), so HOL Light was covered by a `repo:jrh13/hol-light` search instead.
  - All `nagel language:Lean` results (226 items, 5 pages, with text-match fragments) were inspected.
- **All languages** (results filtered to `.lean/.thy/.v/.ml/.miz/.mm/.ftl/.tex`): `nagelPoint`, `nagel_point`, `NagelPoint`, `"Nagel point"`, `"Nagel line"`, `gergonnePoint`, `"Gergonne point"`, `spiekerCenter`, `"Spieker"`, `deLongchamps`, `"de Longchamps"`, `symmedianPoint`, `symmedian_point`, `lemoinePoint`, `"Lemoine point"`, `"Lemoine circle"`, `brocardPoint`, `brocard_point`, `"Brocard point"`, `"Brocard angle"`, `"Brocard circle"`, `isogonalConjugate`, `isogonal`, `anticomplementary`, `antimedial`, `"Droz-Farny"`, `"Nagel"`.
- **Targeted:**
  - Lean: `isogonal language:Lean`, `antimedial language:Lean`, `excentral language:Lean`, `Brocard language:Lean`.
  - File extensions: `Nagel extension:thy`, `{symmedian,nagel,brocard} extension:ml`, `{nagel,symmedian} extension:miz`, `{nagel,lemoine} extension:mm`, `nagel extension:ftl`, `{gergonne,symmedian} extension:v`.
  - Per repository: `{Lemoine,Nagel,Brocard} repo:GeoCoq/GeoCoq`; `{symmedian,Brocard,Nagel,Gergonne,Lemoine} repo:isabelle-prover/mirror-afp-devel`; `{nagel,brocard,symmedian} repo:jrh13/hol-light`; `{Nagel,Brocard} repo:naproche/naproche`; `Lemoine repo:rocq-archive/area-method`; `"Gergonne point" repo:rjwalters/lean-genius`; `X8 Nagel language:Coq`.
- **Repository search:** `gh search repos "triangle centers"`, `gh search repos "ETC coq"`.
- Raw output: `code.txt`, `code2.txt`, `code3.txt`, `nagel_lean.txt` (same directory).

### C. Clones at HEAD, grepped
Grep: `grep -rIil -E "nagel|gergonne|spieker|longchamps|anticomplementary|antimedial|symmedian|lemoine|brocard|droz|isogonal"` over `*.lean`, `*.yaml`, `*.md`.

| Repo | HEAD (date UTC) | Commits since 2026-10-22 |
|---|---|---|
| leanprover-community/mathlib4 (sparse: `Mathlib/Geometry`, `Archive`, `Counterexamples`, `docs`) | `0383cdfb` (2026-10-27 12:01) | 77 |
| facebookresearch/atlas-lean | `ef8178c9` (2026-10-26 12:42) | 591 |
| google-deepmind/formal-conjectures | `c0c53807` (2026-10-27 09:30) | 153 |
| dwrensha/compfiles | `1745e6ce` (2026-10-23 11:05) | 1 |
| rjwalters/lean-genius | `470a7df8` (2026-10-22 15:57) | 1 (= the commit SCOUT already used) |
| GeoCoq/GeoCoq | `87e8f9c` (2026-10-18) | — |
| rocq-archive/area-method | 2020-10-18 | — |

Grepping the full tree at HEAD covers every new commit since 2026-10-22. The mathlib4 `docs/1000.yaml` was also grepped.

### D. Web search (WebSearch tool)
1. `Lean formalization Nagel point Nagel line Mathlib`
2. `formalization symmedian point Lemoine point theorem prover Coq Isabelle Lean`
3. `Brocard point Brocard angle formal proof Isabelle OR Coq OR "HOL Light" OR Lean`
4. `Droz-Farny theorem formal verification proof assistant`
5. `Gergonne point Spieker center formalized proof assistant 2026` (timed out, HTTP 524)
6. `Narboux Braun "Encyclopedia of Triangle Centers" certified Coq`
7. `"Towards a Certified Version of the Encyclopedia of Triangle Centers" Coq nsatz barycentric Nagel`
8. `Narboux David Braun certified Encyclopedia of Triangle Centers Coq source code properties verified`
9. `"encyclopedia of triangle centers" Narboux Braun abstract "Coq" ADG 2014 Coimbra properties checked`

**Caution:** the search backend's snippets were partly unreliable. It gave wrong author lists for the ETC paper and a placeholder arXiv URL (`2310.xxxxx`). Every claim below was therefore checked against primary sources:
- Crossref and Semantic Scholar metadata;
- the paper PDF (HAL `hal-01174131v2`, via the Wayback snapshot of 2020, 18 pp.);
- the Certified ETC website pages and coqdoc pages (Wayback snapshots of 2019-03-20/25).

## Hits table

Classes: SAME = formal proof of one of our statements; PARTIAL; UNRELATED. Every SAME/PARTIAL hit was opened.

| # | Hit | System | Date (earliest public) | < 2026-10-26? | Class | What it actually contains (verified) |
|---|---|---|---|---|---|---|
| 1 | Narboux & Braun, *Towards a Certified Version of the ETC*, MCS 10 (2016) 57–73; HAL hal-01174131v2 (submitted 2016-02-24); an ADG 2014 workshop version is reported by web search but was not verified | Coq | 2014/2016 | yes | **PARTIAL** (Thm nagelline, spieker, delong(iv), symmedian: algebraic form) | Points are records of homogeneous (barycentric/trilinear) coordinates defined from ETC formulas (`Definition X_1 … X_5…`, ">6000 points"). `col` is a 3×3 determinant. Transformations (complement, anticomplement, isogonal/isotomic conjugate, …) are defined *algebraically* (paper §2.4: "we adopt algebraic definitions"). Facts are proved by `field` under automatically generated non-degeneracy hypotheses. Totals: 79 914 facts proved out of 129 158 conjectures. Some Coq files are `Admitted` (e.g. `Lemma_iso_conjugate_292_4124_4564.v`, "Not checked symbolically"). No incircle, excircle, contact points, Euclidean angles or tie to geometric definitions. |
| 1a | Certified ETC page `complement.html` (generated 07/09/15; Wayback 2019-03-25) | Coq | 2015 | yes | PARTIAL → Thm nagelline | "X(1) is complement of X(8): **Coq verified**". Since complement(P) = G − ½(P − G), this is N − G = 2(G − I) for barycentrically-defined I = X(1) and N = X(8). |
| 1b | same page | Coq | 2015 | yes | PARTIAL → Thm spieker | "X(10) is complement of X(1): Coq verified" (Spieker on the Nagel line; with 1a this gives X(10) = mid(X(1), X(8)) algebraically). Not the "incentre of the medial triangle" form we prove. |
| 1c | same page | Coq | 2015 | yes | PARTIAL → Thm delong(iv) | "X(4) is complement of X(20): Coq verified", i.e. X(20) = anticomplement(X(4)) by barycentric formula. Does not cover delong (i)–(iii), the orthocentre of the anticomplementary *triangle* as a geometric object. Note: `medial_triangle_is_complement_triangle_of_ABC` is proved. |
| 1d | `isogonal_conjugate.html` | Coq | 2015 | yes | PARTIAL (weak) → Thm symmedian | "X(6) is isogonal conjugate of X(2): Coq verified", with the isogonal conjugate *defined* as (1/p : 1/q : 1/r) in trilinears. No angle equalities. |
| 1e | coqdoc `pedal_triangle.html` | Coq | 2015 | yes | UNRELATED to Thm pedal | Pedal-triangle lemmas only for X(4), X(3), X(1). Nothing for X(6) as centroid of its pedal triangle. |
| — | Brocard points, Brocard angle/circle, Lemoine circle, Droz-Farny in Certified ETC | Coq | — | — | not found | Brocard points are not triangle centres, so they are absent from ETC. Collinearity pages (e.g. the Brocard axis X(3), X(6), X(182)) were not archived. **Gap.** |
| 2 | rjwalters/lean-genius `proofs/Proofs/CevasTheoremOQ04OQ04OQ02.lean` | Lean | 2026-06-25T14:03Z (only commit) | yes | PARTIAL (already cited) | Unchanged since SCOUT; HEAD is still `470a7df`. |
| 3 | rjwalters/lean-genius `CevasTheoremOQ02OQ01OQ03.lean` (first 2026-04-04, last 2026-06-23) and `CevasTheorem.lean` (first 2025-12-27, last 2026-07-17) | Lean | 2025-12/2026-04 | yes | UNRELATED | The word "symmedian" appears only in docstrings ("Symmedian point (α_D = \|AB\|², …)", "Symmedians: Meet at symmedian point"). There is no theorem about K. The 18 theorems are 1-D division-ratio identities. |
| 4 | rocq-archive/area-method `area_coords_constructions.v` (`Definition is_Lemoine`) | Coq | file added 2009-08-10 | yes | UNRELATED | Definition by area ratios, used only in unfolding tactics. No theorem about the Lemoine point. |
| 5 | GeoCoq HEAD `87e8f9c` | Coq | — | — | none | 0 matches. The grep hits in `circumcenter.v`, `legendre.v`, etc. were on unrelated words. |
| 6 | AFP mirror, HOL Light, Naproche (GitHub code search) | Isabelle / HOL / Naproche | — | — | none | All `nagel` hits are author names (Sternagel, Nagele). All other terms: 0. |
| 7 | Mizar/Metamath (`extension:miz`, `extension:mm`) | — | — | — | none | 0, or unrelated `.mm` Objective-C files. The `.miz` extension may not be indexed by GitHub (gap; SCOUT's local MML grep stands). |
| 8 | formal-conjectures `BrocardProblem.lean`, `BrocardConjecture.lean`, `Lemoine.lean`, `ErdosProblems/398.lean`, `976.lean` | Lean | various | yes | UNRELATED | Number theory (n!+1=m², Lemoine's conjecture, Nagell). |
| 9 | atlas-lean `WantedExt/NumberTheory/{LemoineVerification,BrocardRamanujan*,NagellLjunggren*}Wanted.lean` | Lean | ≤2026-10-26 | yes | UNRELATED | Number theory. Also, no geometry file in `MathlibExt/Geometry/Euclidean/` mentions any of our centres (it has EulerOI, Feuerbach, ConwayCircle, Routh, …). |
| 10 | Paul3435/open-math-lab `ProofLab/BrocardFactorialSquare.lean` | Lean | — | — | UNRELATED | Brocard's factorial problem. |
| 11 | LeanTriathlon / CBirkbeck AINTLIB / cadamcat catalan / LeanPool (Nagell–Lutz, Ramanujan–Nagell) | Lean | — | — | UNRELATED | The term "nagel" only appears inside "Nagell". |
| 12 | mathlib4 `docs/1000.yaml` @ `0383cdfb` | — | — | — | UNRELATED | The only hit is Q3527132 "Nagell–Lutz theorem". No triangle-centre entries. |
| 13 | mathlib4 PRs since 2026-10-01 in `Geometry/Euclidean` | Lean | see below | yes | UNRELATED | #44772 / #44781 (Incenter → `Incenter/Basic` move, merged 2026-10-12; **check that our imports still compile against the new path**, a deprecated module exists). #44794 (SouthPole, merged 2026-10-14). #44462 (corner simplex). #44822 (inversion). #44721 (hyperplane distance). Still open: #44230 (Euler OI, updated 2026-10-17), #44236 (Feuerbach), #44060, #31981. **0 PRs** for any of nagel, gergonne, spieker, longchamps, anticomplementary, symmedian, lemoine, brocard, droz, isogonal. |
| 14 | compfiles @ `1745e6ce` | Lean | — | — | none | 0 matches (only incenter in `Usa1988P4.lean`). |
| 15 | TeX/docs hits (tkz-euclide, planetmath, evanchen handouts, MO-Problem-Journal) | — | — | — | UNRELATED | Informal mathematics or drawing packages. |

## Text to change in `paperg.tex` (suggested; not applied)

**(1) §Related work, "Other systems" paragraph (around lines 536–541).** Replace

> In GeoCoq and the Coq high-school geometry library the Euler line is
> formalised; we found no Nagel, Gergonne, Spieker, symmedian, Brocard, Lemoine-circle or Droz-Farny
> results there, nor in the Archive of Formal Proofs, the HOL~Light distribution or the Mizar
> Mathematical Library.

with

> In GeoCoq and the Coq high-school geometry library the Euler line is
> formalised; we found no Nagel, Gergonne, Spieker, symmedian, Brocard, Lemoine-circle or Droz-Farny
> results there, nor in the Archive of Formal Proofs, the HOL~Light distribution or the Mizar
> Mathematical Library. Closest to this paper is the certified version of Kimberling's encyclopedia
> by Narboux and Braun \cite{certifiedetc}, in Coq. There, triangle centres are defined by their
> barycentric or trilinear coordinates and transformations such as the complement and the isogonal
> conjugate by formulas; facts are proved by field normalisation under generated non-degeneracy
> conditions. Among some 80\,000 verified facts are that $X(1)$ is the complement of $X(8)$ and
> $X(10)$ the complement of $X(1)$ (the Nagel line with its ratio, and the Spieker centre on it),
> that $X(20)$ is the anticomplement of $X(4)$, and that $X(6)$ is the isogonal conjugate of $X(2)$.
> These are algebraic forms of parts of Theorems~\ref{thm:nagelline}, \ref{thm:spieker},
> \ref{thm:delong}(iv) and~\ref{thm:symmedian}: the points are not tied to incircle or excircle
> contact, to an incentre defined by equal distances, or to Euclidean angles, which is what our
> statements add. We found no Brocard-point, Brocard-angle, Lemoine-circle or Droz-Farny results
> there.

**(2) §Related work, end of "Earlier Lean work" paragraph (line 533).** Replace

> We found no Lean formalisation of the other theorems of this paper.

with

> We found no Lean formalisation of the other theorems of this paper; for algebraic Coq forms of some
> of them see the next paragraph.

**(3) §Related work, "How the search was done" paragraph (lines 543–551).** Replace the sentence from "Two gaps matter:" through the `\PH{…}` with

> A second sweep on 2026-10-27 repeated the GitHub searches at the then-current heads of Mathlib,
> \lean{atlas-lean}, \lean{formal-conjectures}, Compfiles and \lean{lean-genius}, searched mathlib4 pull
> requests opened or merged since 2026-10-01, and added general web search, which found the Coq work
> \cite{certifiedetc}. Remaining gaps: ProofAtlas was checked only through its sitemap (752 URLs), not
> by reading its pages, and only archived copies of the certified-encyclopedia website were available,
> so we could not inspect its collinearity lists. Our statements of novelty are subject to these gaps.

**(4) §What is not claimed, the Nagel/Gergonne item (lines 729–732).** Replace

> Our claim is to the statements with Mathlib's contact points, incentre and
> centroid.

with

> Nor do we claim the first formal proof of the Nagel line or of the Spieker centre's position on it in
> barycentric form, which is among the Coq facts of \cite{certifiedetc}. Our claim is to the statements
> with Mathlib's contact points, incentre and centroid.

**(5) Bibliography: add**

```latex
\bibitem{certifiedetc}
J.~Narboux and D.~Braun,
Towards a certified version of the Encyclopedia of Triangle Centers,
\emph{Mathematics in Computer Science} \textbf{10} (2016), 57--73,
\doi{10.1007/s11786-016-0254-4}; website \url{http://dpt-info.u-strasbg.fr/~narboux/CETC/}
(consulted via the Internet Archive, snapshots of March 2019).
```

Use `\url{https://doi.org/...}` instead of `\doi` if the latter macro is not loaded.

**(6) Limitations item "Prior art" (line 761).** No change is needed if (3) is applied.

**Separate engineering note (not prior art).** mathlib4 #44772 (merged 2026-10-12) moved `Mathlib/Geometry/Euclidean/Incenter.lean` to `Incenter/Basic.lean`, leaving a deprecated module behind. This does not affect the pinned revision, but any re-pin will trigger deprecation warnings.

## Remaining gaps
- **HAL and unistra.fr were unreachable (ECONNREFUSED).** The paper and website were read through Wayback snapshots (2019/2020). The Certified-ETC Coq tarball and the per-point collinearity pages were not archived, so the Coq proof of "X(1) is complement of X(8)" was not opened. Only the site's "Coq verified" status and the generic `complement` definitions and lemmas (coqdoc) were seen. Some site lemmas are `Admitted`; the "Coq verified" label is taken at face value.
- **ProofAtlas** was not re-crawled; still sitemap only.
- **WebSearch quality:** snippets were partly fabricated or garbled. Only primary sources were relied on.
- **Mizar:** GitHub does not appear to index `.miz`, so the SCOUT local MML grep stands.
- **Time box:** about 67 min used of 75.
