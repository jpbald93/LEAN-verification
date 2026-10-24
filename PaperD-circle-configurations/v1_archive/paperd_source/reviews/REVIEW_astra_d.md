VERDICT: MAJOR REVISION — 0 BLOCKER, 11 MAJOR, 8 MINOR issues.

# Independent layer-12 referee report

Reviewed `paperd.tex` (623 lines), the eight supplied Lean source developments and their gates, and every supplied report in `reports/`. I also consulted the local `REFAUDIT.md` for bibliographic scope. This is a read-only statement/evidence review, not a fresh Lean build or a rerun of the numerical experiments. No input file was modified. Known red placeholders are not counted as defects; assertions outside them that already claim their intended outcomes are counted.

Paths below are relative to `AFM/PaperD/`; paper line numbers refer to `paperd.tex`. A report assertion is treated as evidence that its author reported a check, not as a substitute for an archived numerical witness or kernel certificate.

## MAJOR issues

### M1. The Clifford statements slide from existence/explicit witnesses to unspecified chosen points

**Paper:** 181–185, 195–199; also 176–178.

**Code:** `src/clifford/Clifford/Basic.lean:381–389`; `src/clifford/Clifford/Third.lean:457–473,543–565,806–824`.

Theorem 1 only asserts existence of a common point. Theorem 2 then says “let P_k be the point of Theorem 1,” which reads as applying to the common point chosen from that existential assertion. The declaration cited in its heading, `clifford_two`, instead jointly **exists-quantifies** all five points together with the incidence and circle-or-line properties. The explicit theorem proves the property for five particular values of `cliffordPoint`. No uniqueness theorem for the geometric common point is supplied.

Theorem 3 similarly speaks about circles through “three of” the five points, whereas `clifford_three` uses specific `cliffordPoint` values and six specifically indexed triples, listed at Third:806–811. The source does not directly quantify over arbitrary common-point choices or arbitrary defining triples. These stronger readings may be geometrically recoverable, but that recovery is not the cited declaration.

**Fix:** Define `P_T := cliffordPoint(c_T)` in the statement, explicitly transporting coordinates back from M=0. State Theorem 2 for those points and cite `clifford_two_explicit` plus `cliffordPoint_mem_gams`; alternatively use exactly the joint existential formulation of `clifford_two`. For Theorem 3 specify the six defining triples, or supply the uniqueness/permutation/circle-independence bridge that licenses “any three.” Do not use “the point” to import unproved uniqueness.

### M2. `IsGCircle` is not exactly “a circle or a line” in the nondegenerate/inversive sense advertised

**Paper:** 122–123, 188–191, 210–218, 472–473.

**Code:** `src/cliffordchain/Clifford/Clean.lean:135–158,165–184,230–255`.

`IsGCircle X` permits `X = Metric.sphere o r` for **any real r**, with no positivity condition. Thus it permits the empty set for negative r and a singleton for r=0, not just genuine circles and lines. This is not merely a hypothetical unused allowance: Clean:145 constructs a radius-zero sphere when all five Miquel points coincide. The `Chain` predicate is also existential at each recursive branch; it does not assert a unique coherent construction at every level.

Consequently “defines the whole chain” needs a degeneracy/quantifier qualification, and “exactly Clifford's statement read in the extended plane” is too strong: the code neither introduces the point at infinity nor uses only the ordinary nondegenerate generalized circles of inversive geometry. The reported all-coincident case does not pick out a unique level-5 circle.

**Fix:** Describe this as an **existential incidence-chain predicate allowing degenerate spheres**; disclose singleton and formally empty spheres, noting that the required incidences exclude empty witnesses in the relevant proved cases. If a genuine generalized-circle formalization is intended, require r>0 and handle coincident lower-level points separately. Replace “exactly ... extended plane” by “the finite Euclidean circle-or-line conclusion corresponding to the usual generalized-circle formulation, under our stated hypotheses.” No need to claim a code defect in the proved n=4,5 results.

### M3. The universal Lester counterexample claim is false: collinearity alone does not refute `Concyclic`

**Paper:** 265–268, table row 359; related abstract claim 65–67.

**Code:** `src/lester/Lester/Basic.lean:40–63`; `src/lester/Lester/Bridge.lean:90–97`.

The paper says that **an isosceles, non-equilateral triangle** makes the four points collinear and therefore makes `Concyclic` false. Mathlib applies the predicate to a **set**: repeated points disappear, and a two-point set is concyclic. There are exceptional non-equilateral isosceles triangles where this matters.

An exact counterexample to the paper's explanatory assertion is

- A=(0,1/√3), B=(-1,0), C=(1,0);
- circumcentre O=(0,-1/√3);
- nine-point centre N=A;
- the outward-apex Fermat point is F1=A;
- the inward-apex Fermat point is F2=O.

The incidences follow directly from the apex formulas at Basic:31–47 (I checked the coordinate identities symbolically). The four-point set is `{A,O}`, which lies on the circle centred at (0,0) of radius 1/√3. This triangle is non-equilateral and isosceles, and its apex angle is 120 degrees.

`verify_john.md:13` reports an isosceles numerical check but gives neither a universal proof nor a distinctness bound. It cannot support the universal inference in the paper.

**Fix:** Say “The scalene hypothesis cannot simply be dropped: there are non-equilateral isosceles triangles for which at least three of these centres are distinct and collinear.” Supply one such witness and the distinctness check. Do not say every excluded isosceles triangle falsifies the conclusion. The actual scalene Lean theorem is not affected.

### M4. The Kosnita exceptional locus is not uniformly three distinct parallel lines

**Paper:** 306–313, table row 361.

**Code:** `src/kosnita/Kosnita/Basic.lean:49–55,180–191`.

The paper generalizes three numerical samples to the whole locus `AB²+BC²+CA²=5R²`, saying that the three lines are pairwise parallel and distinct. On part of this locus, a purported line is not even defined by two distinct points.

For an exact example take the unit circumcircle with

- O=(0,0), A=(1,0), B=(1/2,√3/2), C=(1/2,-√3/2);
- Oa=A, Ob=(1/2,-√3/6), Oc=(1/2,√3/6).

All four triangles ABC, OBC, OCA, OAB are nondegenerate; the displayed subsidiary centres satisfy the required equidistances; the side-square sum is 5. But `AOa` has identical endpoints, while `BOb` and `COc` are the **same** vertical line, not distinct parallel lines. These identities were checked symbolically against the source's equidistance model.

The Lean conclusion is a conjunction of three `Collinear` predicates. With hS present, the nonzero-denominator certificate and its relabellings prevent zero line directions, so this does **not** invalidate the quoted theorem. It does invalidate the claimed universal description of its excluded boundary.

**Fix:** Say that removing hS admits configurations with distinct parallel lines, and exhibit the reported examples as such; additionally acknowledge other degeneracies on that locus. If retaining a universal characterization, state and prove its extra distinct-line hypotheses. “Necessary to retain an unrestricted affine theorem” is defensible; “every point of this locus has three distinct parallel lines” is not.

### M5. “Each development” independently numerically reverified, and “every trial” negative controls, contradict the supplied evidence

**Paper:** 420–424, 446–447.

**Evidence:** `verify_john.md:3–69`; `verify_jack_clifford.md:13–34`; `verify_jack_crosscheck.md:3–46`.

The supplied independent numerical reports cover Clifford, cliffordchain, Lester, Thébault, fivecircles and Kosnita. They do **not** contain numerical or independent statement-fidelity experiments for Blundon or Steiner–Lehmus. The battery reports for these two are not numerical experiments.

Moreover `verify_john.md:50` explicitly reports the fivecircles negative control as **999/1000 violated**, not every trial. Also its reported worst positive residual is **5.3×10^-47**, which is outside a literal interval bounded above by 10^-47 in paper:423. The reports generally support the order of magnitude, not that exact endpoint interval.

For Steiner–Lehmus in particular, random generic triangles do not satisfy the equal-bisector premise; a separate equal-bisector witness would be required to substantiate “every hypothesis” at 446–447. No such witness is in these files.

**Fix:** List exactly the six developments covered and give per-result trial counts, precisions, residuals, and negative-control success counts. Explicitly disclose 999/1000 and investigate/classify the remaining trial. Remove the universal numerical satisfiability claim or obtain and archive checks for the two companions. Use “worst residual at most 5.3×10^-47 among the reported main-result experiments” if that is the intended summary.

### M6. Both-platform and exact-source identity claims lack the stated receipts

**Paper:** 126–127, 412–418, 426–429, 440–443.

**Evidence:** all `john_*.md`, `jack_partial_clifford_*.md`, `verify_*.md`.

The available receipts do not establish that **every** development passed gates on **both** platforms. They document seven John batteries (not the original `clifford`) and a Jack Clifford battery; the independent Jack crosscheck adds cliffordchain and Thébault. The supplied reports do not document the opposite-platform gate runs for Blundon, Steiner–Lehmus, Lester, fivecircles or Kosnita, nor John's gate for the original Clifford development.

No supplied report contains a SHA-256 source manifest or an actual comparison supporting “sources identical (by SHA-256).” The inventories' short identifiers are not two-machine per-file digest comparisons. The snapshot contains source/gate files but no `lean-toolchain` or Lake manifest; the single explicit Lean v4.33.1/pin assertion in `verify_jack_crosscheck.md:1` concerns its two repositories, not an eight-repository lockfile audit.

The resumed Jack report establishes a corrected result of 0 contradictions, but does not document the claimed **24** prior OOM false positives, their exit-status classification, or a 24-case rerun. Its header mentions an OOM fix; that does not verify all the specific narrative details at 440–443.

**Fix:** Add a repository × platform matrix linking actual receipts, plus per-file hashes and toolchain/Mathlib locks. Until then state only the runs documented here. Archive the OOM incident/rerun log if retaining its precise counts. The `confirm both-machine figures` placeholder does not justify an unconditional preceding sentence.

### M7. Conclusion-mutation coverage excludes most main theorems, despite “each theorem's conclusion”

**Paper:** 431–437, 460–461.

**Evidence:** each battery's “no mutants generated (manual look)” list.

The total 490/489 is arithmetically correct, but the coverage prose is false. No conclusion mutants were generated for:

- original Clifford's `clifford_one`, `clifford_two`, `clifford_two_explicit`, `clifford_three` (`jack_clifford_summary.md:74`);
- cliffordchain's `clifford_one`, `clifford_two`, `clifford_two_clean` (`john_clifford_j_*.md:68`);
- `Lester.lester` and `lester_core` (`john_lester_*.md:47`);
- `Thebault3.sawayama_thebault` (`john_thebault3_j_*.md:53`);
- `Fivecircles.fivecircles` (`john_Fivecircles_*.md:41`);
- `Kosnita.kosnita` (`john_Kosnita_*.md:43`).

These declarations are at the exact source anchors cited in the paper. The generated mutants largely test auxiliary algebra, not every main statement. A timeout also establishes only failure to complete under a resource bound, not falsity of the mutated proposition or successful semantic sensitivity.

**Fix:** Say “The mutation generator produced 490 mutants of the supported conclusion forms,” give a main-theorem coverage table, and explicitly list unmutated main statements. Retain 455 type/error rejections, 34 heartbeat-limited runs, and one surviving weakening as distinct categories. Do not summarize this as showing that all proofs “depend on their conclusions.”

### M8. Failure to find contradiction is promoted to consistency; the satisfiability total mixes unlike evidence

**Paper:** 438–447, 460–463.

**Evidence:** battery verdict tables; e.g. `john_clifford_j_*.md:90`, `john_lester_*.md:69`, `jack_clifford_summary.md:13–15`.

“No contradictory hypothesis set was found” is supported. “All 24 were then consistent” and “have consistent hypotheses” are not consequences of unsuccessful automated contradiction probes. The paper itself acknowledges 101 unresolved satisfiability obligations.

The **196/297** count is correctly copied but should not be read as 196 independently instantiated geometric hypothesis sets. The reported certified total includes hypothesis-free binders and closed declarations: cliffordchain contributes 67, of which only **11** are categorized as having hypotheses (54 hypothesis-free binders and 2 closed); Lester contributes 20, of which only **3** have hypotheses (8 hypothesis-free binders and 9 closed). Both closed `CliffordChain` theorems already prove propositions whose per-configuration existence is conditional on `GenPosN`; counting such a closed theorem as certified does not exhibit any general-position centres.

**Fix:** Replace “consistent” with “the corrected probes found no contradiction.” Preserve the unresolved count and disaggregate certified results into with-hypotheses witnesses, hypothesis-free declarations and closed propositions, as the reports already do. State that neither this probe nor its aggregate success count certifies satisfiability of every main geometric premise set.

### M9. Ablation is described at finer granularity than the tests support

**Paper:** 448–456.

**Code/evidence:** `src/cliffordchain/Clifford/Basic.lean:586–601,643–663`; `src/lester/Lester/Basic.lean:40–47,60–62`; `src/lester/Lester/Proof.lean:139–144,328–333`; `john_clifford_j_*.md:74`; `john_lester_*.md:53`; the two Jack battery reports.

“Every hypothesis is used” overstates binder-level ablation. `GenPos4/GenPos5` bundle many geometric conditions into one argument. Removing `h : GenPos5 ...` does not test whether every field is needed. Likewise the Fermat predicates bundle three line memberships each; the actual Lester proof at Proof:330,333 passes only `.1` and `.2.1` to `fermat_on`, not the third membership. Thus “all tested binders were needed by the unchanged proof” and “all mathematical hypothesis components are used” are materially different claims.

The supplied Jack reports also end before an ablation-result section. They do not substantiate the completed original-Clifford ablation claims already written outside the running-work placeholder. Direct source inspection supports the named unused n-hypotheses, but not the claimed completed experimental coverage.

**Fix:** Report the granularity and number of **tested binders**, not “every hypothesis.” Explicitly exclude fields/conjuncts from that claim unless separately tested. Cite a completed or partial ablation receipt for the original Clifford numbers; distinguish source inspection from an executed ablation experiment. Failure of an unchanged proof after deletion is not logical necessity.

### M10. Text pre-commits to unfinished linter, blind and hand-review outcomes

**Paper:** 457–458, 462–466, 476, 480–482.

**Evidence:** no Clifford linter output in the Jack reports; layer 13 and the author's statement review remain placeholders at 368–370 and 465–466.

“The unused-variable linter reports no warnings in any library file” includes Clifford before its result is available. The concluding sentence says the interpretation gap “is addressed ... by the blind re-formalisation ... and by the hand check,” while those checks have no results. “Blind checks establish equivalence of statements” at 476 similarly presupposes a successful outcome. The authorship statement that the author “reviewed the paper” should not be allowed to imply the unfinished per-statement hand verification.

**Fix:** Limit the linter sentence to the seven documented libraries. Use future/conditional language for layer 13 and the hand check until completed, and distinguish general author editorial review from the specific quoted-statement audit. This issue concerns the unconditional surrounding text, not the presence of the placeholders.

### M11. Novelty wording becomes a universal absence assertion broader than the search

**Paper:** 68–72, 90–92, 374–392.

**Evidence:** `reports/priorart.md:49–67`; local `REFAUDIT.md` entry `leangenius` and material finding 4; paper's own bibliography at 611–614.

“We found no ...” is a properly bounded search result. But “the geometric theorem does not [have a Lean proof]” and “The only formal proofs of the circle theorems nearby are ... three-circle Miquel” turn that into an unrestricted absence assertion. “Nearby” is undefined; the paper itself cites Paper B's formal proofs of Feuerbach and Brahmagupta, so the literal nearby-circle claim is untenable.

The Related-work evidence should also not equate all three Miquel controls at the level of existence: the local reference audit specifically says the lean-genius PR proves conditional incidence (a point on two circles lies on the third), **not existence** of a common point. That is relevant when comparing “complete formal proof” claims.

**Fix:** Throughout use “we found no complete geometric formalization in the sources and search scope listed in Section ...”. Replace “the only ... nearby” with a precise statement about the prior-art hits for the named target theorems. Describe lean-genius as a conditional-incidence Miquel formalization, separately from AFP's existence statement. This does not require abandoning the qualified novelty claim.

## MINOR issues

### m1. Eight developments, not seven; make the counting convention explicit

**Paper:** 125–139.

There are **eight** development directories, despite seven table rows (Blundon and Steiner–Lehmus share a row). All file/line figures themselves match the supplied `.lean` files exactly. They include root import files, blank lines and comments and are physical line counts, not proof-size or token counts; some polynomial certificates occupy extremely long individual lines.

**Fix:** Change “seven” to “eight” and define “files/lines” as library `.lean` files including root imports, physical lines including comments/blanks, excluding Mathlib and scratch files. Total: **20 files, 4,353 lines**.

### m2. “Twenty non-collinearity hypotheses” is a count error

**Paper:** 452–455.

**Code:** `src/clifford/Clifford/Third.lean:457–471`.

`clifford_two_explicit` has **ten** pairwise second-intersection nonzero hypotheses and **ten** non-collinearity hypotheses, not twenty non-collinearity hypotheses. Five of the latter are named unused in the paper.

**Fix:** “five of its ten non-collinearity hypotheses (among twenty geometric hypotheses in total).”

### m3. The fivecircles exclusion table omits within-family coincidences

**Paper:** 65–66, 347–358.

**Code:** `src/fivecircles/Fivecircles/Basic.lean:383–385`.

The theorem body correctly states injectivity of A,T,M, but the purported exclusion inventory only lists coincidences **between** the three families. It omits coincidences **within** each family, notably `hM : Injective M`.

**Fix:** Say “any coincidence among the fifteen labelled A-, T-, and M-points,” covering both within-family and cross-family distinctness. This is a table-completeness defect, not a missing hypothesis in Theorem 5.

### m4. “Every declaration named” is broader than the gate lists

**Paper:** 144–148 (compare the explicit `\decl` convention at 24–25).

**Code:** gates' REQUIRED lists; examples `src/clifford/Clifford/Basic.lean:194,309`; `src/cliffordchain/Clifford/Clean.lean:156,165,184`; `src/kosnita/Kosnita/Basic.lean:49`.

All actual content `\decl{...}` names occur in the appropriate gate lists. But numerous declarations named with `\lean`, or named mathematically, do not: `secondInter`, `cliffordPoint`, `IsGCircle`, `Chain`, `CliffordChain`, `CliffordNondeg`, `cert_den`, `five_NN`. The unqualified sentence is false.

**Fix:** “Every declaration typeset with `\decl` is in its development's REQUIRED list.” Explain that dependencies are covered transitively by the listed main theorem's axiom audit; not every named definition is separately queried. Also say the gate runs in strict/default mode, since the scripts explicitly provide a permissive `SCAFFOLD=1` mode.

### m5. The fivecircles proof is materially an angle-addition certificate, not solely the claimed polynomial certificate method

**Paper:** 110–116, 251–253.

**Code:** `src/fivecircles/Fivecircles/Basic.lean:8,42–56,167–343`, especially 215–218 and 339–342.

`Fivecircles.core` does not establish its central result by one polynomial ideal-membership certificate in Cartesian coordinates. It converts cross-ratio numerator vanishing into equalities of doubled arguments in `Real.Angle`, then performs a sequence of `linear_combination (norm := abel)` angle-addition certificates. Polynomial coordinate bridges occur around this argument. The final theorem does correctly use five cyclic relabellings.

**Fix:** Qualify the method paragraph: polynomial certificates for most developments, with an additive directed-angle/cross-ratio argument for fivecircles. Replace “one certificate” by “one core angle-chasing lemma, reused under cyclic relabelling.”

### m6. Two small source-anchor/model descriptions are inaccurate

**Paper:** 155–160, 162–163.

**Code:** `src/clifford/Clifford/Basic.lean:194,197–204,240–257`.

Distinct centres alone do not give a **distinct** second intersection: c1=1,c2=2 are tangent at 0 and the formula gives P12=0. The later theorem excludes this correctly, but the introductory sentence says two distinct-centre circles meet “at 0 and at a second point.” Also the anchor Basic:203 is `gam`, not the explicit circumcentre formula, which is at Basic:197 (with generic formula at 57).

**Fix:** Call it the algebraic second-intersection candidate, distinct from 0 under the transversality hypothesis; cite Basic:197 or 57 for the circumcentre formula and 203 for Γ.

### m7. Historical/citation wording exceeds what the cited older books can support

**Paper:** 89–92, 265, 398–404.

Lester's 1996 discovery cannot have a “long history ... of ... computer-algebra proofs” evidenced by the grouped 1929, 1970 and 1988 references. The Lester date and article are plausible and bibliographically verified locally, but the supplied reports do not verify the additional **“found ... by computer”** historical detail. The broad assertion that non-kernel machine proofs “typically” have generated rather than stated non-degeneracy conditions is not documented by the prior-art report's example-file findings; for Hasclid, `priorart.md:42` explicitly says success was not checked.

**Fix:** Separate historical discussion by theorem and cite Lester/Yiu for Lester; provide a pinpoint historical source for “by computer” or omit those words. Attribute the behavior of older automated methods to a specific method/source rather than extrapolating from discovered example files. Keep Hasclid described as an example/proof attempt, not an established successful proof.

### m8. Search-method limits are slightly overstated/underreported

**Paper:** 381–396.

**Evidence:** `reports/priorart.md:62–65`.

AFP coverage was a full mirror plus a check of the **live front page for newer entries**, not a direct query of the live search/index. The GitHub rerun used unqualified queries, with a reported ceiling of about **50 returned results per query**; language-qualified searches were abandoned after rate limiting. The paper only states the more generic repository-index limitation. Its main corpus counts (1045 AFP entries, 1500 Mizar articles) do match the report.

**Fix:** Describe the AFP substitute accurately and add the GitHub result-cap/query restrictions. No need to repeat the earlier failed searches as though they were the final coverage: `priorart.md` clearly records the paced rerun.

## Theorem-by-theorem statement audit

This covers every theorem environment, including the one environment containing two chain declarations. “Matches” below means the mathematical hypotheses/conclusion match under the paper's stated coordinate identification, not that I reran Lean.

| Paper theorem / lines | Actual source | Result |
|---|---|---|
| Clifford n=4, 169–174 | `clifford/Clifford/Basic.lean:381–388` | Six Pij≠0 and four non-collinearity assumptions; existence of a point on all four Γ. Matches after translating M to 0. No uniqueness asserted in code. |
| Clifford n=5, 181–186 | `clifford/Clifford/Third.lean:543–564`; explicit:457–473 | Ten Pij≠0 and ten triple conditions match. Incidences plus `Cospherical ∨ Collinear` match; chosen-point/existential scope needs M1. `Cospherical` in ℂ gives the intended circle containment (allowing degeneracy). |
| Clifford n=6, 195–200 | `clifford/Clifford/Third.lean:780–824` | Fifteen Pij≠0, twenty triple conditions, six designated-point non-collinearity conditions; Q plus all-five memberships for each of six circles. Matches for the designated explicit construction, subject to M1. |
| Chain n=4 and n=5, 221–223 | `cliffordchain/Clifford/Clean.lean:226–227,245–255` | Exactly `CliffordChain 4` and `CliffordChain 5`. `GenPosN`:177–179; `GenTriple`:Basic:402–403; no hidden `CliffordNondeg` in the clean result. Definition/degenerate-object qualification M2. |
| Five circles, 239–244 | `fivecircles/Fivecircles/Basic.lean:383–388` | All three injectivities, all three cross-family disjointness conditions, cyclic hL and hC, and `Concyclic ∨ Collinear` match exactly. |
| Lester, 258–263 | `lester/Lester/Basic.lean:56–63` | Three pairwise side-length inequalities, supplied outer/inner Fermat points, nine-point centre/circumcentre, and `Concyclic` match. Equilateral-apex definitions are correct by direct inspection; equilateral-distance and nine-point-centre bridges exist. Existence appropriately disclaimed at 274. The defect is the necessity discussion, not this theorem. |
| Sawayama–Thébault, 281–286 | `thebault/Thebault3/Basic.lean:32–38,514–517` | Nondegenerate triangle, strict betweenness, positive radii, distances to both full lines, internal tangency equation, the two strict same-side conditions, and collinearity with Mathlib's incentre match. Existence appropriately disclaimed. Numerical uniqueness at paper:291 should be understood as the 1989 sampled cases of `verify_john.md:32`, not a proved uniqueness theorem. |
| Kosnita, 299–304 | `kosnita/Kosnita/Basic.lean:180–191` | Plane/noncollinearity, circumcentre equidistances, all three subsidiary noncollinearities and hS match. Existential P with three collinearities is the code conclusion; under hS the denominator certificate justifies actual nonzero line directions. Boundary explanation is wrong as in M4. X54 identification is not a formal conclusion of this code. |
| Blundon, 318–323 | `blundon/Blundon/Basic.lean:65–76,147–155` | Real inner-product affine space, genuine `Affine.Triangle`, standard R/r and explicitly defined s; both displayed bounds match. Optimality is attributed historically, not proved by the cited theorem. |
| Steiner–Lehmus, 332–335 | `steinerlehmus/SteinerLehmus/Basic.lean:29–30,112–115` | Noncollinearity, E and F on closed opposite segments (`Wbtw`), two Mathlib unoriented angle equalities, BE=CF, conclusion AB=AC all match. The code is actually as general as a real inner-product affine torsor. Formula and factorization at paper:336–339 agree with Basic:34–41,49–52. |

## Quantitative reconciliation

The following are verified against physical source counts, gate REQUIRED lists and battery JSON summaries. These are **not** claims of two-platform coverage.

| Development | Lean files | Physical lines | REQUIRED declarations | Mutants / rejected | Heartbeat-limited | SAT credited / audited |
|---|---:|---:|---:|---:|---:|---:|
| clifford | 3 | 1271 | 20 | 129 / 129 | 27 | 73 / 103 |
| cliffordchain | 3 | 983 | 14 | 118 / 118 | 2 | 67 / 96 |
| fivecircles | 2 | 428 | 6 | 36 / 36 | 0 | 15 / 20 |
| lester | 4 | 506 | 19 | 82 / 82 | 0 | 20 / 31 |
| thebault | 2 | 559 | 12 | 65 / 64 | 0 | 13 / 28 |
| kosnita | 2 | 249 | 11 | 33 / 33 | 3 | 7 / 11 |
| blundon | 2 | 228 | 5 | 21 / 21 | 2 | 1 / 5 |
| steinerlehmus | 2 | 129 | 3 | 6 / 6 | 0 | 0 / 3 |
| **Total** | **20** | **4353** | **90** | **490 / 489** | **34** | **196 / 297** |

Verified: the lone surviving `sign_neg` mutation is the true weakening `<0` to `<1`; the Kosnita `_hr1/_hr2` ablation findings match its source; all 21 `\src` targets resolve to existing declaration starts, with the circumcentre-description caveat in m6; all actual content `\decl` names are in the applicable REQUIRED lists.

Verified as reported numerical observations, not exact counterexample certificates: Clifford's distinct collinear case (spacing 0.042, residual 5×10^-60) appears in `verify_jack_crosscheck.md:20`; fivecircles' collinear case (spacing 0.52, residual 10^-39) in `verify_john.md:49`; three sampled Kosnita boundary cases in `verify_john.md:67`. These reports do not include the coordinates, scripts' contents, random seeds or exact/interval witnesses in the supplied directory. Archive those artifacts if the paper is to make the exclusion experiments reproducible. Their absence does not erase the reported observations, but the observations do not license universal characterizations such as M3/M4.

Verified as search-report coverage: Mathlib title-only entries; the qualified no-hit conclusions for the named circle targets; Steiner–Lehmus algebraic prior art; Acorn stated-only prior art; the weaker Gerretsen bound; 1045 AFP mirror entries and 1500 Mizar sources. These support a bounded “none found,” not a global absence theorem.

## Release recommendation

The quoted main results are mostly faithful once Clifford's witness conventions are made explicit. The strongest reasons not to release this prose unchanged are the **false universal exceptional-case explanations** (M3/M4) and the **inflated verification scope** (M5–M10). Correct those independently of the unfinished placeholders. No proof-kernel unsoundness or demonstrably false main Lean theorem was established by this review.
