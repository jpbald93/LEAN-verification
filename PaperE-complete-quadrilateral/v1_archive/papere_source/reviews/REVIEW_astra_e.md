MAJOR REVISION — BLOCKER: 0; MAJOR: 2; MINOR: 7.

# Independent layer-12 review of Paper E

Reviewer: `genspark-llm-proxy/gpt-6-astra`. Paper line numbers below refer to `papere.tex`; source paths are relative to `src/`. I read the theorem statements, both bridges, the numerical scripts, the four pre-bridge battery reports and the prior-art sweep; independently reran the 1,000-case numerical script; performed exact/symbolic checks; and consulted the cited external sources. No Lean executable was available, so this is not a fresh kernel/build verification. The five known placeholders are not counted as defects.

## Issues

### 1. MAJOR — The abstract/table promote the fixed-pair cross-product result to unconditional affine-line parallelism

**Paper:** 51–61, 98–101, 109–111; compare 263–278.

**Evidence:** `quadmiquel/QuadMiquel/Simson.lean:171–174` proves only
`cr (F₂ - F₁) (H₃ - H₄) = 0` under `GenPos`. This is vacuous when `H₃ = H₄`. `QuadMiquel/Bridge.lean:577–579` proves that equality occurs exactly when `L₁ ⟂ L₂`; the actual affine-subspace parallel theorem at 606–610 therefore has the additional `hperp` hypothesis. The body accurately explains this limitation, but the abstract calls all eight classical geometric theorems machine-checked from the single hypothesis and says the Simson line is parallel to the orthocentre line without qualification; the table likewise gives that geometric conclusion and says every entry assumes only `GenPos`.

This is **not** a counterexample to the classical unconditional parallelism of the genuine orthocentre line. A different pair can determine that line in the exceptional case, and relabelling should supply the missing argument. It is a mismatch between what these exported declarations establish and what the summary credits to them. The later caveat does not make the unqualified headline statement an exact description of the proof.

**Fix:** Either qualify the summary/table as a cross-product form, with affine parallelism for the chosen pair under `L₁ ⟂̸ L₂`, or add a theorem for the affine span of all four orthocentres that handles the exceptional case by another pair. Keep the distinction between a necessary condition for the **fixed pair** and a condition for the classical theorem itself.

### 2. MAJOR — The description of the HSG Miquel theorem omits essential restrictions and is false literally

**Paper:** 317–324, especially “a point on two of the four circumcircles lies on the other two”; also the summary of prior proofs at 68–70.

**Evidence:** I fetched `https://raw.githubusercontent.com/rocq-community/HighSchoolGeometry/master/theories/applications_cocyclicite.v`. `Theorem Miquel` indeed ends in `Qed` and is the four-line configuration, but it assumes, among other things, `triangle A E M`, `triangle B D M`, and `triangle B F M`, in addition to the incidences and two cocyclicity premises. The two specified circles `(ACF)` and `(AED)` share the vertex `A`. Taking `M = A` satisfies membership in both circles but does **not** give membership in the other two under general position. The omitted non-collinearity assumptions exclude this case. The sweep itself records these assumptions (`reports/priorart.md:57–65`). The result is conditional and does not itself construct a common point from four arbitrary general-position lines.

**Fix:** Say “under the library's incidence and non-collinearity hypotheses, a suitable second common point of the specified two circumcircles lies on the other two.” Explicitly distinguish this conditional result from the present existence/formula theorem. Retain credit for prior formal work; do not describe it as the unrestricted two-circle implication.

### 3. MINOR — The contribution's uniqueness claim quantifies over more triples than the cited theorem

**Paper:** 119–120; compare the correct description at 241–243.

**Evidence:** `quadmiquel/QuadMiquel/Bridge.lean:496–503` has three particular premises: membership in the circles of `T₄`, `T₃`, and `T₁`. It proves uniqueness on this triple, hence on all four. It does not quantify over a choice of three of the four. The stronger “any three” claim is mathematically reasonable by relabelling, but the paper expressly says symmetry has not been formalised (123–124, 400–401).

**Fix:** Change the contribution to “any point on the circumcircles of `T₄`, `T₃` and `T₁` is `M`; in particular, the common point of all four is unique,” or formally supply the other triples.

### 4. MINOR — The cross-machine satisfiability difference is five declarations in quadnewton, not one

**Paper:** 373–375.

**Evidence:** The totals differ by one, but the certified sets do not. From `reports/jack_quadnewton.md:36–50` and `reports/john_quadnewton.md:36–49`:

- Jack unresolved / John certified: `dv_ne`, `mid_ne`, `meet_mem_right`.
- John unresolved / Jack certified: `r_ne`, `collinear_of_param`.

Thus five declaration outcomes differ, with a net count difference of one. In quadmiquel the sole difference really is `meet_mem_right` (unresolved on Jack, certified on John).

**Fix:** Say “all other reported categories agree; the numbers of satisfiability certificates differ by one in each development,” and, preferably, state the five-versus-one declaration-level differences. The totals 37/38 of 52 and 56/57 of 75 are correct.

### 5. MINOR — The ablation paragraph conflates proof dependence, logical necessity, and totalised division

**Paper:** 388–393.

**Evidence:** The reports establish 41 failed removals for quadnewton, and 125 failed / 17 successful removals for quadmiquel. Failed removal with the existing proof is not a proof that a hypothesis is logically necessary. Conversely, the 17 successful removals are genuinely all non-vanishing conditions in the six named lemmas, but they are not all explained by division by zero:

- `QuadMiquel/Algebra.lean:110–118`: the unused `hK` in `circC_T4` and `circC_T3` is compatible with zero denominator because both sides then evaluate to zero.
- At 127–137, the unused `hq` and `hD` in `circC_scaled` likewise allow zero-denominator cases (both sides become `a`).
- At 242–248, the `qM u v s t` term cancels from the difference of the two `footC` expressions. Consequently `simF2.hD` is irrelevant to that difference; `hu`, `hv`, and `hK` are not denominator requirements of the simplified identity. Its unused `hE` does have a totalisation explanation: when `E = 0`, the remaining conjugate Miquel expression and `qW` are both zero.
- At 250–265, the same cancellation explains `simF3.hD` and `simF4.hD`; `hK`, `hu`, and the uncapitalised `huv` / `h4` are also unnecessary. The corresponding capitalised denominator hypotheses are retained.

These account for all 17: five have the direct zero-denominator extension explanation, while twelve are removed by cancellation/absence of the alleged denominator constraint. I independently simplified the three generic Simson identities with SymPy.

**Fix:** Replace “are needed” by “removing them broke the existing proof in the ablation test.” Explain that the unused hypotheses reflect a mixture of cancellation and valid extension to totalised zero-denominator cases. Do not infer mathematical necessity from the failure of an unchanged proof.

### 6. MINOR — The bridge interface is not literally identical in both developments

**Paper:** 280–297, especially “the quadmiquel ones are the same.”

**Evidence:** The first five listed bridge names and meanings match. But `quadnewton/QuadNewton/Bridge.lean:174–180` bundles four non-collinearity statements **and** `List.Pairwise` distinctness of all six vertices in `genPos_triangles`. In quadmiquel, `genPos_triangles` at 240–244 contains only non-collinearity, in the opposite triangle order, and a separate `genPos_vertices_ne` at 201–207 supplies distinctness. There is no `QuadNewton.genPos_vertices_ne` declaration. Also, Newton's `genPos_iff` at 334–343 states nonconcurrence using Mathlib affine-line membership, whereas Miquel's version at 645–657 still uses local `Line.carrier` for nonconcurrence (bridged separately by `carrier_eq_line`). The meanings agree, but not the literal packaged statements.

**Fix:** Say “the corresponding bridge names agree except for the split triangle/vertex result; the statements are equivalent through the carrier bridge.” State the two packaging differences explicitly. No new mathematics is required.

### 7. MINOR — The Newton negative control is described with the perturbed and original configurations reversed

**Paper:** 368–370.

**Evidence:** `numerics/paperE_numerics.py:60–65` evaluates `colres([mids[0], mp_[1], mp_[2]])`: **one original midpoint and two perturbed midpoints**, not one midpoint from a perturbed configuration. Its own output label correctly says “one midpoint from unperturbed config.” The control is meaningful and fails in all 1,000 trials; this is only a reproducibility-description error.

**Fix:** Describe the actual mixed triple, or invert the mix in the script and regenerate the result. The existing script's numerical values match the paper to the reported precision.

### 8. MINOR — Prior-art proof status drops qualifications present in the sweep

**Paper:** 316–333 and 406.

**Evidence:** `reports/priorart.md:49–51,65` says the area-method result is relative to an axiomatized field and area geometry, and HSG to its axiomatic plane. The sweep could not run `Print Assumptions`; the area-method repository contains three `Admitted` lemmas reported as outside the relevant path. The source `Qed` results are real—I independently fetched `gauss_line` and `Miquel`—but the paper's unqualified “complete formal proofs” and source-confirmation paragraph do not disclose that foundation/dependency distinction or that the prior proofs were not rebuilt. This does not invalidate their status as prior formal work.

**Fix:** Add a concise qualification: these are completed source proofs relative to their libraries' geometric axioms, inspected but not independently rebuilt; the area-method admission-dependency assessment was not confirmed by `Print Assumptions`. Keep “we found none” scoped to the searched sources. ProofAtlas partial coverage is already properly disclosed at 315 and needs no correction.

### 9. MINOR — “Every theorem is ... closed by field_simp and ring” is too broad

**Paper:** 181–184.

**Evidence:** Rational identities are the algebraic engine, not the entire proof of every theorem. `QuadNewton/Quad.lean:53–67` constructs collinearity from a real parameterization; 97–109 proves a disjunction of inequalities. `QuadMiquel/Miquel.lean:200–214` builds the existential `Cospherical` witness. Bridge uniqueness at `QuadMiquel/Bridge.lean:496–516` invokes Mathlib's two-circle intersection result, rather than merely clearing denominators. Even before bridges, the normal-form existence and non-vanishing statements require incidence/linear-independence arguments.

**Fix:** Write “The central coordinate identities reduce to rational identities, discharged principally by `field_simp`, `ring`, and linear-combination certificates; incidence and nondegeneracy lemmas connect these to the geometric conclusions.”

## Verified as correct

- **Model and labelling.** The two `Basic.lean` files are byte-identical after namespace substitution. Paper 152–172 matches `Basic.lean:18–60`: cross product, carrier, meet, all 14 `GenPos` fields, circumcentre, orthocentre, and foot. The four triangles and three diagonal pairs are consistently labelled. Newton's normal form (`Lines.lean:101–107`, `nX` at 83–84) and Miquel's (`Frame.lean:168–174`, `qA34` at `Algebra.lean:25`) agree with 177–181.

- **Diagonal-side theorems.** The statements at paper 191–198, 211–225 match `QuadNewton/Quad.lean:53–55,70–71,79–83,97–99,135–141,155–164`. In particular the non-all-equal disjunction really is `H₃ ≠ H₄ ∨ H₂ ≠ H₄`; perpendicularity ranges over **any two of all four orthocentres**, using the specified first two diagonal midpoints. The power bridge and three pairwise-distinct centres are present (`Bridge.lean:232–254`). The coaxal interpretation is valid classical reasoning: each equal-power locus is a line, and the two distinct orthocentres force those lines to coincide. The paper correctly does not claim a formal coaxal-pencil object.

- **Circle-side theorems.** The explicit formula is exactly `miquelPt` (`Miquel.lean:17–20`); I symbolically verified its claimed spiral-similarity centre relation. The denominator non-vanishing, all-four-circle membership (`Miquel.lean:162–170`), five-point cosphericity (200–204), four-foot collinearity (`Simson.lean:155–157`), and fixed-pair cross-product relation (171–174) have the stated hypotheses. Reflection/second intersection, exclusion of all six vertices, the specified-triple uniqueness, and all six inequalities between feet are actually proved (`Bridge.lean:365–368,468–473,496–503,555–561`). The affine theorem and its exception are accurately explained in the body.

- **No hidden trivial Steiner circle.** `Cospherical` alone allows repeated points, and the exported theorem does not separately assert five-point distinctness. Nevertheless there is no actual degeneracy counterexample under `GenPos`. Any two triangle circumcircles share a vertex; equal centres would imply equal radii and the same circle, placing three distinct collinear vertices on it, impossible. Thus the four centres are pairwise distinct. `M` cannot equal a centre because it lies on that nonzero-radius triangle circumcircle. Already the proved `O₄ ≠ O₃` (`Bridge.lean:431–434`) excludes a zero-radius common sphere. The paper's “lie on one circle” wording is sound; a separate formal distinctness lemma would be optional strengthening, not a required correction.

- **Exact example and perpendicular criterion.** Independent exact SymPy computation gives
  `A12=0, A13=1, A14=2, A23=i, A24=-2i, A34=3/2-i/2`,
  `O4=(1+i)/2, O3=1-i, O2=3/2, O1=-i/2`, and precisely `H1=H2=3/2-i/2`, `H3=H4=0`. All six direction cross products and all four nonconcurrence checks are nonzero. Paper 201–205 is correct. Both `T3` and `T4` use the sides `L1,L2` through `A12`, so 269–270's right-angle explanation is correct for the perpendicular case; the converse is supplied by `ortho34_eq_iff`, not merely by that verbal explanation.

- **Numerics.** Running `python3 numerics/paperE_numerics.py` reproduced all eleven archived JSON records exactly: residuals `4.68e-60, 2.38e-59, 1.31e-54, 8.89e-60, 1.45e-57, 6.28e-58, 1.16e-57, 3.31e-58`; control minima `2.68e-7, 1.05e-8, 0.00316`. All three `SHA256SUMS` checks pass. Unit directions make the rejection threshold a genuine vertex-to-line distance. Bodenmiller checks all orthocentres and both power differences; the perpendicularity row checks the most separated orthocentre pair; Steiner tests the four centres and `M` against a circle fitted to three centres; parallelism uses exactly `H3-H4`. These are meaningful numerical checks, not proofs of all-pair/nondegeneracy/uniqueness statements. The normalized parallel test does not exercise the forced perpendicular exception. The three controls are meaningful, but are not eight separate theorem-specific controls. The paper appropriately calls the results evidence, not proofs.

- **Inventory and battery totals.** The library-only counts are exactly 6 files/1,066 lines and 7 files/1,626 lines, totaling 13/2,692. Both toolchains and Mathlib pins match the paper. Current REQUIRED lists have 35 and 51 entries, and every paper `\decl` name belongs to the appropriate list. The pre-bridge reports support 110/110 rejected Newton mutants, 150 error-rejected plus 2 heartbeat-rejected Miquel mutants, zero survivors, the stated main-theorem mutation blind spots, zero derived contradictions, 41 versus 142 ablations, and the 17 listed successes. The six tamper categories match the scripts and reports. Their `falsehyp` tests remove genuinely necessary hypotheses in the particular examples tested.

- **Bridge findings.** The reports consistently say no requested Newton bridge statement needed correction; only the requested Miquel fixed-pair affine parallel form needed an extra hypothesis. Counterexamples to already-excluded zero-direction/collinear inputs do not contradict “only statement that failed as first written.” The numerical bridge scripts named in those reports are not included in this snapshot, so their detailed execution history is report evidence, not independently rerun here.

- **Prior art and bibliography.** HOL Light's `GAUSS` source (currently lines 520 onward) really cites Chou example 15 and uses `GEOM_TAC THEN CONV_TAC GROBNER_REAL_ARITH`; the incidence pattern is the Newton–Gauss configuration. Rocq's `gauss_line` is the corresponding area-method result. The sweep supports the qualified search outcome “two target theorem families found, no proofs of the other six or Lean versions found in searched sources,” not a universal absence theorem. The AFP Miquel entry independently confirms that it is the triangle pivot form. The Clifford/inversion remark is a valid classical relationship for the appropriate nondegenerate configurations and is explicitly not claimed formalised.

  Bibliographic checks: NUMDAM confirms Steiner's exact title, volume 18 (1827–1828), pp. 302–304 (`https://www.numdam.org/item/AMPA_1827-1828__18__302_0/`). I also extracted the original PDF text: its items 1–2 explicitly state the common point and the circle through the four centres and that point; items 3–7 contain the relevant line results. Coolidge 1916/Clarendon is confirmed by the original-book catalog and contemporary Nature review (`https://www.nature.com/articles/099201b0`). Johnson 1929/Houghton Mifflin and p. 172 for Gauss–Bodenmiller are explicitly cited by MathWorld (`https://mathworld.wolfram.com/Gauss-BodenmillerTheorem.html`); I did not inspect Johnson's page image. Chou 1988/Reidel/Dordrecht is corroborated by scholarly bibliographies. Janičić–Narboux–Quaresma, JAR 48(4), 489–532 (2012), is confirmed by HAL and publisher indexing (DOI `10.1007/s10817-010-9209-7`). Guilhot's article/title, TSI 24(9), 1113–1138 (2005), is corroborated by DBLP and scholarly citations (DOI `10.3166/tsi.24.1113-1138`). No fabricated or materially incorrect entry was found among the six requested references.

## Pending evidence, not counted as defects

Paper 342–347's **bridge-inclusive, both-machines** gate/tamper claim still depends on the pending final receipts: the four machine-labelled reports in this snapshot are explicitly pre-bridge (22 and 32 gate declarations); the bridge reports supply the new 35/51 results but not a pair of machine-labelled final receipts for each tree. Likewise 394's linter claim is presently supported by pre-bridge runs, not a bridge-inclusive run. Keep these claims conditional until the promised final receipts/battery are inserted. The five placeholders, layer-13 review, author hand check, and publication pins remain explicitly pending and are not findings of this review.
