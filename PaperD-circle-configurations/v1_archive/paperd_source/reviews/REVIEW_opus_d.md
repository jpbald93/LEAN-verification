VERDICT: MINOR REVISION. Of Astra's 19 issues, 15 are fixed, 4 partly fixed and 0 not fixed. The revision introduces 0 BLOCKER, 3 MAJOR and 10 MINOR new issues. One of the MAJOR issues is a new factual error in Related work.

# Second independent review: Paper D revision after Astra (REVIEW_astra_d.md)

**Scope.**

- I read `paperd.tex` (692 lines, revised), `astra_changes.diff`, `FIX_LOG.md`, the Lean sources under `src/`, and all files in `reports/`.
- I recomputed the following with python/sympy:
  - the Lester isosceles family and the 120° example;
  - the Kosnita 1, √3, 1 example;
  - every count in §Verification;
  - the `\decl` and `\src` anchors (run locally against `src/*/gate.sh`);
  - the SHA-256 values in `manifest_john.log` against the local snapshot.
- I also fetched the two prior-art control theorems: AFP `Miquel.thy` and HighSchoolGeometry `applications_cocyclicite.v`.
- Paper line numbers below refer to the revised `paperd.tex`.

## 1. Astra's 19 issues

| # | Status | Where | Comment |
|---|---|---|---|
| M1 Clifford witnesses | **FIXED** | 187–204, 211–218 | Theorems 2 and 3 are now stated for the explicit points `cp`, with the existential/explicit split and the designated triples (matching `m6`, Third:808). "We do not prove that the common point is unique" (191) is correct. |
| M2 `IsGCircle` / `Chain` | **FIXED** | 229–241 | Radius 0 and empty spheres are disclosed, and so is the radius-0 use at Clean:145. The existential, non-coherent `Chain` is disclosed. Residual: Contributions (100) still says "defines the whole chain" with no qualifier (trivial). |
| M3 Lester universal claim | **FIXED** | 289–298, 394 | The new numbers are correct (§2a). Astra was right. |
| M4 Kosnita boundary | **FIXED** | 339–348, 396 | The example is verified (§2b). Two residual nuances are listed as new issues N6 and N7. |
| M5 numerical scope | **PARTLY** | 462–475, 509–510 | The coverage list, per-theorem counts, 999/1000 control, Blundon/Steiner–Lehmus exclusion and missing-scripts disclosure are all correct. Two problems remain: (a) 509–510 "the numerical configurations above satisfy every hypothesis" goes beyond the reports (N10); (b) 463–464, "on the machine other than the one where the proofs were written", has no receipt (N11). |
| M6 platform / hash receipts | **PARTLY** | 457–460, 479–480, 500–504 | The receipt table is a placeholder, as allowed. But the text around it pre-commits ("the hashes agree across the two machines"). The one existing hash receipt is incomplete and does not match the snapshot. The OOM narrative gained a new unreceipted number (87) and an "archived" claim. See N2 and N3. |
| M7 mutation coverage | **FIXED** | 482–497 | 490 / 455 / 34 / 1 and the per-development figures are all correct. The list of main theorems with no mutants matches every battery report's "no mutants generated" line. "The second development's n=4,5 theorems" is ambiguous: the report lists cliffordchain `clifford_one` / `clifford_two`, not `cliffordChain_four` / `_five` (trivial). |
| M8 consistency / satisfiability | **PARTLY** | 498–510 | The wording is fixed: "does not show that the hypotheses are consistent". But "the other 101, including every main theorem, are recorded as unresolved" is false for Theorem 7 (N4). The Clifford share of 49/136 is inferred, not in any receipt (N5). |
| M9 ablation granularity | **PARTLY** | 511–523 | The binder-versus-conjunct caveat is good; I confirmed at Proof:330, 333 that Lester uses `.1` and `.2.1`. The original-Clifford ablation results (517–520) are still presented as executed battery results, but neither Jack report contains an ablation section. I checked them by source inspection and they are correct: `clifford_two_explicit` (Third:471–542) never uses n135, n145, n235, n245 or n345, and `five_NN` (Third:614–616) uses only n123, n124, n134 and n234. They should therefore be labelled as source inspection (or wait for the placeholder at 523). |
| M10 pre-committed outcomes | **FIXED** | 524–531, 544 | The linter claim is limited to seven developments. The blind and hand checks are now conditional. The authorship sentence (550) is unchanged but acceptable. |
| M11 novelty scope | **FIXED** | 68–72, 92–93, 424, 436 | Absence is now always bounded by the search scope. However, the new Related-work sentence introduced a factual error (N1). |
| m1 eight developments | **FIXED** | 129–132 | 20 files and 4,353 lines recomputed: exact. |
| m2 ten/twenty | **FIXED** | 519–520 | Correct (Third:458–471). |
| m3 fifteen points | **FIXED** | 262–263, 393 | |
| m4 `\decl` scope | **FIXED** | 153–156 | Every `\decl` is in a REQUIRED list. All 22 `\src` anchors land on the named declaration. SCAFFOLD is disclosed (gate.sh:9–21). |
| m5 fivecircles method | **FIXED** | 114–116, 273–278 | "Unlike the other developments, the proof is not a single polynomial certificate" (273–274) slightly over-generalizes, since Clifford n=6 and Thébault are multi-lemma (trivial). |
| m6 tangency / anchors | **FIXED** | 164–174 | Example P₁₂ = 1+i checked. `ccenter` is at Basic:197 and `gam` at Basic:203. |
| m7 history | **FIXED** | 89–91, 289, 438–443 | "by computer" and "typically" are gone, and Hasclid is "which we did not run". |
| m8 search limits | **FIXED** | 419–420, 432–436 | Matches priorart.md:62–65. |

**Where Astra itself was wrong, over-stated or incomplete:**

- **Kosnita audit.** Astra accepted 338–339 ("the first exclusion is forced"). It is not forced; it is logically redundant (N7).
- **Kosnita fix.** Astra's suggested sentence, "necessary to retain an unrestricted affine theorem", is only partly defensible: at its own example the Lean conclusion holds anyway (N6).
- **M6 toolchain.** "No `lean-toolchain` or Lake manifest" is now moot: `manifest_john.log` records toolchain and Mathlib for all eight repositories on john.
- **M5 residual.** The 5.3×10⁻⁴⁷ point is pedantic but correct.
- **Missed by Astra.** Astra did not notice that the HighSchoolGeometry "Miquel" is the four-line, conditional-incidence theorem (N1, N12).
- Otherwise Astra's findings were correct.

## 2. Checks on new factual sentences

**a. Lester (289–298).** Recomputed with the source's apex definitions (Basic:22–47).

- For A=(0,h), B=(−1,0), C=(1,0):
  - O=(0,(h²−1)/2h);
  - N=(0,(h²+1)/4h);
  - F₁=(0,1/√3) and F₂=(0,−1/√3) for every h, with line residuals ≤4e-16.
- Minimum pairwise separation of the four points:

  | h | separation |
  |---|---|
  | 0.3 | 0.331 |
  | 0.5 | 0.0476 |
  | 1 | 0.0774 |
  | 2.5 | 0.148 |

  The stated range "0.048 to 0.33" is correct, the points are four distinct collinear points, and so they are not concyclic.
- For h=1/√3 (apex 120°): N=A=F₁ and F₂=O, so the set has 2 elements. **Correct.**
- Caveat: this computation, like the re-verification numerics, is not archived (see N3 and the disclosure at 472–475).

**b. Kosnita (343–348).** Exact sympy check.

- Oa=(1,0)=A, Ob=(½,−√3/6), Oc=(½,√3/6).
- Every equidistance holds exactly.
- ABC, OBC, OCA and OAB are all non-collinear (determinants ±√3/2).
- Sides are 1, √3, 1; cos A = −½, so the angle at A is 120°.
- AB²+BC²+CA² = 5 = 5R².
- B, Ob, C and Oc all lie on x=½, so BOb and COc are the same line.
- **All stated facts are correct.** Two nuances (N6, N7) are below.

**c. Numerical counts (466–471).**

| Item | Paper | Receipt |
|---|---|---|
| Clifford n=4/5/6 | 4500 / 1800 / 300 | verify_jack_clifford:20, 25, 32 |
| cliffordchain | 1500 / 300 | verify_jack_crosscheck:11, 24 |
| Lester | 2000 | verify_john:17 |
| Thébault | 500 / 1989 | crosscheck:43; john:32 |
| fivecircles | 1000 | john:50 |
| Kosnita | 2000 | john:68 |
| fivecircles control | 999/1000 | john:50 |

All correct.

- **Residual range** "5.3e-47 to 1e-60": the upper end is fivecircles (john:50). The smallest *worst* residual for a theorem is 3.7e-59 (crosscheck:45); 1e-60-scale figures are model-matching residuals. This is loose but harmless.
- **"50 to 60 digits"**: precision is stated only for Lester (50) and the jack reports (60). It is unstated for john's Thébault, fivecircles and Kosnita runs.

**d. Battery counts.**

- **Mutations.** Mutants: 129+118+82+65+36+33+21+6 = 490. Timeouts: 27+2+3+2 = 34. Rejected by error: 490−34−1 = 455. The survivor is `sign_neg` lit0→1 (thebault:37). All **correct**.
- **Satisfiability.** The breakdown from the six john receipts is 41 with hypotheses / 71 hypothesis-free / 11 closed. The paper's 49/136/11 needs Clifford to contribute 8/65/0, and `jack_clifford_summary.md` gives no breakdown (N5).
- **Ablation, linter and the cert_den underscores** match the john receipts.

## 3. New issues introduced (or left standing) by the revision

### MAJOR

**N1. False new claim that the three-circle Miquel controls prove existence (410).** "Isabelle/HOL and Rocq's HighSchoolGeometry, both with existence of the common point" is false for HighSchoolGeometry.

- `applications_cocyclicite.v:270–286` (fetched) proves a conditional incidence statement. From `sont_cocycliques A C F M` and `sont_cocycliques A E D M` it derives `sont_cocycliques E C B M ∧ sont_cocycliques D F B M`. This has the same shape as lean-genius.
- It is also the **four-line (complete-quadrilateral)** Miquel theorem, not the three-circle pivot (lines ADF, AEC, BDE, BFC; compare verify_john.md:76).
- AFP has both forms: `miquel_pivot` (Miquel.thy:267, incidence) and `miquel_concurrent` (Miquel.thy:467, existence by an explicit point).

**Fix:** "AFP proves both the incidence form and existence; HighSchoolGeometry proves the incidence form of the four-line Miquel theorem; lean-genius proves the incidence form of the pivot theorem." Line 82 has the same problem (N12).

**N2. Receipt text pre-commits, and the one existing hash receipt does not support "every library file" (457–458, 479–480).**

- "the hashes agree across the two machines" is unconditional, yet FIX_LOG.md says the jack hash run was only launched.
- `manifest_john.log` **omits `Lester/Bridge.lean`**, the file containing every `bridge_*` lemma the paper cites (301–303). Lester.lean, which imports it, is hashed.
- John's `cliffordchain/Clifford.lean` hash is `d97d04…`, but the local snapshot's is `2bc4e5…`. The two contain the same imports with different bytes. So the snapshot the paper counts (132, 139) is not byte-identical to what john gated.
- 479–480 ("battery … on sources with the same SHA-256 hashes as those checked by the gates"): the battery receipts contain no hashes, only 8-character prefixes in `inv_*`, and they predate the manifest (01:31 UTC on 14 Oct).

**Fix:** re-take the manifest with a recursive find, reconcile the cliffordchain root file, and make 457–458 and 479–480 conditional until the jack table exists.

**N3. New unreceipted specifics in the OOM narrative (500–504).** The revision added three things no supplied file supports:

- "the 87 mutation records affected in the same way";
- "discarded those 24 records";
- "the run logs and the discarded records are archived".

The only trace in any file is the header "resumed after OOM fix" (jack_partial…:1). This is exactly what Astra M6 asked to archive or drop, and the revision instead added a further count plus a claim that the evidence is archived. **Fix:** archive the pre-fix run and the rerun, or cut the passage to "a first run misread out-of-memory kills as successes; the harness was fixed and Clifford re-run (receipt …)".

### MINOR

- **N4. Theorem 7 contradicts "including every main theorem" (507).** `cliffordChain_four` and `cliffordChain_five` (Clean:226, 245) are the only closed theorems in cliffordchain. They are absent from its unresolved list (john_clifford_j:97), so they are the "2 closed" certified items (john_clifford_j:90). Fix: say "every main theorem with hypotheses", and note that the two closed chain theorems are "certified" only trivially.
- **N5. The 49/136 split is inferred, not receipted (506–507).** It holds only if all 65 Clifford no-hypothesis declarations were certified, and Blundon shows that no-hypothesis declarations can be unresolved. Get the split from the jack JSON, or present it as john-only plus a Clifford total.
- **N6. Kosnita boundary wording (339–347).**
  - "On the locus … the concurrence point … goes to infinity" is still a universal statement about the locus, and 345–346 then denies having one.
  - At the 1, √3, 1 example the Lean conclusion is true anyway: {A, Oa, P} = {A, P}, and any P on x=½ works. So hS is not needed there.
  - Fix: "at the three sampled boundary triangles the lines are distinct and parallel"; state that the conclusion holds trivially at the 120° example, mirroring the Lester remark at 294–298.
- **N7. "The first exclusion is forced" (338–339) is wrong; it is redundant.** Suppose hOBC fails. Then O,B,C are collinear; with OB=OC and B≠C (from hABC), O is the midpoint of BC. No point Oa can then be equidistant from three distinct collinear points, so hOa1 and hOa2 cannot both hold. Hence hOBC is implied by hABC, hOA, hOC, hOa1 and hOa2, and likewise for hOCA and hOAB. Removing it would not make the theorem false. Ablation "needed" only means the unchanged proof uses it. This sentence predates the revision; Astra missed it.
- **N8. Lean docstrings still assert the retracted universal claims.**
  - `src/lester/Lester/Basic.lean:7` says "For a non-equilateral triangle".
  - `Basic.lean:51–53` says isosceles "makes the four points collinear … hence not concyclic".
  - `src/kosnita/Kosnita/Basic.lean:177–178` says "(otherwise the lines are parallel)".
  - Fix these before publishing the code alongside the paper.
- **N9. Line 124 conflicts with the revised table.** It says Section 8 says "which are genuinely necessary", but the revised table (394, 396) deliberately avoids "necessary". Change it to "which cannot simply be dropped".
- **N10. Numerical satisfaction of hypotheses is overstated (509–510).** The reports say the hypotheses held for Clifford n=6 (verify_jack_clifford:34), Thébault (crosscheck:44) and the fivecircles *circle* hypotheses (john:50). They say nothing for Kosnita, Lester, cliffordchain GenPos5 or fivecircles distinctness. Restrict the claim, or say "were generated to satisfy".
- **N11. "On the machine other than the one where the proofs were written" (463–464) is unsupported, and doubtful for the original Clifford.** The manifest maps john `clifford_jack` to "jack clifford", i.e. the development lives on jack. Both verify_jack_clifford and the Clifford battery also ran on jack. Delete the clause or substantiate it.
- **N12. Line 82 mis-describes the Rocq control.** It says the pivot theorem "is formalized … in Rocq [hsgeometry]", but the Rocq theorem is the four-line form. This predates the revision; fix it together with N1.
- **N13. Precision and archiving of the new computations.** "50 to 60 digits" (465) is not stated for three of the reports. The new Lester computation (292) is "we computed" with no archived script, which conflicts with the archive-disclosure tone of 472–475. Either archive the scripts or add the Lester computation to the same disclosure.

No problems found in:

- Clifford M1 statements versus Third:457–473, 543–565 and 780–824;
- the tangency sentence (170–171);
- the m6 anchors;
- the 20-file / 4,353-line count;
- the gate and SCAFFOLD description;
- the binder caveat;
- the conditional wording around the PH placeholders at 403–405, 523, 525 and 533. The exception is 457–458 (N2).
