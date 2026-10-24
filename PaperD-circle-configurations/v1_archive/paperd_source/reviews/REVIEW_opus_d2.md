VERDICT: MINOR REVISION. Of the 17 tracked items (N1–N13, M5, M6, M8, M9), 11 are fixed, 4 partly fixed and 2 not fixed. This round adds 2 MAJOR issues (unreceipted claims added while placeholders were removed) and 7 MINOR ones. No BLOCKER.

# Confirmation review, round 2 (paperd.tex after opus_changes.diff)

Line numbers refer to the current `paperd.tex` (727 lines).

**What I re-ran:**
- the full `paperd_numerics.py` (SCALE=1, in a /tmp copy). All 9 records match `results_20261014.jsonl` exactly.
- `paperd_examples.py`. Its output is byte-identical to `examples_output.txt`.
- `sha256sum -c SHA256SUMS`: all OK.

**What I recomputed:**
- file, line and REQUIRED counts;
- the per-repo SHA-256 values of `src/` against `manifest_john.log` and `gates_jack.log`;
- the statuses in the pre-fix and post-fix JSONL files.

## 1. Previous items

| # | Status | Where | Note |
|---|---|---|---|
| N1 Miquel controls | FIXED | 421–425 | AFP has both incidence (`miquel_pivot`) and existence (`miquel_concurrent`). HSG has the four-line conditional incidence. lean-genius has pivot incidence. All three are correct. |
| N2 hash receipts | PARTLY | 470–473, 512 | `manifest_john.log` now includes `Lester/Bridge.lean` and `Clifford/Bridge.lean`. The local cliffordchain `Clifford.lean` (d97d04…) now matches john. But 471 still pre-commits "the hashes agree across the two machines", which is now demonstrably false (see X1). |
| N3 OOM narrative | FIXED | 532–537 | Pre-fix file: exactly 24 `contra/CONTRADICTORY` and 87 `mut/error-unattributed`, all 87 with rc=137. Post-fix: contra ok 38 (=14+24) and mut 102 killed + 27 timeout = 129 (=39+3+87). So 111 records were removed and re-run, consistent with the text. Nit: the 24 CONTRADICTORY records carry no `rc`/`err`, so the archived file shows OOM only for the 87, not for the 24. |
| N4 closed theorems | FIXED | 541–543 | john_clifford_j:90 has "2 closed". Every main theorem with hypotheses is in an unresolved list: jack JSONL (clifford_one, two, two_explicit, three); john lists (clifford_two_clean, lester, sawayama_thebault, fivecircles, kosnita, blundon, steiner_lehmus). |
| N5 49/136/11 | FIXED | 539–541 | john: 41/71/11, unresolved 71. jack `kind` field (and `sat_breakdown_clifford.txt`): hyps 8, hyp-free 65, closed 0, unresolved 30. Totals: 49/136/11, 196 certified, 101 unresolved, 297 declarations ✓. Caveat: 297 is the pre-Bridge count (X1). |
| N6 Kosnita locus wording | NOT | 351–358 | "On the locus … goes to infinity" is still universal. The text does not say that at the 1, √3, 1 example the Lean conclusion holds trivially: with Oa=A, {A,Oa,P}={A,P}, and P can be any point of x=½. |
| N7 "first exclusion is forced" | NOT | 350 | Unchanged. **The Kosnita "redundant" argument you asked me to verify is not in the paper**: grep finds no "redundan" in paperd.tex or Kosnita sources. The argument itself stands. If hOBC fails, O is the midpoint of BC, so hOa1 and hOa2 are unsatisfiable; hOBC is therefore implied by the other hypotheses. Replace "forced" with "logically redundant given hOa1/hOa2 (if O∈BC no Oa exists); kept for the proof". Row 408 says only "cannot be dropped (affine)", which is fine for hS. |
| N8 docstrings | PARTLY | — | Lester is fixed: Basic:7 ("scalene") and 51–53. Kosnita's theorem docstring 178–179 is fixed ("can be parallel"). But the **module docstring `Kosnita/Basic.lean:17–18`** still says "when equality holds the three lines are pairwise parallel (and distinct) … the affine claim is false". Paper 356–358 contradicts this. The same text is in `pub/kosnita`. |
| N9 | FIXED | 126 | |
| N10 numerical hypotheses | FIXED | 501–502, 544–545 | One residual for Clifford n=6: the script checks non-collinearity of `pts[0..2]` = T∈{2345,1345,1245}, not the designated triples of m1–m6. This is implied, because all five points are distinct (≥1e-3) and concyclic, but it is not directly checked. |
| N11 | FIXED | 476–477 | |
| N12 | FIXED | 82–84 | |
| N13 precision / archiving | FIXED | 480, 304–310 | The Lester and Kosnita examples are now in `paperd_examples.py`, and the output matches 304–310 (separations 0.331, 0.0476, 0.0774, 0.148). Nit: the paper never names `paperd_examples.py`. |
| M5 numerics | PARTLY | 475–508 | The new table is reproducible (see §2c). But the deleted disclosure ("scripts … not kept, so the figures … cannot be re-run") still applied to several remaining agent-only claims that the new script does **not** reproduce (X3). |
| M6 receipts | PARTLY | 470–473 | Table still a placeholder, with pre-committing text (see X1). |
| M8 | FIXED | 538–545 | |
| M9 ablation | FIXED | 552–557 | See §2e. |

## 2. New factual content

**a. Related-work Miquel (421–425; intro 82–84).** Correct (as in N1).

**b. Kosnita "redundant" argument.** Absent (N7). The Kosnita section is unchanged by the diff.

**c. Numerics table (489–497) against `results_20261014.jsonl`.** Every figure matches: 1.12e-58, 1.23e-57, 1.07e-57, 1.75e-59, 1.58e-58, 2.41e-60, 1.23e-59, 7.78e-62, Blundon margin 4.51e-11 with control 310/1000. The other controls are all n/n. I checked what each row of the script actually tests:

- **Clifford n=4.** It builds the common point as the second intersection of Γ123 and Γ124, then tests it on all four Γ. That is a genuine test, since Γ134 and Γ234 are unforced. Control: P12∉Γ234, genuinely false. `genpos_ok` checks Transversal, P_ij≠M, non-collinear second-point triples, and additionally non-collinear centres. These are the Lean hypotheses, a superset for `clifford` and exactly GenPos for cliffordchain. Note that it tests the classical point, not the Lean `cp` formula. That is fine given "from the mathematics".
- **n=5 and n=6.** Genuine tests. The n=5 control replaces a point by P12. The n=6 control uses the other intersection of C₀ and C₁. Both are genuinely false. n=6 caveat as in N10.
- **Five circles.** T_i = A_{i−2}A_{i−1} ∩ A_iA_{i+1}, so T_{i±1} lie on line A_{i−1}A_i ✓. M_i is the second intersection of circles i and i+1 ✓. All 15 points are ≥1e-2 apart ✓. Control: replace M₄ by A₀ ✓.
- **Lester orientation.**
  - The script's `apex` reproduces Lean `apexOut`/`apexIn` exactly: ccw → B+(C−B)·conj ω outward. `Ccw` is cyclically invariant, so one global `ccw` flag is correct for all three sides.
  - However, (i) the code comment explicitly copies "Lean's Ccw", so "written from the mathematics rather than from the Lean code" (479–480) is not quite true for this row.
  - (ii) The conclusion is symmetric in F₁ and F₂, so a swapped in/out convention would pass undetected. The orientation convention is therefore not tested. This is harmless for truth, but it should not be read as validation of `apexOut`.
  - F is the intersection of two of the three lines; that is fine.
  - Control: centroid for N. Generally false ✓.
- **Thébault.** `findroot` solves dist(P,AD)=dist(P,BC)=r and |PO|=R−r, with the side conditions checked afterwards ✓. Control: centroid for incentre ✓.
- **Kosnita.** P = AOa∩BOb, then the residual of C,Oc,P ✓. The hypothesis margins match. Control: Oa in place of Oc. False ✓.
- **Steiner–Lehmus.** The bisector-foot ratios are correct (AE/EC = c/a, AF/FB = b/a). The search fixes θ and root-finds t=|AC| from random starts. That is a genuine counterexample search, though weak: Newton returns the nearby root. There is **no negative control**, which contradicts 481 ("a deliberately false variant of each theorem").
- **Blundon.** R and r are computed from the sides; the margin is ≥0 ✓. The control "drop the root term" is a genuinely false universal bound ✓. Stated honestly as 310/1000. But 507, "in the re-run every control was violated", contradicts 310/1000 and the absent SL control. Reword as "every control except Blundon's (310/1000) was violated in every trial; Steiner–Lehmus has none".
- **"all eight developments" (479).** No row exercises cliffordchain's `Chain`/`CliffordChain` predicate. The n=4,5 rows cover its mathematics only. Say "the theorems of all eight".

**d. Bridge paragraph (243–253) against `Clifford/Bridge.lean`.**

- All five statements are as described:
  - `transversal_iff` is at :58, so anchor Bridge:58 is correct, with M=0;
  - `triP_ne_zero_iff` :62;
  - `cycP_ne_zero_iff` :83 needs pairwise Transversal plus non-collinear centres;
  - `genTriple_iff` :110 needs only Transversal;
  - `onCircleM_iff_mem_sphere` :104 is `sphere c ‖c‖`.
- Identity `cross_second` (:70): X · [conj(a−b)conj(a−c)conj(b−c)(a−b)(a−c)(b−c)] = triP²·cycP. The bracket is ∏|cᵢ−cⱼ|² ✓. Its hypotheses are only a≠b, a≠c, b≠c (the paper omits these; fine).
- All 7 Bridge declarations are in the cliffordchain REQUIRED list ✓.
- BRIDGE_REPORT gives the counterexample for the uncorrected statement ✓.

**e. Ablation (552–557) against `reports/jack_clifford_ablation_partial.jsonl`.** The `.md` reports are stale; this JSONL is the receipt.

- NEEDED counts: clifford_one 10/10, clifford_two 20/20, clifford_three 41/41.
- UNUSED binders:
  - clifford_two_explicit: 5 (n135, n145, n235, n245, n345);
  - five_NN: 6 (n125, n135, n145, n235, n245, n345);
  - ZD_ne_zero: 4 (n156, n256, n356, n456).
- "All involve circle 5 or 6" ✓. All 37 ablation controls are ok.
- The file is labelled *partial*: 37 of the 38 hypothesis-bearing declarations were ablated (`den3_eq_zero_of_collinear` is missing). The text makes no claim about it, so this is OK. The paper should cite this JSONL, since no .md summary exists.

**f. Satisfiability.** ✓ (N5).

**g. OOM.** ✓ (N3), with the nit noted there.

**h. Counts.** All correct:
- 21 files and 4,475 lines;
- cliffordchain: 4 files, 1,105 lines (Basic 724, Clean 257, Bridge 121, root 3);
- REQUIRED lists 20/21/19/12/11/6/5/3, total 97.

## 3. New over-claims and inconsistencies

**X1 (MAJOR). "Same source trees" (512) and "hashes agree across the two machines" (471) are false for the current snapshot.**

- `gates_jack.log` gated cliffordchain *before* the bridge: 3 files, root `Clifford.lean` 2bc4e5…, "PASS (14 declarations)". `manifest_john.log` and `src/` have root d97d04… plus `Bridge.lean`.
- The john battery for cliffordchain (`john_clifford_j_20261013_221029`, 96 theorems, 0 mentions of any bridge lemma) also predates Bridge.lean. So 297 declarations, 490 mutants, "every tested binder was needed" in cliffordchain, and the linter claim all exclude the 7 new declarations. The 21-declaration PASS has only BRIDGE_REPORT as its receipt.
- Local `Lester/Basic.lean` (bf6ada…) and `Kosnita/Basic.lean` (2218c6…) differ from both john (c76de8…, 5c0d52…) and jack after this round's docstring edits. These are docstring-only changes, but they have never been re-gated or re-hashed.
- **Fix:** re-run the gates and hashes on both machines over the final tree, run the battery on cliffordchain including Bridge, then fill the table. Until then, make 471 conditional and change 512 to "on the trees of 13–14 Oct (cliffordchain before Bridge.lean was added)".

**X2 (MAJOR). Linter (560): "no warnings in any library file" has no receipt.**
- The `\PH{clifford linter}` was removed.
- No report in `reports/` contains a linter result for `clifford`: the jack files have no "lint" entry.
- No report contains one for `Bridge.lean` either.
- Restore the seven-development wording or supply the receipt.

**X3 (MINOR). The disclosure of non-reproducible agent-only figures was deleted, but several of those figures are still asserted.** None of them is reproduced by `paperd_numerics.py`:
- 207–209: n=5 line case, spacing 0.042, collinear to 5e-60;
- 284–285: five-circles collinear case, 1e-39;
- 333–336: exactly one Thébault circle per angle, on 1989 triangles;
- 353–355: three Kosnita locus triangles with parallel lines.

The "line case genuine" rows (403, 405) rest on these. Either add them to the scripts (cheap) or keep a one-line disclosure that these come from the unarchived agent runs.

**X4 (MINOR). Negative-control claims overstate (481, 507).** Steiner–Lehmus has no control, and Blundon's is 310/1000 (§2c).

**X5 (MINOR). "Written from the mathematics rather than from the Lean code" (479–480).** The Lester row mirrors Lean's `Ccw`/apex convention, and its symmetric conclusion cannot detect a convention error (§2c).

**X6 (MINOR). The n=6 hypothesis check is indirect** (N10 residual).

**X7 (MINOR). Kosnita module docstring** (N8 residual), and the Kosnita section is unchanged (N6, N7).

**Nits:**
- 476–478: "its reports … Their scripts" (number agreement).
- `paperd_examples.py` and the ablation JSONL are not named in the paper.
- The 24 OOM contradictions are not visible as OOM in the archived file.

The PH placeholders at 415 and 568 are fine. 472 is the exception: the sentence before it pre-commits (X1).
