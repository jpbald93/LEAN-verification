# INTEGRATE N — Layer 15 into the arm64 machine:~/lean/paperg_nagel

All work was done inline, with no sub-agent. `~/lean/reformalG` and `~/lean/l15_nagel` were not touched.

## Files
- **Added** `NagelLine/L15Classical.lean` (741 lines, sha256 723687d2c80bd7d1…), namespace `NagelLine.Classical`. Source: `~/lean/l15_nagel/scratch/L15_compare.lean` (sha256 21d65f97…, identical to the workspace `L15_compare_N.lean`). The header comment names `PaperGClassical.lean` and its sha256 prefix 2bb545d76d505fe0.
  - It contains the classical definitions (ClassicalTri … ClassicalAnticompl), all bridge lemmas, the NEW PROOFS (`cevian_unique`, `nagel_unique`, `medial_indep`, `anti_indep`) and all 11 `cov_*` theorems. The proofs are unchanged.
  - Changes from the scratch file (mechanical only):
    1. `import NagelLine` became `import NagelLine.Basic/Main/Extensions/L14`. A library file cannot import the root module, because the root imports this file.
    2. Namespace `PaperGClassicalL15` became `NagelLine.Classical`.
    3. The 14 trailing `#print axioms` lines were removed.
    4. `local notation "Pt" => EuclideanSpace ℝ (Fin 2)` was removed, because `notation` is forbidden both by the task and by the gate's token grep. Every `Pt` was replaced by `(EuclideanSpace ℝ (Fin 2))`. **The definitions and the `cov_` statements are therefore verbatim up to expanding this abbreviation**, which elaborates to the identical terms. This is noted in the file header.
    5. The header docstring was rewritten. The gate's grep also scans comments, so it avoids the words notation/syntax/prefix.
- **Modified** `NagelLine.lean`: +1 line `import NagelLine.L15Classical`.
- **Modified** `gate.sh`: REQUIRED gained 58 names. Nothing else in the file changed.
- **Modified** `README.md`: new section "Layer 15 (classical statements)", with a table of the cov_ theorems and the new proofs in plain English.
- Note: the working tree already held uncommitted Layer-14 work: `NagelLine/L14.lean` (untracked), the `import NagelLine.L14` line, and the l14_ names in REQUIRED. L15 imports L14 and the gate needs it, so **that L14 work is included in the same commit**.

## REQUIRED delta (+58, all `NagelLine.Classical.`)
Definitions (18): ClassicalTri ClassicalBary ClassicalSemiperimeter ClassicalArea ClassicalCentroid ClassicalExcenterA ClassicalExContactA ClassicalExradiusA ClassicalInContactA ClassicalInContactB ClassicalInContactC ClassicalBisectorPoint ClassicalIsogonalLine ClassicalSymmedian ClassicalIsogonalConj ClassicalFoot ClassicalPedalCentroid ClassicalAnticompl
New proofs / bridges (29): proj_congr bary_lin sA sB sC inA_eq inB_eq inC_eq tri_pos inv_helper exA0 exA1 exA2 exC0 exC1 exC2 cevian_unique nagel_unique centroid_lin medial_points_eq medial_indep medial_eq anti_points_eq anti_indep anti_eq col_of_mem centroid_eq_lineMap O_H_lineMap deLongchamps_eq
cov (11): cov_N1 cov_N2a cov_N2b cov_N3 cov_N4 cov_N5 cov_N5_all cov_N6a cov_N6b cov_N7 cov_N8

## Checks
- Build: `Build completed successfully (8712 jobs).`
- Gate: `PASS (149 declarations, standard axioms only)` (was 91 before this change: 77 committed + 14 L14).
- Tamper (`~/lean/jl -g tamper`): sorry/ax2line/evalfake/macro → forbidden token; wrap → nonstandard axioms; falsehyp/falsehyp_ext → build; `ALL TAMPERING TESTS REJECTED`.

## Commit
`f39c6f4ccac2934b9ce548d4f2d32494b835ad22`, author Josh Bald <jpbald93@gmail.com>, message "Layer 15: classical statements and new uniqueness proofs". 5 files, +1186/−1. Not pushed. The working tree is clean.

## Battery
Started detached at Mon Oct 26 06:30:36 PDT 2026 (PID 1927; `serial.sh paperg_nagel` PID 2225 running). The log `~/leancheck/reports/paperg_nagel_l15_batt.log` begins: `START paperg_nagel Mon Oct 26 13:30:37 UTC 2026`.

## cov_ theorems needing changes to compile
None. All proofs compiled unchanged. The only edit that touches statements is the textual `Pt` expansion (item 4 above), which was needed because `notation` is banned in the library.
