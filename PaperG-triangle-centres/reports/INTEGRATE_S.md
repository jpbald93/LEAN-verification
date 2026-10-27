# Paper G — Layer 15 integration (Group S comparer → library), the x86-64 machine `~/paperg_brocard`

## Result
- Gate: `flock ~/l15jack.lock bash gate.sh` → exit 0, **`PASS (147 declarations, standard axioms only)`**. Before: 88. Full output: `the x86-64 machine:~/l15_integrate_gate.out`.
- Tamper: `flock ~/l15jack.lock bash tests/tamper.sh` → exit 0, **`ALL TAMPERING TESTS REJECTED`** (sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp2). Output: `the x86-64 machine:~/l15_integrate_tamper.out`.
- Commit (local, not pushed): **`016c5b9375fea7face119a3e5ddc1a11f3a4e1b6`**, author `Josh Bald <jpbald93@gmail.com>`, message "Layer 15: classical statements and new uniqueness proofs".
- Battery started detached at 13:31:55 UTC. Log `~/leancheck/reports/paperg_brocard_l15_batt.log`, first line: `START paperg_brocard Mon Oct 26 01:31:55 PM UTC 2026`. Process: `bash ~/leancheck/serial.sh paperg_brocard` (PID 1744554). This report does not include battery results.

## Files added / changed
- **Added `Brocard/L15Classical.lean`** (723 lines, sha256 d7dbc86eb1ca1742…). It starts with `import Brocard.L14`, and its namespace is `Brocard.Classical`.
  - Header comment: names `PaperGClassical.lean` and sha256 prefix `2bb545d76d505fe0`.
  - The file is the scratch file `~/l15_brocard/scratch/L15_compare.lean` (sha256 7e0af132…) with these mechanical changes only:
    - `import Brocard` → `import Brocard.L14`, so the library root does not import itself.
    - `namespace/end L15CmpS` → `Brocard.Classical`.
    - The 13 `#print axioms` lines were removed.
    - `local notation "Pt" => EuclideanSpace ℝ (Fin 2)` → `abbrev Pt := EuclideanSpace ℝ (Fin 2)`. `notation` is forbidden by the task and by the gate's token check.
    - A module docstring was added.
  - All proofs are unchanged.
  - The whole "Basic definitions" block (all 18 definitions, 3758 bytes) was checked by script: it occurs byte-for-byte in the classical file `the x86-64 machine:~/PaperGClassical.lean` (sha256 2bb545d76d505fe0…).
  - The gate's forbidden-token grep finds nothing in the file. It also contains no `#print`/`#check`. For this, the header wording avoids the words "prefix"/"syntax", which the grep would flag.
- **`Brocard.lean`**: one line added, `import Brocard.L15Classical`.
- **`gate.sh`**: the 59 new names appended to REQUIRED. No other change.
- **`README.md`**: new section "Layer 15 (classical statements)".
- **Also in the commit**: Layer 14 was uncommitted in the working tree when I started: `Brocard/L14.lean` untracked, its `import Brocard.L14` line, and its 21 `l14_*`/`l14w_*` REQUIRED names. I did not edit these. They are committed here because L15Classical imports L14 and uses its lemmas (`l14_drozFarny`, `l14_symmedianPoint_eq_centroid_pedal`, …). So the commit diff shows 2 import lines in `Brocard.lean`; only `import Brocard.L15Classical` is from this task.
- No other existing library file was touched.

## REQUIRED delta (+59, all `Brocard.Classical.*`)
- Definitions (20): Pt, ClassicalTri, ClassicalBary, ClassicalSemiperimeter, ClassicalArea, ClassicalCentroid, ClassicalExcenterA, ClassicalExContactA, ClassicalExradiusA, ClassicalInContactA, ClassicalInContactB, ClassicalInContactC, ClassicalBisectorPoint, ClassicalIsogonalLine, ClassicalSymmedian, ClassicalIsogonalConj, ClassicalFoot, ClassicalPedalCentroid, ClassicalAnticompl (18 classical definitions plus `Pt`), and the helper `basis3`.
- Instance: factFinrankPt.
- NEW-PROOF lemmas: refl_vec, range3, span_top, interior_eq, coords_of_interior, interior_of_weights, bary_vsub, symm_mem, symm_dir, ne01, ne02, ne12, K_vsub, tri_facts, brocard1_unique, brocard2_unique, brocard1_interior, brocard2_interior, brocard1_spec, brocard2_spec, isog_vertex, hull_rot, indep_rot, meet_unique, lines_transverse.
- cov_ theorems (13): cov_S1a, cov_S1b, cov_S2a, cov_S2b, cov_S3a, cov_S3b, cov_S3c, cov_S3d, cov_S3e, cov_S4, cov_S5, cov_S6, cov_S7.

All 59 report `[propext, Classical.choice, Quot.sound]`.

## cov_ theorems needing changes to compile in the library
**None.** All 13 `cov_*` statements and proofs are unchanged in content. The only thing that differs is the `Pt` abbreviation, which is the same term as the old notation, and the build needed nothing else. The build has three linter warnings, the same ones as in the scratch file: unused `hC` (cov_S1b), `hu`, `hv` (cov_S7).

## Process
- All work was inline; no sub-agent.
- No `lake update`/`cache get`, no push, no processes killed.
- Builds, gate and tamper ran under `flock ~/l15jack.lock`. `lake build` took 13 s (8714 jobs).
