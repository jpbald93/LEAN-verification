# Paper E — Layers 14 and 15 integration report (2026-10-22)

Machine: jack (x86_64), `jack`. Toolchain: Lean v4.33.1; `.lake/packages` → `~/barbier/.lake/packages`.
Publication-ready copies: `jack:~/pubE_newton` (published commit 48e94cf) and `jack:~/pubE_miquel` (published commit 011c9ec).
Each copy is the L14 copy from john (`~/lean/l14E_*`, sent by tar over ssh without `.lake`) with `L14_REPORT.md` moved out to `jack:~/l14E_reports/`. I also unset the macOS-only `core.ignorecase`/`core.precomposeunicode` that came across in `.git/config`. There was no `scratch/` directory and no stray logs. `.git` is kept. Nothing was committed or pushed.

## How L15Classical.lean was made (both repositories)
- Source: `<l15 copy>/scratch/L15_compare.lean`. It is byte-identical to `AFM/PaperE/layer15/L15_compare_{newton,miquel}.lean`. The comparer had already checked that its writer definitions match the writer's `Classical.lean` (sha256 8e1e634a…) exactly, and that each `cov_X` statement matches the writer's `classical_X`.
- Changes, made by a script (`tmp/integ/E/scripts/mk.py`):
  - `import <Lib>` became explicit imports of the library modules. This avoids an import cycle, because the root file now imports L15Classical.
  - Added the required Layer-15 header docstring. The writer's original header is kept after it.
  - Namespace `ClassicalQuadrilateral` renamed to `<Lib>.Classical`. This touches 3 lines: `namespace`, `open`, `end`.
  - Removed the 9 `#print axioms` lines.
- Nothing else changed. The writer's definitions and statements are verbatim. There was no `set_option`, `macro`, `notation`, `run_cmd`, `#check` or `#eval` to remove, and no proof needed restructuring.
- **Counterexamples: none.** No writer statement is false, so no `¬ classical_…` theorems exist.
- **Dropped: nothing.**

## quadnewton (`~/pubE_newton`)
- New files:
  - `QuadNewton/L14Newton.lean`: 832 lines, sha256 `7554fe86600450803b3229f775bccab1b97a5187fdbada57f822fb46ede1b877`. Identical to john's L14 copy.
  - `QuadNewton/L15Classical.lean`: 428 lines, sha256 `ebfce42e8deff7ad17f8005b48f2e73d64b64d872b053329ac1e433a3c08f6b3`.
- Root file: `import QuadNewton.L14Newton` (from L14) and `import QuadNewton.L15Classical` appended at the end.
- REQUIRED: published **35** → L14 **70** → final **81**. The 11 added names are:
  - obligations: `QuadNewton.Classical.Configuration.vertex_exists_unique`, `…Configuration.triangle_independent`
  - NEW PROOF lemmas: `QuadNewton.Classical.cross_iff_dot`, `QuadNewton.Classical.radical_eq_line`
  - `QuadNewton.Classical.cov_E1_a`, `cov_E1_b`, `cov_E2_a`, `cov_E2_b`, `cov_E3_a`, `cov_E3_b`, `cov_E4_a`
- `lake build`: rc 0 (`Build completed successfully (8714 jobs)`).
- Gate: `PASS (81 declarations, standard axioms only)`. All 81 report `[propext, Classical.choice, Quot.sound]`.
- Tamper: `ALL TAMPERING TESTS REJECTED`.
- Forbidden grep on L15Classical.lean (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check`): **0 hits**, raw count, comments included.
- Hashes of the published library files (sha256 prefix, HEAD vs working tree):

| file | HEAD | now | |
|---|---|---|---|
| QuadNewton/Basic.lean | 7514740705648ce8 | 7514740705648ce8 | same |
| QuadNewton/Bridge.lean | 902c885b3fe53ae1 | 902c885b3fe53ae1 | same |
| QuadNewton/Core.lean | b005e0198ac94777 | b005e0198ac94777 | same |
| QuadNewton/Lines.lean | 55d37f730c57fddb | 55d37f730c57fddb | same |
| QuadNewton/Quad.lean | 06783cf3344b232b | 06783cf3344b232b | same |
| QuadNewton.lean (root) | 5cb4e2e86eefa5a8 | 84eeef2f80869211 | changed (+2 import lines) |

- README: added a "Layers 14 and 15" section. Updated the declaration count 35 → 81 in three places (Status, Verification, Expected output). The README contains no machine paths.
- `git status --short`:
```
 M QuadNewton.lean
 M README.md
 M gate.sh
?? QuadNewton/L14Newton.lean
?? QuadNewton/L15Classical.lean
```

## quadmiquel (`~/pubE_miquel`)
- New files:
  - `QuadMiquel/L14Miquel.lean`: 861 lines, sha256 `060f567bb1178563c35298095ace5332c48fb2fd899c4b000ada50a3ac6649a9`. Identical to john's L14 copy.
  - `QuadMiquel/L15Classical.lean`: 392 lines, sha256 `4f51168791c80e992e6b0a0272a3ced74a2e7c79d572b278ebe268d769553469`.
- Root file: `import QuadMiquel.L14Miquel` (from L14) and `import QuadMiquel.L15Classical` appended at the end.
- REQUIRED: published **62** → L14 **95** → final **104**. The 9 added names are:
  - obligations: `QuadMiquel.Classical.Configuration.vertex_exists_unique`, `…Configuration.triangle_independent`
  - `QuadMiquel.Classical.cov_E5_a`, `cov_E5_a_unique`, `cov_E6_a`, `cov_E7_a`, `cov_E7_b_part`
  - `cov_E7_b`, which is the NEW PROOF: feet not all equal for arbitrary M
  - `cov_E8_a`
- `lake build`: rc 0 (`Build completed successfully (8716 jobs)`).
- Gate: `PASS (104 declarations, standard axioms only)`. All 104 report `[propext, Classical.choice, Quot.sound]`.
- Tamper: `ALL TAMPERING TESTS REJECTED`.
- Forbidden grep on L15Classical.lean: **0 hits**.
- Hashes:

| file | HEAD | now | |
|---|---|---|---|
| QuadMiquel/Algebra.lean | 95b548bc2ee7b7c8 | 95b548bc2ee7b7c8 | same |
| QuadMiquel/Basic.lean | f7b4da7d2abf6c1f | f7b4da7d2abf6c1f | same |
| QuadMiquel/Bridge.lean | fb6f3e39230d5279 | fb6f3e39230d5279 | same |
| QuadMiquel/Frame.lean | 1e7cbfc90348e688 | 1e7cbfc90348e688 | same |
| QuadMiquel/Miquel.lean | 5ce67f6891f4ec1c | 5ce67f6891f4ec1c | same |
| QuadMiquel/Parallel.lean | ea33070625a61685 | ea33070625a61685 | same |
| QuadMiquel/Simson.lean | 69b49c142ec7435e | 69b49c142ec7435e | same |
| QuadMiquel.lean (root) | 40e264fd0c8b0dd9 | cc62d1b9c00efffc | changed (+2 import lines) |

- README: added a "Layers 14 and 15" section. Updated the count 62 → 104 in three places. No machine paths.
- `git status --short`:
```
 M QuadMiquel.lean
 M README.md
 M gate.sh
?? QuadMiquel/L14Miquel.lean
?? QuadMiquel/L15Classical.lean
```

## Notes
- In both gate.sh files only the REQUIRED line differs from L14 (`diff` shows 1 line changed).
- The bridge helper lemmas (`rl_d_ne`, `genPos`, `vertex_eq`, `tv0..3`, `range_*`, `H_eq`, `foot_eq`, `miquel_iff`, …) are glue, so they were not added to REQUIRED. They are checked indirectly, because every cov_* theorem depends on them.
- Newton's `cross_iff_dot` and `radical_eq_line` were added as NEW PROOF lemmas, following the comparer's report. Miquel's `miquelPt_isMiquel` and `eq_miquelPt` are glue and were not added.

## Commit step
Done on jack on 2026-10-22. The copies are `~/pubE_newton` and `~/pubE_miquel`. Nothing was pushed.

### quadnewton (`~/pubE_newton`, origin https://github.com/jpbald93/quadnewton)
- Origin commits merged: **none**. `git fetch origin` returned rc 0, and `HEAD..origin/main` is empty: origin/main = HEAD = 48e94cf. So no stash or merge was needed.
- Gate fix: **no**. gate.sh line 26 is already `chk=".gatecheck_$$.lean"`, there is no `mktemp`, and `.gatecheck_*` is already in .gitignore.
- `lake build`: rc 0, `Build completed successfully (8714 jobs).`
- Gate: `PASS (81 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- New commit: `c3a4ce513eb8789f5f0de4ae02efe707a718466c`. Author and committer are both `Josh Bald <jpbald93@gmail.com>`. Changes: 5 files, +1270/−4 (QuadNewton.lean, L14Newton.lean, L15Classical.lean, README.md, gate.sh).
- `git log --oneline -3`:
```
c3a4ce5 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
48e94cf Lean 4 development accompanying Paper E (complete quadrilateral)
```
  The repository has only 2 commits.
- `git status --short`: empty (clean).

### quadmiquel (`~/pubE_miquel`, origin https://github.com/jpbald93/quadmiquel)
- Origin commits merged: **none**. `git fetch origin` returned rc 0, and `HEAD..origin/main` is empty: origin/main = HEAD = 011c9ec.
- Gate fix: **no**. gate.sh line 26 is already `chk=".gatecheck_$$.lean"`, and `.gatecheck_*` is already in .gitignore.
- `lake build`: rc 0, `Build completed successfully (8716 jobs).`
- Gate: `PASS (104 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- New commit: `4089a974d5f56663be3daa5203ec856c28b793c3`. Author and committer are both `Josh Bald <jpbald93@gmail.com>`. Changes: 5 files, +1263/−4 (QuadMiquel.lean, L14Miquel.lean, L15Classical.lean, README.md, gate.sh).
- `git log --oneline -3`:
```
4089a97 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
011c9ec Lean 4 development accompanying Paper E (complete quadrilateral)
```
  The repository has only 2 commits.
- `git status --short`: empty (clean).

### Re-verification (2026-10-22, later run)
- Re-fetched origin for both repos. `HEAD..origin/main` is still empty (origin/main = 48e94cf for newton, 011c9ec for miquel). HEADs are unchanged at c3a4ce5 and 4089a97, and author and committer are both Josh Bald.
- Rebuilt and re-ran the checks. newton: build OK (8714 jobs), `PASS (81 declarations, standard axioms only)`, `ALL TAMPERING TESTS REJECTED`. miquel: build OK (8716 jobs), `PASS (104 declarations, standard axioms only)`, `ALL TAMPERING TESTS REJECTED`.
- `git status --short` is empty for both after the runs. No new commit was needed and nothing was pushed.
