# Paper C — Layers 14/15 integration report

Date: 2026-10-22. Machine: john (arm64 macOS). All work done inline. Nothing committed, nothing pushed.
Outputs: `~/lean/pubC_barbier` and `~/lean/pubC_fourvertex`, each copied with `cp -a` from the L14 copy. The `.git` directory (published history) and the `.lake/packages` symlink are kept.

## Method (both repos)
- `scratch/` removed. No stray logs were present.
- `<Lib>/L15Classical.lean` was built from `<l15 copy>/scratch/L15_compare.lean`:
  - Header docstring as specified.
  - The writer block (scratch lines 17–264) sits inside `namespace <Lib>.Classical`. A `diff` against the scratch file confirms it is **byte-identical** (VERBATIM_OK).
  - The L15C comparison section follows in the same namespace.
  - Removed: `set_option linter.unusedVariables false` and the trailing `#print axioms` lines.
  - The scratch file imported the root module (`import Barbier` / `import FourVertex`), which is a build cycle inside the library. It was replaced by `import Mathlib` plus the root file's own import list, which is the same set of modules.
- `import <Lib>.L15Classical` is appended as the last line of the root file.
- REQUIRED in gate.sh is extended. A diff against the L14 gate.sh shows only the `REQUIRED=` line changed.
- Gate and tamper were run with `~/lean/jl -g` (GNU mode).
- No `set_option maxHeartbeats` was needed anywhere, so no restructuring was required.
- Counterexample theorems (`¬ classical_…`): **none** exist in either scratch file. No writer statement was shown false.

## barbier  (`~/lean/pubC_barbier`, published commit 7baae04)

| new file | lines | sha256 |
|---|---|---|
| Barbier/L14.lean | 290 | 0add7ccd1a76799cbd3be28585f9ed85993ef6a8dba847b25586125ed62afcec |
| Barbier/L15Classical.lean | 578 | b7894cd0ab92dbacca26d6591683b9a6350ed36d8354507cadf557621ada0cc5 |

- **REQUIRED:** 62 (published) → 82 (L14) → **96** (final).
- **Added (14):** `Barbier.Classical.{cov_supportFn_obligation, isPlaneConvexBody_iInter, cov_C1_a_support, cov_C1_b_part, cov_C1_a_part, cov_C1_b_equiv_part, isPlaneConvexBody_reuleaux, reuleaux_not_disk, cov_C2_a_part, cov_C2_b_part, cov_C2_c_disk_area, cov_C2_reuleaux_polygon_part, angle_equilateral, cov_C2_boundary_part}`. These are all `cov_*` theorems and all NEW PROOF lemmas. The obligation proof is `cov_supportFn_obligation`.
- **Build:** `lake build` rc 0, "Build completed successfully (8719 jobs)". The only warnings are unused-binder warnings in the verbatim writer `def`s.
- **Gate:** `PASS (96 declarations, standard axioms only)`. Every report is `[propext, Classical.choice, Quot.sound]`.
- **Tamper:** sorry / ax2line / evalfake / macro / falsehyp / wrap all rejected. `ALL TAMPERING TESTS REJECTED`.
- **Forbidden grep** on L15Classical.lean (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval`): **0 hits**. No machine paths in the README or the new files.
- **Hashes:** published HEAD vs working tree, sha256 prefix:

| file | HEAD | now | |
|---|---|---|---|
| Barbier/Arclen.lean | 020d752eff5cd9b7 | 020d752eff5cd9b7 | same |
| Barbier/ArclenFinite.lean | 19135dcb6f225bce | 19135dcb6f225bce | same |
| Barbier/Basic.lean | 7732afa0bbfc4545 | 7732afa0bbfc4545 | same |
| Barbier/Bridge.lean | b3bfda483e795b8d | b3bfda483e795b8d | same |
| Barbier/BridgePiecewise.lean | 90b7b22d22bd1bdc | 90b7b22d22bd1bdc | same |
| Barbier/ConvexBodyBridge.lean | 0034be9474c24436 | 0034be9474c24436 | same |
| Barbier/Examples.lean | 1ff02ddb985150d7 | 1ff02ddb985150d7 | same |
| Barbier/Piecewise.lean | 36650d1a5a16d124 | 36650d1a5a16d124 | same |
| Barbier/Reuleaux.lean | 48aa7fd90a919d3e | 48aa7fd90a919d3e | same |
| Barbier/ReuleauxLength.lean | a9856c24d758caff | a9856c24d758caff | same |

- **README:** added a "Layers 14 and 15" section. The count was updated 62 → 96 in three places: Status line, Verification paragraph, PASS line.
- **Dropped:** nothing.
- `git status --short`:
```
 M Barbier.lean
 M README.md
 M gate.sh
 D scratch/Ax.lean
?? Barbier/L14.lean
?? Barbier/L15Classical.lean
```

## fourvertex  (`~/lean/pubC_fourvertex`, published commit 14d1044)

| new file | lines | sha256 |
|---|---|---|
| FourVertex/L14.lean | 138 | ac7b7250a03400dd269b4c4a24ef138d13f9390df3d00e036940b104e889988d |
| FourVertex/L15Classical.lean | 727 | e787752b2e699b69242008eddc5bee277e00ff979ee3a5c3b8e4067ad0144205 |

- **REQUIRED:** 48 (published) → 59 (L14) → **66** (final).
- **Added (7):** `FourVertex.Classical.{cov_supportFn_obligation, isPlaneConvexBody_iInter, cov_C3_a_part, cov_C3_a_precise_part, cov_C3_a_doCarmo_part, cov_C3_remark_circle, cov_C3_remark_ellipse}`.
- **Build:** rc 0, "Build completed successfully (8715 jobs)".
- **Gate:** `PASS (66 declarations, standard axioms only)`. Every report is `[propext, Classical.choice, Quot.sound]`.
- **Tamper:** all six rejected. `ALL TAMPERING TESTS REJECTED`.
- **Forbidden grep** on L15Classical.lean: **0 hits**. No machine paths.
- **Hashes:**

| file | HEAD | now | |
|---|---|---|---|
| FourVertex/Basic.lean | 7978f1087d65d9e8 | 7978f1087d65d9e8 | same |
| FourVertex/Bridge.lean | a0143bd9e7818475 | a0143bd9e7818475 | same |
| FourVertex/Curvature.lean | c5c1a82e28bbdd7a | c5c1a82e28bbdd7a | same |
| FourVertex/Examples.lean | b46a536332697d95 | b46a536332697d95 | same |
| FourVertex/Support.lean | b0f85836e1303d4a | b0f85836e1303d4a | same |
| FourVertex/Vertices.lean | a48c2a38e6e5f0c3 | a48c2a38e6e5f0c3 | same |

- **Edits to proof text (not to writer statements):**
  - The proofs referred to `PaperCClassical.signedCurvature` by its full name. These were renamed to `FourVertex.Classical.signedCurvature`, which is required by the namespace move.
  - The dead helper `lemma sc_periodic : … → True := fun _ => trivial` was deleted. It was unused and trivial; the real lemma `sc_periodic'` is kept.
- **README:** added a "Layers 14 and 15" section. The count was updated 48 → 66 in three places.
- **Dropped:** only the trivial `sc_periodic` above. No cov/NEW PROOF theorem was dropped.
- `git status --short`:
```
 M FourVertex.lean
 M README.md
 M gate.sh
 D scratch/Ax.lean
?? FourVertex/L14.lean
?? FourVertex/L15Classical.lean
```

## Notes
- `scratch/Ax.lean` is tracked in the published repos. Removing `scratch/` as instructed therefore shows up as ` D scratch/Ax.lean`.
- The published gate.sh header comment still says REQUIRED covers "every name queried by scratch/Ax.lean". It was left as is, because only the REQUIRED line may change. Restore that file or reword the comment before publishing if you want them to match.
- The two scratch writer files are identical apart from the import line, so both repos carry the same 34 writer definitions and statements: 17 `classical_*`, 2 `obl_*` and 15 supporting defs.
- The proved obligation is `obl_supportFn` (via `cov_supportFn_obligation`). `obl_perimeter` is not proved in either scratch file.
- Uncovered statements in each repo remain plain `def … : Prop`.

## Commit step

Date: 2026-10-22, on john. All work done inline. **Nothing pushed.**

Common to both copies:
- `git fetch origin` succeeded. `git log --oneline HEAD..origin/main` is **empty**: origin/main equals the copy's base commit. No stash or merge was needed.
- Both copies were in detached HEAD at the base commit, which is also the local `main` (= origin/main). I ran `git switch main`, which carried the working changes over, so the commit sits on `main`. `main` is now `[ahead 1]` of origin/main.
- (b) Gate fix: **no, not needed**. gate.sh already had the portable line `chk=".gatecheck_$$.lean"` (it is in the published commit; no `mktemp --suffix` remains), and `.gitignore` already lists `.gatecheck_*`.
- (c) Build, gate and tamper were run with `~/lean/jl` in default system/BSD-tools mode, without `-g`.
- `git add -A` staged only the intended files. `.lake/` is ignored, and there were no scratch or log files.
- Commit author and committer: `Josh Bald <jpbald93@gmail.com>`.

### barbier (`~/lean/pubC_barbier`)
- Origin commits merged: none.
- Gate fix: no (already portable).
- Build: `Build completed successfully (8719 jobs).`
- Gate: `PASS (96 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, falsehyp, wrap)
- New commit: `0dd68bdeb06ee35b1db95baa8b896419c0c571b4`
- Committed changes: M Barbier.lean, A Barbier/L14.lean, A Barbier/L15Classical.lean, M README.md, M gate.sh, D scratch/Ax.lean
- `git log --oneline -3` (the history has only 2 commits):
```
0dd68bd Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
7baae04 Barbier / four-vertex initial release (Lean 4.33.1, Mathlib 0df444a3)
```
- `git status --short`: (empty, clean)

### fourvertex (`~/lean/pubC_fourvertex`)
- Origin commits merged: none.
- Gate fix: no (already portable).
- Build: `Build completed successfully (8715 jobs).`
- Gate: `PASS (66 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, falsehyp, wrap)
- New commit: `8f2ae82c75f28701e4b720c353e6be9468c71891`
- Committed changes: M FourVertex.lean, A FourVertex/L14.lean, A FourVertex/L15Classical.lean, M README.md, M gate.sh, D scratch/Ax.lean
- `git log --oneline -3` (the history has only 2 commits):
```
8f2ae82 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
14d1044 The four-vertex theorem for convex ovals (Lean 4.33.1, Mathlib 0df444a3)
```
- `git status --short`: (empty, clean)

### Open item
- The gate.sh header comment (line 16) still says REQUIRED covers "every name queried by scratch/Ax.lean". This commit deletes that file, so the comment is now out of date. Reword it before pushing if you want them to match.

### Re-verification (2026-10-22, later run)
The commit step was requested again. I checked john's state first and found the commits above already in place, so I made no new commits and changed nothing:
- `git fetch origin`; `git log --oneline HEAD..origin/main` is empty in both copies. Both are on `main` at `[ahead 1]`. Nothing pushed.
- gate.sh line 34 is `chk=".gatecheck_$$.lean"` in both, and `.gitignore` line 9 is `.gatecheck_*`. No `mktemp --suffix` is present.
- I re-ran the checks with `~/lean/jl` in system/BSD mode, without `-g`:
  - barbier: `Build completed successfully (8719 jobs).`, `PASS (96 declarations, standard axioms only)`, `ALL TAMPERING TESTS REJECTED`. HEAD is `0dd68bd`.
  - fourvertex: `Build completed successfully (8715 jobs).`, `PASS (66 declarations, standard axioms only)`, `ALL TAMPERING TESTS REJECTED`. HEAD is `8f2ae82`.
- After gate and tamper, `git status --short` is empty in both. The only ignored entry is `.lake`.
