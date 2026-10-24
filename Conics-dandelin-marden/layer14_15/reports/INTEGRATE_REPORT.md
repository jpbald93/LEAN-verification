# Integration report: Layers 14 and 15, Paper Conics (dandelin, marden)

Machine: jack (`jack`). All work was done inline; no sub-agents were used. Builds, gates and tamper runs used `flock ~/l15jack.lock`. Nothing was pushed.

## Starting point (addendum a)
- `git fetch origin` was run in both copies. GitHub HEAD (`master`) **equals the published commit** in both repos: dandelin `205e480`, marden `bd2cd3c`. There were no later commits (no CITATION.cff, no portable gate), so no fast-forward was needed. The copies were taken off detached HEAD onto `master`, which tracks `origin/master`.
- `~/pubConics_<repo>` = `cp -a` of `~/l14Conics_<repo>`, keeping `.git` and the `.lake/packages` symlink (→ `~/barbier/.lake/packages`).
- **`scratch/` was NOT removed, and neither was marden's `ax.log`.** Both are *tracked files of the published commit*, and README and paper cite them as recorded axiom outputs. Deleting them would change published content. No untracked stray logs or scratch files were present (`git clean -nd` listed only `L14.lean`).

## Common changes (both repos)
- New `<Lib>/L15Classical.lean`, made from the L15 scratch file (byte-identical to `AFM/L14L15/Conics/L15_scratch/`). Changes:
  - `import <Lib>` was replaced by imports of the published modules, which avoids an import cycle.
  - The scratch header docstring was replaced by the required Layer-15 docstring plus a short note on the packaging.
  - `namespace PaperConicsClassical` became `<Lib>.Classical`.
  - All `#print axioms` lines were removed.
  - The "(verbatim from /tmp/…)" and "(NEW, scratch only)" section headers became "(verbatim)" and "(NEW)".
  - Writer definitions and `classical_*` statements are unchanged, character for character.
- No `set_option`, macro, notation, `#check`, `#eval` or `run_cmd` was present, so no proof needed restructuring. **Nothing was dropped.**
- **No counterexample theorems.** L15 found no false writer statement, so no `¬ classical_…` theorem exists to carry over.
- One line `import <Lib>.L15Classical` was appended at the end of the root file, after `import <Lib>.L14`.
- `gate.sh`: the REQUIRED line was extended. **(addendum b)** The GNU-only line `chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)` was replaced by `chk=".gatecheck_$$.lean"`, the form used at desargues HEAD `53efa45`. `.gitignore` already contained `.gatecheck_*`. `tests/tamper.sh` already uses portable `mktemp -d`, so it was not touched.
- **(addendum c) README fixes:**
  - **dandelin, stale count:** the published README said "75 named declarations" and "PASS (75 …)", but the published gate checks **85**. Both are now 158.
  - **Both repos, inaccurate log reference:** the README said recorded outputs "are the `*.out` files there and the log files at the repository root".
    - dandelin has no root log files, so the text now says only the `*.out` files.
    - marden has no `*.out` files, so the text now says its recorded output is `ax.log` at the root.
  - The "every Lean name cited in the paper…" parenthetical now also mentions the L14 and L15 declarations.
- No Lean docstring needed fixing:
  - L15's "NEW" results (any sphere tangent to all generators is an axis sphere; the Marden ellipse lies in the triangle) go *beyond* the repo's claims.
  - Repo docstrings already say "axis spheres" or "in focal form", so they are not overclaims.
  - No published proof or statement was edited.

## Repo: dandelin
| file | lines | sha256 |
|---|---|---|
| `Dandelin/L14.lean` | 732 | `22dd08271f5207808cdc3e203f27c12b0a8579dc15516475de4e1d47b392d365` |
| `Dandelin/L15Classical.lean` | 1555 | `77e41d95aaaace42750e1ec276e9d10ca26b73c6dda0184ab5925724081db016` |

- REQUIRED: published **85** → L14 **102** → final **158**. The 56 added declarations are 8 `cov_*` plus 48 `l15_*` (bridges, new proofs and setup lemmas, including `l15_S`).
  - `cov_*`: Conics1_a, 1_b, 2_a, 2_b, 3_obligation (the construction obligation, proved), 3_a, 3_b, 3_parabola_unique.
  - Not gate-listed: the writer's `def`s (`cone`, `IsDandelinSphere`, `classical_*` …), which are reference statements.
- Build: `lake build` rc 0 (8716 jobs).
- Gate: `PASS (158 declarations, standard axioms only)`. All 158 report `[propext, Classical.choice, Quot.sound]`. It was re-run after the commit with the same result.
- Tamper: `ALL TAMPERING TESTS REJECTED`.
- Forbidden grep on `L15Classical.lean` (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check`): **0 hits** (raw, comments included).
- Not proved (unchanged from L15): `classical_Conics3_c` (planar standard-form converse). No writer statement was shown false.
- Commit **`89309188e77f1564fd31cc9a2d245dbba1b34f8c`**. Author and committer are `Josh Bald <jpbald93@gmail.com>`. The branch is `master`, ahead of `origin/master` by 1. Not pushed.

```
8930918 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
205e480 Add bridge lemmas: cone angle/generator forms, plane as affine subspace, tangencies as IsTangentAt
a366dcc README: describe the scratch folder and tamper-test criterion
```
`git status --short` before commit:
```
M  Dandelin.lean
A  Dandelin/L14.lean
A  Dandelin/L15Classical.lean
M  README.md
M  gate.sh
```
After commit: clean (empty).

Hashes. Each pre-existing `.lean` file's working copy was compared with `git show HEAD:<file>`, where HEAD = `205e480`:
| file | sha256 | status |
|---|---|---|
| Dandelin/Basic.lean | 3e385a9f41fa1904a22d8554715e8a7d4c114378ee1ea1aa318a07ea7ebf6031 | same |
| Dandelin/Bridge.lean | 26feef722a5c5da8c32cb7a1d7761c8b3fefd4e09ac81c7e97d06f5e52dc1bae | same |
| Dandelin/Degenerate.lean | 0aa1548719514c99d6535379a6200888bbd50b0ebae5128c43c7a8a23cb18803 | same |
| Dandelin/Directrix.lean | 01cc84a24890dd4876dcb30b238589259f96634038296d327d1b706f3bf4ace1 | same |
| Dandelin/Existence.lean | 12ed8eac7d66daec6abbf0300273048b8a2fd012568e259e6685f81a9a475778 | same |
| Dandelin/Hyperbola.lean | 0415b77fad7b0fbf4f0f69d2063500c6725fb80df7f59fccbfccee826ad99d7b | same |
| Dandelin/Regime.lean | 1081f5348e28cef60735716f58d68ea4fc3b52ec6d6b7b82c87eff866d07a750 | same |
| scratch/Ax*.lean (7 files) | — | same |
| Dandelin.lean | — | changed (+2 import lines) |
| gate.sh | — | changed (REQUIRED + mktemp line) |
| README.md | — | changed (section + count/log text) |

## Repo: marden
| file | lines | sha256 |
|---|---|---|
| `Marden/L14.lean` | 213 | `0e9347dd327cb8acf8856455aa18c559eb5e5b0fe9618967a0051607e335d014` |
| `Marden/L15Classical.lean` | 666 | `b7d85a8d2d63b67baebb94bd47df30b1677fd7d42c167fbc283e2e6a8e54759c` |

- REQUIRED: published **18** → L14 **24** → final **56**. The 32 added declarations:
  - 4 `cov_*`: Conics4_a, Conics4_b_part, Conics5, Conics5_double_root.
  - 9 `Marden.l15_*` bridges.
  - 19 `Marden.Classical.l15_*` new-proof lemmas, including the def `l15_cross`.
  - Note: the published README said 18, which matched the published gate.
- Build: `lake build` rc 0 (8713 jobs).
- Gate: `PASS (56 declarations, standard axioms only)`. All 56 report `[propext, Classical.choice, Quot.sound]`. It was re-run after the commit with the same result.
- Tamper: `ALL TAMPERING TESTS REJECTED`.
- Forbidden grep on `L15Classical.lean`: **0 hits** (raw).
- Partial result (unchanged from L15): `cov_Conics4_b_part` proves only the centre-of-symmetry clause of `classical_Conics4_b`. The area and maximal-area clauses are out of scope; there is no measure theory in the repo. No writer statement was shown false.
- Commit **`b4fbe75198e728699764a9b44e8f9981ba589299`**. Author and committer are `Josh Bald <jpbald93@gmail.com>`. The branch is `master`, ahead of `origin/master` by 1. Not pushed.

```
b4fbe75 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
bd2cd3c README: describe the scratch folder and tamper-test criterion
6f09713 Keep the axiom and build logs cited in the paper at the repository root
```
`git status --short` before commit:
```
M  Marden.lean
A  Marden/L14.lean
A  Marden/L15Classical.lean
M  README.md
M  gate.sh
```
After commit: clean (empty).

Hashes (vs `bd2cd3c`):
| file | sha256 | status |
|---|---|---|
| Marden/Basic.lean | 04f4ca78e3a88618dc5f84ad0ab4db70bb56016b1baa0f00745ba9a954624258 | same |
| Marden/Main.lean | 362eb19696e3ccb9d9a5f56c5045bfd3afc19727b4c9523f6fe7e988c3115e9c | same |
| Marden/Tangent.lean | 43ef5eb1cf819f265d1a1ac9d4803dba2bdc37d141ace0b40c9febc049e880f9 | same |
| Marden/Unique.lean | 4c97d47875a9032ad32dc2b4932294660238ca4b59d1068c65feea303333a248 | same |
| scratch/Ax.lean | 381fbe160866813644bdbf50abb7ce633d679a1f2798c5be30548ce90ca3f97e | same |
| Marden.lean | — | changed (+2 import lines) |
| gate.sh | — | changed (REQUIRED + mktemp line) |
| README.md | — | changed (section + count/log text) |

## Logs on jack
`~/pubConics_build_<repo>.log`, `~/pubConics_gate_<repo>.log`, `~/pubConics_gate2_<repo>.log` (post-commit), `~/pubConics_tamper_<repo>.log`.

## Notes for the owner
- The L14 files declare more lemmas (dandelin 35, marden 12) than REQUIRED lists (17 and 6, the restatements and witnesses chosen in L14). That was left as in L14, and the README wording says so explicitly.
- Before pushing, decide whether you want `scratch/` and `ax.log` kept, as now, since they are cited in the paper.

Status: **COMPLETE** for both repos. Local commits only, not pushed.
