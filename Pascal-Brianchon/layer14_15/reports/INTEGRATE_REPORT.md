# INTEGRATE REPORT — Paper Pascal, Layers 14 + 15

Date: 2026-10-23 · Machine: john (arm64 macOS) · All work inline, no subagents.

## pascal-hexagon → `~/lean/pubPascal_pascal-hexagon`

**Start point.** The copy was made from `~/lean/l14Pascal_pascal-hexagon`. `git fetch origin` shows that GitHub HEAD is `master` = `726da4d`, the same commit the L14 copy was cloned from, so nothing later needed merging (the remote branch is `master`, not `main`). The L14 copy had a detached HEAD. I checked out `master` (up to date with `origin/master`) so the commit lands on the branch. The `.lake/packages` symlink is kept. There was no `scratch/` directory and no stray logs.

### New files
| file | lines | sha256 |
|---|---|---|
| `PascalHexagon/L14.lean` | 598 | `8c81c04e3416e7b04aa29b349cba1609fe9598716e284db45b414aa6889a6362` |
| `PascalHexagon/L15Classical.lean` | 1596 | `fc3f7bcac9580772d24376f6a9cc4a42607145c48767e91717598c5bc2c219fe` |

**What `L15Classical.lean` contains.** It is made from `l15…/scratch/L15_compare.lean` with these changes:
- The namespace is now `PascalHexagon.Classical` (was `PaperPascalClassical`).
- It has the required Layer-15 header docstring. The writer's original header text is kept below it.
- The two `set_option linter.*` lines are removed.
- It imports `PascalHexagon.L14` instead of the root module, to avoid a cycle.
- The writer's 20 `classical_*` statements and their own definitions (`Pt`, `IsLine`, `OnLine`, `join`, `IsMeet`, `CollinearPts`, `ConcurrentLines`, `OnConic`, `QNondeg`, `NondegConic`, `IsTangentAt`, `IsTangentLine`, `polarLine`) are verbatim.

It has 88 theorems: 20 `cov_*`, one for each `classical_*` statement (construction obligations included), plus 68 NEW-PROOF and bridge lemmas.

- **Counterexamples:** none. Every writer statement was proved as written.
- **set_option / maxHeartbeats:** no proof depended on one. Nothing was dropped.
- **One proof edit:** `cov_Pascal2_b` called the repository's `pappus` and now inlines that theorem's one-term proof (`pascal'` applied to `linePair`). The published tamper test `wrap` swaps `pappus` for a `True`-valued theorem in its scratch copy. With the direct call, that copy failed at build ("FAIL: build" instead of "FAIL: nonstandard axioms"). The statement is unchanged and no published file was edited. After the change, `wrap` is rejected as expected.

`PascalHexagon.lean`: `import PascalHexagon.L15Classical` added as the last line, after the L14 import.

### REQUIRED count
published **32** → L14 **59** → final **147** (+88 `Classical.*` names; only the REQUIRED line changed for this step).

### gate.sh portability (addendum b)
gate.sh line 28 used `chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)`, which is GNU-only. I replaced it with `chk=".gatecheck_$$.lean"`, the form in jpbald93/desargues HEAD. I also added `.gatecheck_*` to `.gitignore`. Nothing else in gate.sh changed.

### Results
- Build: `~/lean/jl build` → `Build completed successfully (8717 jobs).`, rc 0. There are linter warnings (unused simp args) but no errors.
- Gate (system BSD tools, no `-g`): `PASS (147 theorems, standard axioms only)`. 146 theorems report `[propext, Classical.choice, Quot.sound]` and 1 reports `[propext, Quot.sound]`.
- Tamper: `~/lean/jl -g tamper` → `ALL TAMPERING TESTS REJECTED`, 6/6:
  - sorry, ax2line, evalfake, macro → forbidden token
  - falsehyp → build
  - wrap → nonstandard axioms
- **Tamper needs `-g`:** the published `tests/tamper.sh` uses GNU `sed -i` and fails to plant its defects with BSD sed. It was not edited, since the task allows only the gate.sh changes above. Making it portable is a possible follow-up.
- Forbidden grep on `L15Classical.lean` (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check`): **0 matches**.

### Hashes of published library files (HEAD vs working tree)
| file | sha256 (published) | status |
|---|---|---|
| PascalHexagon/Bracket.lean | b2d6d19cfc660df3852913e3ce67da7f6b252e9bec9de8ae1c1801e8951a2589 | unchanged |
| PascalHexagon/Brianchon.lean | 111d67fcb8753264bcb29a55cc9826c7fb1750d39717d03b4a88389ed6ab3791 | unchanged |
| PascalHexagon/Conic.lean | 81d1578035c2741e65254ac69815196b8ee98789a945853277d7c3a4bcb48540 | unchanged |
| PascalHexagon/Correctness.lean | d79b4d0ee26d302ebff214a96b838489d5f032cd5f8229f7ae50ebbdeb5e1753 | unchanged |
| PascalHexagon/Defs.lean | 038688208f2879766a627626665a01372fa304c5486ca5290cfe59f3f31d6625 | unchanged |
| PascalHexagon/Projective.lean | e2a5e14389910775df82e8db3a01804ebe784c8e62f2135608b0474d234776f9 | unchanged |
| PascalHexagon/StandardConic.lean | a88c9c6b828ffcd2346e4f45ca45f882e52e28158c59e1aa62ff40c0d067dd1f | unchanged |
| PascalHexagon/Veronese.lean | 50d093d435893bd537bd992766aca4b73e70a6f278d7d447422c5c9089bae45c | unchanged |
| PascalHexagon.lean (root) | 1a76f25c… | changed (2 import lines, intended) |

### README (addendum c)
- Added a "Layers 14 and 15" section: L14 has 27 gated declarations; L15 has 20 writer statements, all proved, 88 gated declarations, and no false writer statement.
- Changed the count from 32 to 147 in three places: the Status line, the Verification text, and the Output line.
- Found no machine paths.
- **Docstring/README claims:** neither layer contradicted a repository claim, so no text fixes were needed. L15 proves the writer's tangent/polar duality, which supports the existing scoping of the Brianchon dual-conic claim to nonsingular conics in characteristic ≠ 2.

### Dropped
Nothing.

### Commit (local only, NOT pushed)
Commit: `be35ffaa75a324131a710d3287b3d703408ad4a0`, author `Josh Bald <jpbald93@gmail.com>`, branch `master` (ahead of `origin/master` by 1).

`git status --short` before commit:
```
M  .gitignore
M  PascalHexagon.lean
A  PascalHexagon/L14.lean
A  PascalHexagon/L15Classical.lean
M  README.md
M  gate.sh
```
After commit: clean (empty).

`git log --oneline -3`:
```
be35ffa Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
726da4d Brianchon docstrings: scope dual-conic claim to nonsingular/char != 2; note concurrency witness hypothesis
69df575 Brianchon's theorem (dual of Pascal); gate now 32 theorems, PASS on jack; tamper 6/6 rejected
```
Diff stat: 6 files, +2213 / −5.
