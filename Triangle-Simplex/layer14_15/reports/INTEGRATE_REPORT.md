# Paper TriSimplex: integrating Layers 14 and 15 into publication copies

Machine: john (arm64 macOS). Copies: `~/lean/pubTriSimplex_<repo>`. All work was done inline, with no subagents. Each repo has **one local commit**; nothing was pushed.

## Summary
| repo | REQUIRED published → L14 → final | build | gate (BSD tools, plain `jl gate`) | tamper (`jl -g tamper`) | commit |
|---|---|---|---|---|---|
| carnot | 12 → 20 → 28 | rc 0 | PASS (28 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | fa8c37951d290d26db66ff83c358b09b156d26e6 |
| viviani | 10 → 21 → 28 | rc 0 | PASS (28 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | e71460f2edb224b2e7e98a39c6db6bead93613cc |
| degua | 10 → 20 → 23 | rc 0 | PASS (23 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | daa89522f4a85e6afb8fe4d4d1a94b3d0761943e |
| japanese-theorem | 51 → 67 → 81 | rc 0 | PASS (81 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | be4503b4e1dfdf7e527e2425276f992ecabb4bc2 |
| poncelet-triangles | 22 → 36 → 53 | rc 0 | PASS (53 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | aa9da6c4e077cee2e9191ad9011a246ad9e04f2f |

**Nothing was dropped.** None of the L15 scratch files used `set_option`, so no proof had to be restructured. Every theorem and lemma in each scratch file went into the library file and into REQUIRED. That covers all cov_*, NEW PROOF lemmas, bridges, obligations and both counterexamples.
Axioms: every Layer-14/15 declaration reports `[propext, Classical.choice, Quot.sound]`. The only other lines are two published Japanese definitions (`Japanese.Crosses`, `Japanese.Triangulation.triangles`), which report "does not depend on any axioms".

## Step (a): starting from the current GitHub HEAD
In every copy, `git fetch origin` gave `origin/master` (the default branch is `master`, not `main`), equal to the published commit. There were no later commits, so nothing needed merging and nothing was lost:
carnot 98e5614, viviani 029aa3d, degua d46e6b2, japanese-theorem 34fd0a9, poncelet-triangles 9affe62. The L14 copy was in detached HEAD at that commit. In the pub copy I checked out `master` (same commit) before committing.

## Step (b): gate.sh portability (all 5 repos)
All five `gate.sh` files still had `chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)`. I replaced that single line with `chk=".gatecheck_$$.lean"` (the jpbald93/desargues form). `.gatecheck_*` was already in every `.gitignore`. As a result, **plain `~/lean/jl gate` (BSD tools) now PASSes in all five**. gate.sh diff: exactly 2 lines (REQUIRED and chk).
**Still open (not fixed, out of scope):** `tests/tamper.sh` uses GNU `sed -i '…'` in the `wrap` test (lines 74–75). Under BSD tools, `wrap` fails with "could not plant defect" (seen in carnot and viviani before I switched). With `jl -g tamper`, all six tests are rejected in all five repos. The desargues HEAD `tamper.sh` is the portable version (POSIX awk). Porting it is a recommended follow-up but was not in the brief, which allows edits to the gate only.

## Step (c): repository text claims
No published docstring or README claim was wrong. The L14 report found no false restatement. The L15 discrepancies are *writer* mis-statements (Japanese 4b obligation and rectangle: a degenerate `IsConvexQuad`) or gaps the README and paper already state (De Gua: "Volumes are Gram-determinant volumes, not measure-theoretic"; Japanese: maximal non-crossing chord sets). The only README changes are the new section and the counts. No machine paths appeared in any README, L14 or L15 file.

## Integration notes
- `import <Lib>` in `<Lib>/L15Classical.lean` would form a cycle with the root file, and the first build failed with "build cycle detected". The library file therefore imports the root file's own module list (e.g. `Carnot.Algebra`, `Carnot.Geometry`, `Carnot.Main`). `import <Lib>.L15Classical` is the last line of the root file.
- Namespace `ClassicalTriSimplex` became `<Lib>.Classical`. The `#print axioms` lines at the end of each scratch file were removed. All other text, including the writer's definitions and statements, is unchanged apart from the new header docstring and the two "false as written" comments.
- The `scratch/` directories are **tracked** in the published repos, and the README cites them ("`scratch/` contains the `#print axioms` driver files … cited in the paper"). I therefore **kept** them; deleting them would remove published files and break the README and paper citation. No untracked stray files or logs existed (the L14 scratch additions had never been copied in).
- `.lake/packages`: carnot keeps its symlink (→ `~/lean/clifford/.lake/packages`). In viviani, degua, japanese-theorem and poncelet-triangles, the **L14 copies already had a real directory** (≈12 GB, same toolchain v4.33.1 and the same manifest as clifford), and `cp -a` preserved it. The L14 report's claim of a "symlink" for all five is wrong for those four. They are ignored by git, so this does not affect the commits.

## carnot
| new file | lines | sha256 |
|---|---|---|
| Carnot/L14.lean | 124 | 04f725ef4b1456f4eb346cd08430b1981aa2db6d17ea7aada777735b196cb366 |
| Carnot/L15Classical.lean | 188 | 848638ea92e4e4f9a64a5f038ef7e57b1c047157c93d9aed3e9a008aa7cb718d |

L15 file: 8 theorems/lemmas (all in REQUIRED), 6 defs (writer definitions + classical_* Props).

Added to REQUIRED (L15):

```
Carnot.Classical.signedDistLine_face_eq Carnot.Classical.face_eq Carnot.Classical.sdl_eq_ssd Carnot.Classical.cov_TriSimplex1_a Carnot.Classical.cov_TriSimplex1_b_signed Carnot.Classical.cov_TriSimplex1_b Carnot.Classical.cov_TriSimplex1_b_acute Carnot.Classical.cov_TriSimplex1_b_acute_inside
```
- gate: `PASS (28 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- commit: `fa8c37951d290d26db66ff83c358b09b156d26e6`, author Josh Bald <jpbald93@gmail.com>
- forbidden grep (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval`) on L15Classical.lean outside comments: **0**. L14.lean: 0.
- `git log --oneline -3`:

```
fa8c379 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
98e5614 README: describe the scratch folder and tamper-test criterion
d937580 Keep the axiom and build logs cited in the paper at the repository root
```
- `git status --short` after the commit: *(empty)*. Before `git add -A`: ` M <Lib>.lean`, ` M README.md`, ` M gate.sh`, `?? Carnot/L14.lean`, `?? Carnot/L15Classical.lean`.

Hashes of every tracked .lean file of the published commit (`git show HEAD~1:f | shasum -a 256` vs the working file):

| file | sha256 (published HEAD) | sha256 (now) | same |
|---|---|---|---|
| Carnot.lean | d44a930792b647df… | b3a4dd23bb5e1b17… | NO (root file, +2 import lines) |
| Carnot/Algebra.lean | 1a18e5333c100219… | 1a18e5333c100219… | yes |
| Carnot/Geometry.lean | 87a9c1988963bd6c… | 87a9c1988963bd6c… | yes |
| Carnot/Main.lean | 1fb6ed3429304a9a… | 1fb6ed3429304a9a… | yes |
| scratch/Axioms.lean | 6d3629bedb459b7f… | 6d3629bedb459b7f… | yes |

## viviani
| new file | lines | sha256 |
|---|---|---|
| Viviani/L14.lean | 165 | ca0ea267dd1404586f5cae52f3116d5656f50d9df9e3ed70ff775385883735f8 |
| Viviani/L15Classical.lean | 184 | 9be7980905c30afadc7eb91dc0256099c1157ecefb95763db1b3d131b32fb8c2 |

L15 file: 7 theorems/lemmas (all in REQUIRED), 4 defs (writer definitions + classical_* Props).

Added to REQUIRED (L15):

```
Viviani.Classical.signedDistLine_face_eq Viviani.Classical.face_eq Viviani.Classical.height_two_eq Viviani.Classical.infDist_face Viviani.Classical.cov_TriSimplex3_b_closed Viviani.Classical.cov_TriSimplex3_a Viviani.Classical.cov_TriSimplex3_b
```
- gate: `PASS (28 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- commit: `e71460f2edb224b2e7e98a39c6db6bead93613cc`, author Josh Bald <jpbald93@gmail.com>
- forbidden grep (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval`) on L15Classical.lean outside comments: **0**. L14.lean: 0.
- `git log --oneline -3`:

```
e71460f Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
029aa3d README: describe the scratch folder and tamper-test criterion
33ae77d Keep the axiom and build logs cited in the paper at the repository root
```
- `git status --short` after the commit: *(empty)*. Before `git add -A`: ` M <Lib>.lean`, ` M README.md`, ` M gate.sh`, `?? Viviani/L14.lean`, `?? Viviani/L15Classical.lean`.

Hashes of every tracked .lean file of the published commit (`git show HEAD~1:f | shasum -a 256` vs the working file):

| file | sha256 (published HEAD) | sha256 (now) | same |
|---|---|---|---|
| Viviani.lean | a43a3010c8597cd1… | b11101bee5b7ed4e… | NO (root file, +2 import lines) |
| Viviani/Basic.lean | 0e158e6bb275ef7a… | 0e158e6bb275ef7a… | yes |
| Viviani/Equilateral.lean | 20f61763238cec1f… | 20f61763238cec1f… | yes |
| Viviani/Heights.lean | c325e7bf8d9dca4d… | c325e7bf8d9dca4d… | yes |
| scratch/Axioms.lean | c2a07f516ca7e929… | c2a07f516ca7e929… | yes |

## degua
| new file | lines | sha256 |
|---|---|---|
| DeGua/L14.lean | 140 | 724070630bdde8d07f801d708099f43999bdd61ca79d4a469e67b2c18f22b8e7 |
| DeGua/L15Classical.lean | 92 | 23d9581ae9fadecf031604aa09eaa2fc36d83b4c9463e5a7692dc96b385f56bb |

L15 file: 3 theorems/lemmas (all in REQUIRED), 5 defs (writer definitions + classical_* Props).

Added to REQUIRED (L15):

```
DeGua.Classical.cov_TriSimplex2_a_part DeGua.Classical.cov_TriSimplex2_a_coord_part DeGua.Classical.cov_TriSimplex2_b_part
```
- gate: `PASS (23 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- commit: `daa89522f4a85e6afb8fe4d4d1a94b3d0761943e`, author Josh Bald <jpbald93@gmail.com>
- forbidden grep (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval`) on L15Classical.lean outside comments: **0**. L14.lean: 0.
- `git log --oneline -3`:

```
daa8952 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
d46e6b2 README: describe the scratch folder and tamper-test criterion
7aaac67 Keep the axiom and build logs cited in the paper at the repository root
```
- `git status --short` after the commit: *(empty)*. Before `git add -A`: ` M <Lib>.lean`, ` M README.md`, ` M gate.sh`, `?? DeGua/L14.lean`, `?? DeGua/L15Classical.lean`.

Hashes of every tracked .lean file of the published commit (`git show HEAD~1:f | shasum -a 256` vs the working file):

| file | sha256 (published HEAD) | sha256 (now) | same |
|---|---|---|---|
| DeGua.lean | c410d8d2c78cf98b… | a845e753af7351b8… | NO (root file, +2 import lines) |
| DeGua/Bridge.lean | 084667537392c949… | 084667537392c949… | yes |
| DeGua/CauchyBinet.lean | affbcf74306be0f3… | affbcf74306be0f3… | yes |
| DeGua/General.lean | 14946c809e0ab9e9… | 14946c809e0ab9e9… | yes |
| DeGua/Three.lean | 847942fd3b06ede5… | 847942fd3b06ede5… | yes |
| scratch/Axioms.lean | 87c226880cfcc62e… | 87c226880cfcc62e… | yes |

## japanese-theorem
| new file | lines | sha256 |
|---|---|---|
| Japanese/L14.lean | 279 | afe92417c20657311f3d96735fc7f1849b60c3f34b2976d2e5557c4e48a7aaba |
| Japanese/L15Classical.lean | 364 | 78d07affd973c221b94e0c420b16a720f9ee0832ef079d519d10ce37746d2109 |

L15 file: 14 theorems/lemmas (all in REQUIRED), 11 defs (writer definitions + classical_* Props).

Added to REQUIRED (L15):

```
Japanese.Classical.triInradius_eq_repo Japanese.Classical.triInradius_eq_zero_left Japanese.Classical.triInradius_eq_zero_right Japanese.Classical.areaForm_ne_zero_of_affineIndependent Japanese.Classical.quad_signs Japanese.Classical.cov_TriSimplex4_b_part Japanese.Classical.not_classical_TriSimplex4_b_obligation Japanese.Classical.not_classical_TriSimplex4_b_rectangle Japanese.Classical.cov_TriSimplex4_b_obligation_part Japanese.Classical.not_wbtw_of_isConvexPolygon Japanese.Classical.cov_TriSimplex4_a_obligation Japanese.Classical.cov_TriSimplex4_a_part Japanese.Classical.triInradius_subtype Japanese.Classical.cov_TriSimplex4_b
```
- gate: `PASS (81 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- commit: `be4503b4e1dfdf7e527e2425276f992ecabb4bc2`, author Josh Bald <jpbald93@gmail.com>
- forbidden grep (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval`) on L15Classical.lean outside comments: **0** (the one raw hit is the word "adm**its**" in a docstring). L14.lean: 0.
- Writer statements shown false (comment "The writer's statement … is false as written." above each): `classical_TriSimplex4_b_obligation` (`not_classical_TriSimplex4_b_obligation`) and `classical_TriSimplex4_b_rectangle` (`not_classical_TriSimplex4_b_rectangle`).
- `git log --oneline -3`:

```
be4503b Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
34fd0a9 README: describe the scratch folder and tamper-test criterion
75b1798 Keep the axiom and build logs cited in the paper at the repository root
```
- `git status --short` after the commit: *(empty)*. Before `git add -A`: ` M <Lib>.lean`, ` M README.md`, ` M gate.sh`, `?? Japanese/L14.lean`, `?? Japanese/L15Classical.lean`.

Hashes of every tracked .lean file of the published commit (`git show HEAD~1:f | shasum -a 256` vs the working file):

| file | sha256 (published HEAD) | sha256 (now) | same |
|---|---|---|---|
| Japanese.lean | bdac80e3b9deccd9… | e7d5c4198488985a… | NO (root file, +2 import lines) |
| Japanese/Basic.lean | 263971b7e9e8b78a… | 263971b7e9e8b78a… | yes |
| Japanese/Carnot/Algebra.lean | 1a18e5333c100219… | 1a18e5333c100219… | yes |
| Japanese/Carnot/Geometry.lean | 72d0326f6ef7bb2f… | 72d0326f6ef7bb2f… | yes |
| Japanese/Carnot/Main.lean | 7d27ca0f91c77fb8… | 7d27ca0f91c77fb8… | yes |
| Japanese/Combinatorial.lean | 89bd618e607a92a1… | 89bd618e607a92a1… | yes |
| Japanese/Geometric.lean | 7b107f1405233aba… | 7b107f1405233aba… | yes |
| Japanese/Polygon.lean | 4ac37743441eb5ae… | 4ac37743441eb5ae… | yes |
| scratch/Axioms.lean | b1b5e47d062f8d04… | b1b5e47d062f8d04… | yes |

## poncelet-triangles
| new file | lines | sha256 |
|---|---|---|
| Poncelet3/L14.lean | 245 | 751dd61d9b7933d387dc51a85629bcacf52ec7175db9a21fb33c3da397141364 |
| Poncelet3/L15Classical.lean | 388 | c4740059051f35ed73a317b05199de5302ada0492de1d6a5031fac9bd353706a |

L15 file: 17 theorems/lemmas (all in REQUIRED), 9 defs (writer definitions + classical_* Props).

Added to REQUIRED (L15):

```
Poncelet3.Classical.cov_TriSimplex5_a Poncelet3.Classical.dist_eq_half_of_mem_line Poncelet3.Classical.dist_face_sq Poncelet3.Classical.faces Poncelet3.Classical.cov_TriSimplex5_b Poncelet3.Classical.mem_span_top Poncelet3.Classical.circum_eq Poncelet3.Classical.euler_of_interscribed Poncelet3.Classical.insphere_eq_of_isTangent Poncelet3.Classical.aux_hyps Poncelet3.Classical.cov_TriSimplex6_b Poncelet3.Classical.cov_TriSimplex6_a Poncelet3.Classical.mem_tangentsFrom_of_isTangent Poncelet3.Classical.cov_TriSimplex6_a_construction Poncelet3.Classical.cov_TriSimplex6_b_converse Poncelet3.Classical.cov_TriSimplex6_b_noclose Poncelet3.Classical.cov_TriSimplex6_a_obligation_part
```
- gate: `PASS (53 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- commit: `aa9da6c4e077cee2e9191ad9011a246ad9e04f2f`, author Josh Bald <jpbald93@gmail.com>
- forbidden grep (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval`) on L15Classical.lean outside comments: **0**. L14.lean: 0.
- `git log --oneline -3`:

```
aa9da6c Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
9affe62 README: describe the scratch folder and tamper-test criterion
8f39b09 Keep the axiom and build logs cited in the paper at the repository root
```
- `git status --short` after the commit: *(empty)*. Before `git add -A`: ` M <Lib>.lean`, ` M README.md`, ` M gate.sh`, `?? Poncelet3/L14.lean`, `?? Poncelet3/L15Classical.lean`.

Hashes of every tracked .lean file of the published commit (`git show HEAD~1:f | shasum -a 256` vs the working file):

| file | sha256 (published HEAD) | sha256 (now) | same |
|---|---|---|---|
| Poncelet3.lean | c85ac44b11ae1fad… | cd98db85861caf13… | NO (root file, +2 import lines) |
| Poncelet3/Algebra.lean | 29aa4e3107b22d15… | 29aa4e3107b22d15… | yes |
| Poncelet3/Closure.lean | 4c84dbb67595cbc2… | 4c84dbb67595cbc2… | yes |
| Poncelet3/Construction.lean | 75095e3125f473ac… | 75095e3125f473ac… | yes |
| Poncelet3/Euler/Algebra.lean | 015176ce7796f94b… | 015176ce7796f94b… | yes |
| Poncelet3/Euler/Geometry.lean | ea4c126619c6dbaa… | ea4c126619c6dbaa… | yes |
| Poncelet3/Euler/Main.lean | 060600eb0a41af5f… | 060600eb0a41af5f… | yes |
| Poncelet3/Package.lean | 8bd1430c23d0dd61… | 8bd1430c23d0dd61… | yes |
| Poncelet3/Porism.lean | 66928c79f0bcb398… | 66928c79f0bcb398… | yes |
| scratch/Ax.lean | f79e31cbdf5b5c8a… | f79e31cbdf5b5c8a… | yes |

All pre-existing library files are unchanged. The only modified tracked .lean file in each repo is the root file (+2 import lines).
