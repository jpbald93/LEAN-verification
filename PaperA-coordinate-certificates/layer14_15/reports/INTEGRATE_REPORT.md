# Paper A: Layers 14 and 15 integration report

Date: 2026-10-22. Machine: john (arm64 macOS). Publication-ready copies: `~/lean/pubA_<repo>`.
Nothing was committed or pushed.

## Summary

| repo | REQUIRED published → L14 → final | gate | tamper | dropped |
|---|---|---|---|---|
| desargues | 24 → 31 → 34 | PASS (34 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none |
| monge | 7 → 11 → 15 | PASS (15 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none |
| simson | 12 → 18 → 21 | PASS (21 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none |
| napoleon | 21 → 41 → 45 | PASS (45 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none |
| lami | 17 → 20 → 23 | PASS (23 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none |

Every gated declaration depends on `[propext, Classical.choice, Quot.sound]` only.

## Method (same for every repo)

1. `cp -a l14A_<repo> pubA_<repo>`. The `.lake/packages` symlink is kept (it points to `~/lean/clifford/.lake/packages`). `scratch/` was removed. There were no stray logs. `.git` is kept.
2. `<Lib>/L15Classical.lean` was made from `l15A_<repo>/scratch/L15_compare.lean`:
   - The imports `import <Lib>` were replaced with the library's submodules plus `<Lib>.L14`, because the root file now imports L15Classical, so importing the root would be a cycle. `import Mathlib` is kept.
   - The namespace `L15Compare` is renamed to `<Lib>.Classical`.
   - The required Layer 15 header docstring was added.
   - The trailing `#print axioms` lines were removed. Those were the only forbidden commands present: the scratch files had no `set_option`, `macro`, `notation`, `run_cmd`, `#check` or `#eval`.
   - All other text is byte-for-byte the scratch file: the writer's definitions and `classical_*` statements are verbatim, and all glue lemmas and cov_* proofs are kept.
   - Nothing needed `maxHeartbeats`, and nothing was restructured or dropped.
   - The Napoleon counterexample `A4_obligation_false` got the one-line comment `-- The writer's statement `classical_A4_obligation` is false as written.`
3. One line `import <Lib>.L15Classical` was appended at the end of each root file.
4. REQUIRED in gate.sh: the new fully qualified names were appended. Only that line changed. The gate was run with `~/lean/jl -g gate` because the published gates use GNU `mktemp --suffix`.
5. README.md:
   - The declaration counts were updated: the "Status" line, the "Verification" count and the "Output" line. The published "Verification" count was already stale (for example 19 against 24 in desargues).
   - A "Layers 14 and 15" section was added before "Prior art".
   - References to the removed `scratch/Ax.lean` were removed (the Verification sentence and the sentence in the code/scratch paragraph). Lami's `AxCheck.lean` is a tracked root file and was kept.
   - No machine paths appear in any README.

**Writer statements shown false:** one, Napoleon `classical_A4_obligation`. It omits `U ≠ V`. The negation is proved as `Napoleon.Classical.A4_obligation_false`, and the corrected statement as `Napoleon.Classical.cov_A4_obligation_corrected`. All other writer statements are proved as written.

**Note on step 5 (published-file hashes):** every published library file under `<Lib>/`, plus Lami's `AxCheck.lean`, is unchanged. The only changed tracked files are the root file, gate.sh and README.md, plus the `scratch/*.lean` files deleted by the instructed removal of `scratch/`. Those deletions show as ` D` in `git status`.

**Note on REQUIRED coverage:** REQUIRED holds every cov_*, every NEW PROOF lemma (Simson's `area2_eq_zero_of_collinear`), every obligation and every counterexample. Glue lemmas (not private, but not cited anywhere), such as `pline_eq` and `ext_eq_of_isExt`, and the `classical_*` Prop definitions are not in REQUIRED, but they are covered transitively through the cov_* axiom reports.

## desargues (~/lean/pubA_desargues, HEAD b640925, not committed)

New files:

| file | lines | sha256 |
|---|---|---|
| `Desargues/L14.lean` | 218 | `cc9a638b4cbadbd6cc2055e8f854e96922c63784e076676cf0258d091485e560` |
| `Desargues/L15Classical.lean` | 258 | `d038ae3fc0f436ec62129cddd2cbb4be2bb9c9fe69ae5287c69eccfcd6b04700` |

REQUIRED: published 24 → L14 31 → final 34
Added to REQUIRED: Desargues.Classical.cov_A1_obligation Desargues.Classical.cov_A1_a Desargues.Classical.cov_A1_b 

- build: `~/lean/jl build` rc 0
- gate (`~/lean/jl -g gate`): `PASS (34 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on Desargues/L15Classical.lean (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval): 0 matches (0 including comments)

Hashes of the published library .lean files (HEAD vs working tree):

| file | published sha256 | now | |
|---|---|---|---|
| `Desargues.lean` | 94b087f2ff5d54ec | 27c836ecc5fe8114 | changed |
| `Desargues/Basic.lean` | 8eb210482ceb5ee9 | 8eb210482ceb5ee9 | unchanged |
| `Desargues/Bridge.lean` | 2e45e4677757f92f | 2e45e4677757f92f | unchanged |
| `Desargues/Examples.lean` | b9cf1756987a7c96 | b9cf1756987a7c96 | unchanged |
| `Desargues/Main.lean` | bea8c802295339ed | bea8c802295339ed | unchanged |
| `Desargues/Plane.lean` | 89249b1530a13e8c | 89249b1530a13e8c | unchanged |
| `scratch/Ax.lean` | 6435d16fa588edc0 | (removed) | changed |
| `scratch/probe.lean` | c2737330bb15f8cc | (removed) | changed |

`git status --short`:

```
 M Desargues.lean
 M README.md
 M gate.sh
 D scratch/Ax.lean
 D scratch/probe.lean
?? Desargues/L14.lean
?? Desargues/L15Classical.lean
```

## monge (~/lean/pubA_monge, HEAD a01f750, not committed)

New files:

| file | lines | sha256 |
|---|---|---|
| `Monge/L14.lean` | 91 | `4ebbf749f493ef7597904342c5f8c966f9ebe1981d77495a9fe0d491aab81084` |
| `Monge/L15Classical.lean` | 261 | `c8681ae4ecf9f52c3c5c30c635883d093157f20e37fda388b35a92c935c6c47e` |

REQUIRED: published 7 → L14 11 → final 15
Added to REQUIRED: Monge.Classical.cov_A2_a Monge.Classical.cov_A2_b Monge.Classical.cov_A2_obligation_ext Monge.Classical.cov_A2_obligation_int 

- build: `~/lean/jl build` rc 0
- gate (`~/lean/jl -g gate`): `PASS (15 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on Monge/L15Classical.lean (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval): 0 matches (0 including comments)

Hashes of the published library .lean files (HEAD vs working tree):

| file | published sha256 | now | |
|---|---|---|---|
| `Monge.lean` | f14f723be188eecc | 04330430802a2261 | changed |
| `Monge/Basic.lean` | dc59f1c3d86680bc | dc59f1c3d86680bc | unchanged |
| `Monge/Bridge.lean` | b32c8a52815d705d | b32c8a52815d705d | unchanged |
| `scratch/Ax.lean` | 813537ca7c56f97a | (removed) | changed |

`git status --short`:

```
 M Monge.lean
 M README.md
 M gate.sh
 D scratch/Ax.lean
?? Monge/L14.lean
?? Monge/L15Classical.lean
```

## simson (~/lean/pubA_simson, HEAD 7c239b3, not committed)

New files:

| file | lines | sha256 |
|---|---|---|
| `Simson/L14.lean` | 121 | `cf32580f2f1eba9ecb51de7c8bbe889be28286060bee7791993f8cb16ce81718` |
| `Simson/L15Classical.lean` | 168 | `5a772a38a554d6876df3e171766eefdc239cff125e9a1441b82b44e7b3518a4c` |

REQUIRED: published 12 → L14 18 → final 21
Added to REQUIRED: Simson.Classical.cov_A3_a Simson.Classical.cov_A3_b Simson.Classical.area2_eq_zero_of_collinear 

- build: `~/lean/jl build` rc 0
- gate (`~/lean/jl -g gate`): `PASS (21 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on Simson/L15Classical.lean (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval): 0 matches (0 including comments)

Hashes of the published library .lean files (HEAD vs working tree):

| file | published sha256 | now | |
|---|---|---|---|
| `Simson.lean` | 257b79adfd1c64cc | bbe42eef714feb9e | changed |
| `Simson/Basic.lean` | a9d7180281ad1238 | a9d7180281ad1238 | unchanged |
| `Simson/Bridge.lean` | 8fa41750a2927601 | 8fa41750a2927601 | unchanged |
| `Simson/Identity.lean` | 23af76e601cab8f4 | 23af76e601cab8f4 | unchanged |
| `Simson/Main.lean` | e2955b5d1c414a58 | e2955b5d1c414a58 | unchanged |
| `scratch/Ax.lean` | b5d5862652626aa4 | (removed) | changed |

`git status --short`:

```
 M README.md
 M Simson.lean
 M gate.sh
 D scratch/Ax.lean
?? Simson/L14.lean
?? Simson/L15Classical.lean
```

## napoleon (~/lean/pubA_napoleon, HEAD e16592a, not committed)

New files:

| file | lines | sha256 |
|---|---|---|
| `Napoleon/L14.lean` | 334 | `56770a1ca995efbf867002d28abb72e35384d773d38f48487c46b800bfe82fbc` |
| `Napoleon/L15Classical.lean` | 503 | `6a42d3398dc4c22b3f231ef0522a8311e99cee14708ccd3fdd5f348d73400cd1` |

REQUIRED: published 21 → L14 41 → final 45
Added to REQUIRED: Napoleon.Classical.cov_A4_a Napoleon.Classical.cov_A4_b Napoleon.Classical.A4_obligation_false Napoleon.Classical.cov_A4_obligation_corrected 

- build: `~/lean/jl build` rc 0
- gate (`~/lean/jl -g gate`): `PASS (45 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on Napoleon/L15Classical.lean (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval): 0 matches (0 including comments)

Hashes of the published library .lean files (HEAD vs working tree):

| file | published sha256 | now | |
|---|---|---|---|
| `Napoleon.lean` | 60d7f152537cf509 | 5e3dc95699183a62 | changed |
| `Napoleon/Basic.lean` | b241be8bccfe7841 | b241be8bccfe7841 | unchanged |
| `Napoleon/Bridge.lean` | f12ac6337b1a5f78 | f12ac6337b1a5f78 | unchanged |
| `scratch/Ax.lean` | 357545610fa675ab | (removed) | changed |

`git status --short`:

```
 M Napoleon.lean
 M README.md
 M gate.sh
 D scratch/Ax.lean
?? Napoleon/L14.lean
?? Napoleon/L15Classical.lean
```

## lami (~/lean/pubA_lami, HEAD ea6b038, not committed)

New files:

| file | lines | sha256 |
|---|---|---|
| `Lami/L14.lean` | 73 | `5e117b786d38b106798be55ce14f4723e9d7a8b80eb860ed28a379a352160283` |
| `Lami/L15Classical.lean` | 98 | `43e76627d7099a000b3405295963d6c2598bb55664cb541e18837f875fac356c` |

REQUIRED: published 17 → L14 20 → final 23
Added to REQUIRED: Lami.Classical.cov_A5 Lami.Classical.cov_A5_obligation Lami.Classical.cov_A5_nondegenerate 

- build: `~/lean/jl build` rc 0
- gate (`~/lean/jl -g gate`): `PASS (23 declarations, standard axioms only)`
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on Lami/L15Classical.lean (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval): 0 matches (0 including comments)

Hashes of the published library .lean files (HEAD vs working tree):

| file | published sha256 | now | |
|---|---|---|---|
| `AxCheck.lean` | 5f8e89e269d70621 | 5f8e89e269d70621 | unchanged |
| `Lami.lean` | b73b09d6475edf77 | 1ff43d9f4df801bd | changed |
| `Lami/Basic.lean` | cca0cae5e1c6b679 | cca0cae5e1c6b679 | unchanged |

`git status --short`:

```
 M Lami.lean
 M README.md
 M gate.sh
?? Lami/L14.lean
?? Lami/L15Classical.lean
```


## Commit step

Date: 2026-10-22, on john. All five copies had the same three newer commits on origin/main. They were brought in with `git stash` / `git merge --ff-only origin/main` / `git stash pop`, and `git stash pop` auto-merged in every copy with no conflicts. README.md kept both texts: origin's citation and draft-status edits plus the L14/L15 count and section edits. gate.sh kept origin's portable `chk=".gatecheck_$$.lean"` line and the extended REQUIRED.

The copies were on a detached HEAD at the published base. Local `main` equalled origin/main after the fast-forward, so `git checkout main` was run before committing (the working changes carried over), and each commit is on local `main`. john has no git identity configured, so author and committer were both set to `Josh Bald <jpbald93@gmail.com>`. The message is the specified subject plus a `Co-Authored-By: Claude Opus 5.5` trailer. Staged per copy: the root file, `<Lib>/L14.lean`, `<Lib>/L15Classical.lean`, README.md and gate.sh, plus the `scratch/*.lean` deletions. `.lake/` stays ignored, and there were no logs in the repos. Nothing was pushed.

| repo | origin commits merged | gate fix | gate | tamper | commit |
|---|---|---|---|---|---|
| desargues | 3 | no (already in origin) | PASS (34 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | 086ca71 |
| monge | 3 | no (already in origin) | PASS (15 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | 82dd27d |
| simson | 3 | no (already in origin) | PASS (21 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | e3d2c46 |
| napoleon | 3 | no (already in origin) | PASS (45 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | 0829a14 |
| lami | 3 | no (already in origin) | PASS (23 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | e692d1a |

### desargues (~/lean/pubA_desargues)

- origin commits merged (ff-only, base b640925 → 53efa45); stash pop auto-merged README.md and gate.sh with no conflicts:
  - 53efa45 Add copyright line, CITATION.cff and licence note
  - 2ae1f99 verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
  - edb12a3 README: drop draft status; cite the published commit
- gate fix (b): no. Origin commit 2ae1f99 already changed the line to `chk=".gatecheck_$$.lean"`, and .gitignore already has `.gatecheck_*`. The extended REQUIRED line was kept.
- build (`~/lean/jl build`, system/BSD tools, no -g): rc 0
- gate (`~/lean/jl gate`): `PASS (34 declarations, standard axioms only)`
- tamper (`~/lean/jl tamper`): `ALL TAMPERING TESTS REJECTED`
- new commit: `086ca718192df1cb919b72a7e79d9fb26e43e723` on local `main` (1 ahead of origin/main, NOT pushed)

`git log --oneline -3`:

```
086ca71 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
53efa45 Add copyright line, CITATION.cff and licence note
2ae1f99 verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
```

`git status --short` (clean; only ignored `.lake/` remains):

```
(empty)
```

### monge (~/lean/pubA_monge)

- origin commits merged (ff-only, base a01f750 → 652b8c2); stash pop auto-merged README.md and gate.sh with no conflicts:
  - 652b8c2 Add copyright line, CITATION.cff and licence note
  - 2546e52 verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
  - ba79e5b README: drop draft status; cite the published commit
- gate fix (b): no. Origin commit 2546e52 already changed the line to `chk=".gatecheck_$$.lean"`, and .gitignore already has `.gatecheck_*`. The extended REQUIRED line was kept.
- build (`~/lean/jl build`, system/BSD tools, no -g): rc 0
- gate (`~/lean/jl gate`): `PASS (15 declarations, standard axioms only)`
- tamper (`~/lean/jl tamper`): `ALL TAMPERING TESTS REJECTED`
- new commit: `82dd27d7b81e60e2aa57873e98cc6fa0dce0728f` on local `main` (1 ahead of origin/main, NOT pushed)

`git log --oneline -3`:

```
82dd27d Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
652b8c2 Add copyright line, CITATION.cff and licence note
2546e52 verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
```

`git status --short` (clean; only ignored `.lake/` remains):

```
(empty)
```

### simson (~/lean/pubA_simson)

- origin commits merged (ff-only, base 7c239b3 → 2913c39); stash pop auto-merged README.md and gate.sh with no conflicts:
  - 2913c39 Add copyright line, CITATION.cff and licence note
  - 6a4b02f verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
  - dc3a8c6 README: drop draft status; cite the published commit
- gate fix (b): no. Origin commit 6a4b02f already changed the line to `chk=".gatecheck_$$.lean"`, and .gitignore already has `.gatecheck_*`. The extended REQUIRED line was kept.
- build (`~/lean/jl build`, system/BSD tools, no -g): rc 0
- gate (`~/lean/jl gate`): `PASS (21 declarations, standard axioms only)`
- tamper (`~/lean/jl tamper`): `ALL TAMPERING TESTS REJECTED`
- new commit: `e3d2c46abd6a6da2a4571a28cebc47c8447a0618` on local `main` (1 ahead of origin/main, NOT pushed)

`git log --oneline -3`:

```
e3d2c46 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
2913c39 Add copyright line, CITATION.cff and licence note
6a4b02f verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
```

`git status --short` (clean; only ignored `.lake/` remains):

```
(empty)
```

### napoleon (~/lean/pubA_napoleon)

- origin commits merged (ff-only, base e16592a → 37998d4); stash pop auto-merged README.md and gate.sh with no conflicts:
  - 37998d4 Add copyright line, CITATION.cff and licence note
  - 00fd9d7 verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
  - f91f9f5 README: drop draft status; cite the published commit
- gate fix (b): no. Origin commit 00fd9d7 already changed the line to `chk=".gatecheck_$$.lean"`, and .gitignore already has `.gatecheck_*`. The extended REQUIRED line was kept.
- build (`~/lean/jl build`, system/BSD tools, no -g): rc 0
- gate (`~/lean/jl gate`): `PASS (45 declarations, standard axioms only)`
- tamper (`~/lean/jl tamper`): `ALL TAMPERING TESTS REJECTED`
- new commit: `0829a1483687956644b6b5eb3eb26205c6d7e9b7` on local `main` (1 ahead of origin/main, NOT pushed)

`git log --oneline -3`:

```
0829a14 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
37998d4 Add copyright line, CITATION.cff and licence note
00fd9d7 verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
```

`git status --short` (clean; only ignored `.lake/` remains):

```
(empty)
```

### lami (~/lean/pubA_lami)

- origin commits merged (ff-only, base ea6b038 → 487b7c3); stash pop auto-merged README.md and gate.sh with no conflicts:
  - 487b7c3 Add copyright line, CITATION.cff and licence note
  - f2f52b0 verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
  - 8fa16af README: drop draft status; cite the published commit
- gate fix (b): no. Origin commit f2f52b0 already changed the line to `chk=".gatecheck_$$.lean"`, and .gitignore already has `.gatecheck_*`. The extended REQUIRED line was kept.
- build (`~/lean/jl build`, system/BSD tools, no -g): rc 0
- gate (`~/lean/jl gate`): `PASS (23 declarations, standard axioms only)`
- tamper (`~/lean/jl tamper`): `ALL TAMPERING TESTS REJECTED`
- new commit: `e692d1a9bc0004444e33b76132275461a2e26cf2` on local `main` (1 ahead of origin/main, NOT pushed)

`git log --oneline -3`:

```
e692d1a Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
487b7c3 Add copyright line, CITATION.cff and licence note
f2f52b0 verification scripts: portable to BSD/macOS (no GNU mktemp/sed/python3)
```

`git status --short` (clean; only ignored `.lake/` remains):

```
(empty)
```

### Commit step re-verification (later run, 2026-10-22)

The commit step was found already complete. Nothing was changed and no new commits were made. Re-checked on john for all five copies:
- `git fetch origin`: `HEAD..origin/main` is empty, and each copy is on `main`, 1 ahead of origin/main (not pushed).
- HEAD is the commit listed above (086ca71, 82dd27d, e3d2c46, 0829a14, e692d1a). Author is `Josh Bald <jpbald93@gmail.com>` with the specified subject.
- No conflict markers in README.md or gate.sh. No `mktemp --suffix` in gate.sh.
- `~/lean/jl build` rc 0. `~/lean/jl gate` (no -g) gives PASS with 34 / 15 / 21 / 45 / 23 declarations, standard axioms only. `~/lean/jl tamper` gives ALL TAMPERING TESTS REJECTED.
- `git status --short` is empty in every copy.
