# INTEGRATE report: Paper Prime, Layers 14 and 15 merged into a publishable copy

Machine: jack (`jack`). Repository: `jpbald93/primitive-root-families`.

## primitive-root-families → `~/pubPrime_primitive-root-families`

**Base (addendum a)**
- The copy was made from `~/l14Prime_primitive-root-families`, keeping the `.lake/packages` symlink to `~/barbier/.lake/packages`. That copy had no `scratch/` and no stray logs.
- It was then fast-forwarded to the current GitHub HEAD, `origin/main` = `5dd936f` ("README: document Part 3 (General.lean), 17 theorems"), which is one commit after the L14 base `e30457a`. That commit only touches `README.md`.
- The fast-forward had no conflicts, and the copy is now on branch `main`.

**New files**

| file | lines | sha256 |
|---|---|---|
| `PrimitiveRootFamilies/L14.lean` | 376 | `c8f310a90970c0b84d8aae599fe96492e8be2edb1cb8a935b46a2e7f7b1dfb48` |
| `PrimitiveRootFamilies/L15Classical.lean` | 704 | `7a3a1246cbbf80e13261c4b4adb198f9f12faa93732c480f4e86c872492fdbe1` |

**What `L15Classical.lean` contains**
- It is built from `scratch/L15_compare.lean` (sha256 `6c8e6ee9…b035`) and uses namespace `PrimitiveRootFamilies.Classical`, with the required Layer-15 header docstring.
- It imports `PrimitiveRootFamilies.{Chebyshev,SafePrime,General}` and `Mathlib`. It does not import the root module, because the root imports this file.
- The writer's definitions and the 26 `classical_*` statements (scratch lines 14–175) are **byte-identical**, checked with `diff`. The writer's own header docstring was folded into the new header.
- It keeps every proof unchanged:
  - all 26 `cov_*` theorems;
  - the counterexample `not_classical_Prime3_c`, preceded by a one-line comment saying the writer's statement is false as written;
  - the NEW PROOF `new_Prime3_c_corrected`;
  - the proved obligations `cov_Prime6_obligation` and `cov_Prime6_a_obligation`;
  - the helper lemmas, including the NEW PROOF lemmas `decimalPeriod_eq_orderOf` and `ndig_periodic_iff`.
- Removed: the 28 `#print axioms` lines.
- Changed: the six `instance fact_prime_N` became `local instance`, so the library does not export global `Fact (Nat.Prime N)` instances. This follows the repository's own convention in Chebyshev.lean.
- The scratch file never used `set_option`, `macro`, `notation` or `run_cmd`.
- **Nothing was dropped.**

**Root file:** one line, `import PrimitiveRootFamilies.L15Classical`, appended at the end (after the L14 import).

**REQUIRED count: published 17 → L14 53 → final 83.** The 30 added names, all under `Classical.`:
- the 26 `cov_*` theorems;
- `not_classical_Prime3_c` and `new_Prime3_c_corrected`;
- the NEW PROOF lemmas `decimalPeriod_eq_orderOf` and `ndig_periodic_iff`.

The two obligations are among the `cov_*` theorems.

**gate.sh portability (addendum b)**
- The gate still had the GNU-only line `chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)`.
- That single line was replaced with `chk=".gatecheck_$$.lean"`, the form used in jpbald93/desargues HEAD.
- `.gatecheck_*` was already in `.gitignore`, so it was not changed.
- Only the REQUIRED line and that one line differ from HEAD.

**Checks** (final tree, rerun after the last edit)
- `lake build`: rc 0, `Build completed successfully (8712 jobs).` One deprecation warning (`Set.mem_setOf_eq`) is left in the writer-derived proof code.
- Gate: `PASS (83 theorems, standard axioms only)`.
  - 38 theorems report `[propext, Classical.choice, Quot.sound]`.
  - 45 report a subset that starts with `propext` (the wrapped reports).
  - None reports a non-standard axiom.
- Tamper: `ALL TAMPERING TESTS REJECTED`. All six tests were rejected: sorry, ax2line, evalfake, macro, falsehyp and wrap.
- Forbidden grep on L15Classical.lean (`sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval`): **0 matches** (grep rc 1). The gate's own token filter also passed over all sources.
- No `.gatecheck_*` file is left behind.

**Hash table** (each file in the published HEAD `5dd936f` against the committed tree; changes: root file +2 import lines, README Layers 14/15 section and counts, gate.sh REQUIRED + chk line)

| status | sha256 at HEAD 5dd936f | sha256 now (commit b4ae30a) | file |
|---|---|---|---|
| same | `ea1937866769c95cbc15cbfbcaf0a0ecdbd88b3dda98d80bc70fd95949e69257` | `ea1937866769c95cbc15cbfbcaf0a0ecdbd88b3dda98d80bc70fd95949e69257` | .gitignore |
| same | `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` | `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` | LICENSE |
| CHANGED | `abf6ced1fe2ee65bd279360caf3a799ddea2c81be29e11765e327ec84ba4e642` | `19307949a8b88d23d119d9e6af2a3b89dc6caf3b7cbd2507c1fc6114bc6842fe` | PrimitiveRootFamilies.lean |
| same | `6b27335ade4ff8cceb73eb6bf7a1b098ac5deed3edcda1ce107ee3ab1b7115f2` | `6b27335ade4ff8cceb73eb6bf7a1b098ac5deed3edcda1ce107ee3ab1b7115f2` | PrimitiveRootFamilies/Chebyshev.lean |
| same | `2075da126aa124ad5c5e7591d8755e237836ddda854f9671090991ef324161b4` | `2075da126aa124ad5c5e7591d8755e237836ddda854f9671090991ef324161b4` | PrimitiveRootFamilies/General.lean |
| same | `9fd4a70c588eeb61e6f911c0e085da4ad5cab5439a0390fc05d2fbdcbb3b742f` | `9fd4a70c588eeb61e6f911c0e085da4ad5cab5439a0390fc05d2fbdcbb3b742f` | PrimitiveRootFamilies/SafePrime.lean |
| CHANGED | `2293084ae81211bd869ef65299aa692a83258312781cda65fd111e77ec3bcb75` | `4dace60648e73ecdc0f8c80e2a2bd946abfc9d6d6f28073036131e15b27c5bf9` | README.md |
| same | `8ef164cc15a5f8f91540e69994facf86877fb6090f9cc53214e4abb18ab7b74f` | `8ef164cc15a5f8f91540e69994facf86877fb6090f9cc53214e4abb18ab7b74f` | code/check_family.py |
| same | `f8abf394b70199aca6f060eb570ad1adb8964ebec3fd889c2ea1dcf436cbff3f` | `f8abf394b70199aca6f060eb570ad1adb8964ebec3fd889c2ea1dcf436cbff3f` | code/check_general.py |
| same | `dc47b401179af9c4d0ebc69f9f3135c881624fca0133eb476c41388f2fba7f23` | `dc47b401179af9c4d0ebc69f9f3135c881624fca0133eb476c41388f2fba7f23` | code/check_safe_primes.py |
| CHANGED | `c831ac09d0d0af47e866d9c54483f998dcf6ac51ab718bc8cb48200a2d1293c8` | `e728f2e46af6984f3ecec6aec370172a3bb5681c0a0c3e25e4604de2dcbdaffc` | gate.sh |
| same | `4160ab610a8a1495cf3f59da57292a442e6ad515f70220e6d2aef3498f20485f` | `4160ab610a8a1495cf3f59da57292a442e6ad515f70220e6d2aef3498f20485f` | lake-manifest.json |
| same | `5116bda075db17f02de06cbb06ddf906b78f500bdb4c219095a99630b9bce484` | `5116bda075db17f02de06cbb06ddf906b78f500bdb4c219095a99630b9bce484` | lakefile.toml |
| same | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` | lean-toolchain |
| same | `1903e12fcadaf09322f944d01d927c216dc8a18928376ccafb25cacd0f7d40a9` | `1903e12fcadaf09322f944d01d927c216dc8a18928376ccafb25cacd0f7d40a9` | tests/tamper.sh |

All the published Lean library files (Chebyshev, SafePrime, General) are unchanged.

**README (step 6)**
- Added a section "Layers 14 and 15":
  - L14: 36 theorems, 18 `l14_*` and 18 `l14w_*`.
  - L15: 26 classical statements; 26 `cov_*` theorems prove 25 in full and Prime3_c in part (its case l = 1); 30 gated theorems.
  - Writer statement shown false: Prime3_c (Wertheim with `l ≥ 2`), counterexample p = 19, a = 8; the corrected form is proved.
- Updated the count lines:
  - Status: "17 named theorems. With the Layer 14 and 15 files … 83 theorems".
  - Verification bullet: "each of the 83 named theorems …".
  - Output line: `PASS (83 theorems, …)`.
- The README contained no machine paths.

**Overclaim review (addendum c)**
- No change was needed.
- L14 found no false or under-hypothesised restatement.
- The only false L15 statement (Prime3_c) is the writer's general-`l` form. The repository claims only `p = 2^k l + 1` with `l` prime, which is the writer's form with exponent `l = 1` (the writer's prime `q` is the repository's `l`). That claim is correct, and the README and `General.lean` docstrings do not claim the general Wertheim form.
- No docstring, proof or statement of a published theorem was touched.

**Commit (addendum d), not pushed**
- SHA: `b4ae30a94f5bc5bcba7e0143c239565af261038a`.
- Author and committer: `Josh Bald <jpbald93@gmail.com>`.
- Diffstat: 5 files changed, 1092 insertions(+), 5 deletions(-).
  - `PrimitiveRootFamilies.lean` +2
  - `L14.lean` +376
  - `L15Classical.lean` +704
  - `README.md` ±11
  - `gate.sh` ±4

```
$ git log --oneline -3
b4ae30a Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
5dd936f README: document Part 3 (General.lean), 17 theorems
e30457a General criterion for p = 2^k l + 1, with families for 2 and 3 (17 theorems, gate PASS)
```

`git status --short` before `git add -A`:
```
 M PrimitiveRootFamilies.lean
 M README.md
 M gate.sh
?? PrimitiveRootFamilies/L14.lean
?? PrimitiveRootFamilies/L15Classical.lean
```

`git status --short -b` after the commit:
```
## main...origin/main [ahead 1]
```
The tree is clean.

**Dropped / deviations**
- Nothing was dropped.
- Deviations from the scratch file: `instance` → `local instance` for the six `Fact (Nat.Prime N)` helpers. The new header docstring is my own text, and I reworded one phrase in it during editing; the writer's text is unchanged.
- Logs are outside the repository: `~/pubPrime_build.log`, `~/pubPrime_gate.log`, `~/pubPrime_tamper.log`.
