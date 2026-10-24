# INTEGRATE REPORT: Paper CaseyFuss, Layers 14 + 15 → publication copies

Machine: jack (jack). All work was done inline with no subagents. The only background job was one nohup run of gate.sh and tamper.sh, which was waited on. **Nothing was pushed.**

## Starting point (addendum a)
- Both remotes use the default branch **`master`**, not `main`. `git fetch origin` found **no later commits**: origin/master is still the published commit (casey `a83c43b`, fuss `671efdc`), so no CITATION.cff, README or portable-gate commits were missing. The pub copies were checked out onto `master` (the L14 copies had a detached HEAD at the same commit) and the L14 files were re-applied unchanged.
- `scratch/Ax.lean` and `scratch/ax.out` are **tracked files of the published repo**, and the README describes them. Deleting them would remove published content, so they were **kept**. Only the untracked L15 scratch material was removed (it never existed in the pub copies). No stray logs were present. `fuss/code/*.out` are tracked published outputs and were kept.
- `.lake/packages` is still a symlink to `~/barbier/.lake/packages`. `.git` is the published history.

## Repo casey: ~/pubCaseyFuss_casey
| new file | lines | sha256 |
|---|---|---|
| Casey/L14.lean | 174 | ada14ccd6647e8d1f6511514ffb40f3e0a3a0c43f0145efe5a880ecc0c2cf7b4 |
| Casey/L15Classical.lean | 394 | d9e6265cc5aec9ecac5c0ed34c7e3a6e6c2175329db7759fe0f2d53507ab0537 |

- REQUIRED count: published **18** → L14 **25** → final **38**. The 13 added: `Casey.Classical.{tc_eq, int_dist, ext_dist, signed_bridge, no_mid, cyc_angles, casey_signed, radicand_nonneg}` (NEW PROOF lemmas), `cov_CaseyFuss1_a`, `cov_CaseyFuss1_b`, `cov_CaseyFuss1_a_obligation`, `cov_CaseyFuss1_b_obligation` (cov theorems and obligations), and `not_classical_CaseyFuss1_c` (counterexample; it carries the comment "The writer's statement `classical_CaseyFuss1_c` is false as written.").
- Build: `lake build` rc 0.
- Gate: `PASS (38 declarations, standard axioms only)`. Every new declaration reports `[propext, Classical.choice, Quot.sound]`.
- Tamper: sorry, ax2line, evalfake, macro, falsehyp and wrap were all rejected → `ALL TAMPERING TESTS REJECTED`.
- Forbidden grep on L15Classical.lean (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval, comments stripped): **0**.

## Repo fuss: ~/pubCaseyFuss_fuss
| new file | lines | sha256 |
|---|---|---|
| Fuss/L14.lean | 354 | 0d4231595bb8ced2fef3ab1fb0928aa297f6eb921591888eb1fff458bf555d1c |
| Fuss/L15Classical.lean | 418 | e85cd4c9406388a558926882b80cae8663d9b952269883c2b080a8963ad638d7 |

- REQUIRED count: published **34** → L14 **71** → final **84**. The 13 added: `Fuss.Classical.{tangentAt_of_side, ne_of_not_collinear, isBicentric_of_with, fuss_of_with, fuss_algebra, fuss_of_recip, tangentAt_of_lineTangent, not_collinear_of_mem, not_three}` (NEW PROOF lemmas) and `cov_CaseyFuss2_a_part`, `cov_CaseyFuss2_b_part`, `cov_CaseyFuss3_a_part`, `cov_CaseyFuss3_b_part`. There is no counterexample theorem; none of the writer's fuss statements was shown false. `instance factPl` was kept but not added to REQUIRED, because it is an instance and not a theorem.
- Build: `lake build` rc 0.
- Gate: `PASS (84 declarations, standard axioms only)`.
- Tamper: `ALL TAMPERING TESTS REJECTED` (all 6).
- Forbidden grep: **0**.

## How the L15 scratch files became library files (both repos)
- The writer's definitions and `classical_*` statements are verbatim, now in namespace `<Lib>.Classical`. The header docstring is the required text, plus one line noting the `def … : Prop` packaging.
- Removed: `set_option linter.unusedVariables false`, which leaves only harmless unused-binder linter warnings, and the 5 trailing `#print axioms` lines.
- `import Casey` / `import Fuss` was replaced by the root file's own imports, because the root now imports L15Classical and keeping `import <Lib>` would create a cycle. The root gets one line, `import <Lib>.L15Classical`, at the end.
- **One docstring edit to a writer definition:** the docstring of `directTangent` said "(formula from the notation)". The gate's token filter (`\bnotation\b`, which is not comment-aware) rejected it. The docstring now reads "(formula from the problem statement)". The definition body is unchanged. No other writer text was changed.
- No proof depended on maxHeartbeats. **Nothing was dropped.** No `sorry`.

## Hash table (sha256: published commit vs final tree)
| file | published | final | |
|---|---|---|---|
| casey/Casey.lean | 2a9a5a3bae6cc3c552b4d68db0e782559894b665eefd4148144bd264dac73337 | b89bba754db2756f554e84af828ead8ec1c23aca0aced1494497c8cd6282bafd | changed |
| casey/Casey/Basic.lean | e7aca8d2d02a424cf805c70c00f227142f89decf14bd65c59a401f0e8f57f5ac | e7aca8d2d02a424cf805c70c00f227142f89decf14bd65c59a401f0e8f57f5ac | same |
| casey/Casey/Bridge.lean | 2afb9042653a1a050e4ae1661ca567e1017b2321d8216924ed7fe9a48cacacf4 | 2afb9042653a1a050e4ae1661ca567e1017b2321d8216924ed7fe9a48cacacf4 | same |
| casey/Casey/Main.lean | 369fbf1162ddda0c798cf842f74e3214e312b8d3556d3f04bdf17b3e59334593 | 369fbf1162ddda0c798cf842f74e3214e312b8d3556d3f04bdf17b3e59334593 | same |
| casey/README.md | 014e3f092bb6078b661044d01bcae68fe43dddf17e504b680779b8f9a95a52d0 | 4341810760bab2f47f70967070978122a63607b6e2c5e99600113f03cab43a9f | changed |
| casey/gate.sh | 5cf37844450c52048d0e4593e0adc518c6a07b1759910738666629d1bc7ae391 | 53bc05c77fdd55608aa2ad101eba6257045996325673297d51b3cec82cf6f14a | changed |
| casey/scratch/Ax.lean | 46577a1bd4080e0371436bdf0e15e3559e111b42fe915a03b4e890753e6f1ec1 | 46577a1bd4080e0371436bdf0e15e3559e111b42fe915a03b4e890753e6f1ec1 | same |
| fuss/Fuss.lean | c095f02eb8263108f5812c05fbd597a1c6fcd764e1bf9163bcb79a9c14bfd79f | a55f89262ec5829ec2fe52cf73164a9d3a3a2f9fcf8b4bfb96462eb268c47b86 | changed |
| fuss/Fuss/Example.lean | 9c90f1d0d6ee28dfb38a01e22379901a05ee5a812783fd1b227a062b591b1762 | 9c90f1d0d6ee28dfb38a01e22379901a05ee5a812783fd1b227a062b591b1762 | same |
| fuss/Fuss/Forward.lean | ccb14e1cabd94d6cf4d10ba6ae561dec23b1fe8c4ddfd7204a9569d00d4d0116 | ccb14e1cabd94d6cf4d10ba6ae561dec23b1fe8c4ddfd7204a9569d00d4d0116 | same |
| fuss/Fuss/Geometry.lean | 4a8996c0a30a51513fb3268e863f0e33d83364770193da2ec4793bf718f17833 | 4a8996c0a30a51513fb3268e863f0e33d83364770193da2ec4793bf718f17833 | same |
| fuss/Fuss/Plane.lean | baa6fb1dba3956a4b824fb89c128387491413f3ba3758f9ba4779ee6b02f708c | baa6fb1dba3956a4b824fb89c128387491413f3ba3758f9ba4779ee6b02f708c | same |
| fuss/Fuss/Porism.lean | 33e27511ac40f054bde6662fc6646d6436d64c8e2a6ee881e059ad5a6db76ff7 | 33e27511ac40f054bde6662fc6646d6436d64c8e2a6ee881e059ad5a6db76ff7 | same |
| fuss/Fuss/Steps.lean | 3601e893d106d17f79506004de524f8b9d6a7aef8abdbc693e483620a8d1e9bd | 3601e893d106d17f79506004de524f8b9d6a7aef8abdbc693e483620a8d1e9bd | same |
| fuss/README.md | 5fed705504581a3089e993556a78c59f2a4522cd41b08fa6610f8bf43d9c8668 | 58e302083fe1fdf778bd57540ddad727294b67cfcebc353a0f711c6182286ba5 | changed |
| fuss/gate.sh | df464d2953035f6270ae945b63a8bfb092e19d3006484771b28f1efac5f1ee48 | 56429e15f496a72c5e227ac66fff9f8293dcb47fd88aeea922f88dcf7f6204eb | changed |
| fuss/scratch/Ax.lean | 8d747e2f4bdfc04dd78fcca2f9ce5dee32cd9e2666ceed0978985bb17b183e8b | 8d747e2f4bdfc04dd78fcca2f9ce5dee32cd9e2666ceed0978985bb17b183e8b | same |

Changes: root file +2 import lines; gate.sh: REQUIRED + chk line; README: counts + new section. Every other tracked file (LICENSE, lakefile, manifest, toolchain, tests/, code/) is byte-identical.

## Addendum (b): portable gate
Both gate.sh files used `chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)`. That single line was replaced with `chk=".gatecheck_$$.lean"` (the desargues form). `.gatecheck_*` was already in `.gitignore` in both repos, so .gitignore is unchanged. The full gate.sh diff is 2 lines: REQUIRED and chk.

## Addendum (c): README/docstring claims
- No Layer-14 or Layer-15 finding shows an existing repository claim to be wrong. casey's README already says "The converse … not formalised", so the false writer converse 1(c) is not a claim of this repo. fuss's README already says "convexity of the quadrilateral is not proved", which matches the parts left unproved in L15.
- README updates: the declaration counts (13→38 in casey, 34→84 in fuss, in 3 places each: status line, verification paragraph, PASS output line) and a new "Layers 14 and 15" section before "## Build". **Correction to a stale count:** casey's published README said "13 named declarations", but the published gate already checked 18, so that line was already wrong; it now says 38. No machine paths appear in the READMEs or the new files. The L15 header no longer mentions `/tmp/blindCaseyFuss/...`.

## Addendum (d): local commits (NOT pushed)
Author and committer: Josh Bald <jpbald93@gmail.com>. Message: exactly the requested text, with no Co-Authored-By trailer because the owner specified the message verbatim.

casey: commit **8e9058891620926763871d85a204a7a980354f21**
```
8e90588 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
a83c43b Add bridge lemmas: tangentCentre collinearity and tangency, tangentLength formula
5f6252c Initial public release: Lean 4 formalisation, gate, tamper tests, checking scripts
```
fuss: commit **c5a5915b223e5f7fce56e5c5dcaba450ef36ad48**
```
c5a5915 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
671efdc Initial public release: Lean 4 formalisation, gate, tamper tests, checking scripts
```

`git status --short` before commit (casey; fuss is the same with Fuss.*):
```
M  Casey.lean
A  Casey/L14.lean
A  Casey/L15Classical.lean
M  README.md
M  gate.sh
```
`git status --short` after commit: empty (clean) in both.

## Notes
- Remote default branch is `master`. Pushing would be `git push origin master`.
- Order: the final gate and tamper runs happened after every Lean and gate.sh edit, including the docstring rewording. Only the README.md files changed after those runs (text only, not part of the gate's sources).
