# Paper CB — INTEGRATE Layers 14 + 15 (2026-10-22)

All work was inline, with no subagents.

## cayley-bacharach → `john:~/lean/pubCB_cayley-bacharach`

**Start point.** Copied from `~/lean/l14CB_cayley-bacharach`. The remote default branch is **master**, not main. `git fetch origin` and `git ls-remote` both show `origin/master = 9a4f11e`, the same as the L14 base, so there were no later GitHub commits to fast-forward over (no CITATION.cff etc. on this repo). The copy was on a detached HEAD at 9a4f11e, so I checked out `master` (same commit).

**Cleanup.** The untracked `scratch/` contents from L14 were removed, and there were no stray logs. `scratch/PaperAxioms.lean` and `scratch/paper_axioms.out` are **tracked files of the published repo** and the README cites them, so they were kept. Deleting them would have deleted published files. `.lake/packages` is still a symlink to `~/lean/clifford/.lake/packages`.

### New files
| file | lines | sha256 |
|---|---|---|
| CayleyBacharach/L14.lean | 1050 | b4d5e13c06d3d93551449aacc4811c5efc1bcde20b50b19c450a89f751d620d4 |
| CayleyBacharach/L15Classical.lean | 1040 | d32c2eeb45030f25d3dae5f390029d29f339c12e5464d429df888bed84f5d13a |

### How L15Classical.lean was built from scratch/L15_compare.lean (1652 lines)
- Imports `CayleyBacharach.L14`. Scratch Section 1 (lines 12–605) was a renamed copy of the L14 bridges (namespace `L15B`). I checked that it matches `L14.lean` line for line, then dropped the copy and replaced `open L15B` with `open CBL14`. This avoids duplicate declarations.
- Writer's definitions and `classical_*` Prop defs are verbatim (scratch lines 609–911); only `namespace PaperCB` became `namespace CayleyBacharach.Classical`. The header docstring is the required Layer-15 text.
- All comparison proofs are kept verbatim (scratch lines 915–1630): the `l15_*` bridges, 17 `cov_*` theorems (including the 4 proved obligations), and all NEW PROOF lemmas.
- Removed: the 18 trailing `#print axioms` lines. The scratch file had no set_option, macro, notation or #check, so no proof needed restructuring.
- **Counterexample theorems: none.** L15 found no writer statement false.
- `import CayleyBacharach.L15Classical` was appended as the last line of `CayleyBacharach.lean`, after the L14 import line.

### REQUIRED: published 100 → L14 127 → final 168 (+41)
- 17 `cov_*`: CB1_a, CB1_a_linear, CB1_b_part, CB1_b_irreducible_part, CB2_a, CB2_b_distinct_part, CB3_a, CB3_a_part, CB3_a_obligation, CB3_b, CB3_b_obligation, CB4_a, CB4_a_part, CB4_a_obligation, CB4_b, CB4_b_part, CB4_b_obligation.
- 24 NEW PROOF declarations: l15_papid, l15_cross_ne, l15_tri_ne, l15_on_line, l15_pappus_core, l15_pcol_flip, l15Qb, l15e3, l15Qb_quad, l15Qb_A/E/B/C/D, l15Qb_AB, l15Qc, l15_eval_Qc, l15_tri, l15_tri', l15_not_col4, l15_evalC_Qc, l15_aeval_hom, l15_mem_pointIdeal, l15_intMult_ne_zero_iff.
- All are prefixed `CayleyBacharach.Classical.`.

### Checks
- Build: `jl build` rc 0, "Build completed successfully (8729 jobs)".
- Gate (BSD system tools, `jl gate`): **PASS (168 declarations, standard axioms only)**. Of the 41 Layer-15 declarations, 40 report `[propext, Classical.choice, Quot.sound]` and 1 reports `[propext, Quot.sound]`.
- Tamper (`jl -g tamper`; GNU mode needed, see below):
```
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    falsehyp  rejected (exit 1): FAIL: build
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: PlaneCubic.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ALL TAMPERING TESTS REJECTED
```
- Forbidden grep `sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval`: **0 matches** in L15Classical.lean, and 0 in L14.lean.
- First gate run: FAIL (forbidden token). My own header comment contained the word "sorry"; I reworded the comment and re-ran.

### Hashes of pre-existing library files (published 9a4f11e vs final; first 16 hex digits)
| file | published | final |
|---|---|---|
| CayleyBacharach/Bridge.lean | 1d0e3efca8f268ed | 1d0e3efca8f268ed |
| CayleyBacharach/Classical.lean | f50b6d1995637b58 | f50b6d1995637b58 |
| CayleyBacharach/ClassicalF3.lean | b22b7bcedec29cba | b22b7bcedec29cba |
| CayleyBacharach/ClassicalFinite.lean | f7caaf4c4cf52be9 | f7caaf4c4cf52be9 |
| CayleyBacharach/ClassicalSmall.lean | 7c49380149782e77 | 7c49380149782e77 |
| CayleyBacharach/Conic.lean | b966d28feef9e2ae | b966d28feef9e2ae |
| CayleyBacharach/Criterion.lean | 2b3248660a9ee10b | 2b3248660a9ee10b |
| CayleyBacharach/CriterionIff.lean | 459d88cbc3aa056c | 459d88cbc3aa056c |
| CayleyBacharach/Defs.lean | 15ee54e1865a0db9 | 15ee54e1865a0db9 |
| CayleyBacharach/Factor.lean | fb613cc11ba655d5 | fb613cc11ba655d5 |
| CayleyBacharach/FiniteField.lean | 41ae930b8b9d55b9 | 41ae930b8b9d55b9 |
| CayleyBacharach/General.lean | bf39e491d2cc936d | bf39e491d2cc936d |
| CayleyBacharach/Hard.lean | b8b64adec1fc2f78 | b8b64adec1fc2f78 |
| CayleyBacharach/Line.lean | 2a8a3c0354ebcabe | 2a8a3c0354ebcabe |
| CayleyBacharach/LineRestrict.lean | 29614e44bb5cd6e0 | 29614e44bb5cd6e0 |
| CayleyBacharach/PappusClean.lean | dd0359df74d0310a | dd0359df74d0310a |
| CayleyBacharach/Pascal.lean | a6cc4c8280ea78fc | a6cc4c8280ea78fc |
| CayleyBacharach/PascalClean.lean | 9399b23f4ded45e9 | 9399b23f4ded45e9 |
| CayleyBacharach/Theorem.lean | d693324de2233a56 | d693324de2233a56 |
| CayleyBacharach/Through.lean | 3de6021d7b575336 | 3de6021d7b575336 |

Across all 49 tracked files, only `.gitignore`, `CayleyBacharach.lean`, `gate.sh` and `README.md` differ from 9a4f11e. `tests/tamper.sh`, `scratch/*` and `code/*` are unchanged.

### Addendum fixes
- **(a)** HEAD = origin/master = 9a4f11e, so nothing needed merging.
- **(b)** gate.sh line 31 `chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)` was replaced with `chk=".gatecheck_$$.lean"`, the form used in desargues HEAD. `.gatecheck_*` was added to `.gitignore`. The gate now passes with BSD tools.
- **Not fixed (outside the authorized edits): `tests/tamper.sh` uses GNU-only `sed -i` with no suffix argument.** Under BSD sed, 4 of 6 tests print "could not plant defect" and tamper exits 1. Under `jl -g` it reports ALL REJECTED. This should be made portable before pushing (for example, `sed -i.bak` plus rm, or a perl one-liner), but that needs a decision from the owner.
- **(c)** No L14 or L15 finding contradicts a repository claim. Note that the README's "`|K| > 10`" for Pascal and Pappus describes `pascal_clean` and `pappus_clean` correctly; L15 now adds every-field versions, and the new section says so. One discrepancy was fixed: the published README said "gate.sh checks 99 declarations" in three places, but the published gate already checked 100, because `finrank_ker_evalMap_eq_two_iff` was added in 9a4f11e without a README update. All counts now read 168, and the PaperAxioms sentence now says the paper run covers the 99 paper declarations while the gate checks more. No proof or statement was touched.
- **README:** added a "Layers 14 and 15" section and updated the declaration counts (99 → 168). No machine paths appear.
- **(d)** One local commit, author and committer `Josh Bald <jpbald93@gmail.com>`, **not pushed**:
  - SHA `d9c674c68c0a1b475a284f9bd33ec5f7e6d52689`
  - The message ends with a Co-Authored-By: Claude trailer (from the session's attribution rule). Amend it before pushing if you don't want it.
```
d9c674c Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
9a4f11e CriterionIff.lean: the eight-point criterion as a single iff (...); gate 100 declarations
0426550 Bridge.lean: bridge lemmas showing the local definitions (...); gate 99 declarations
```
- `git status --short`: before the commit it showed the following; after the commit it is empty (clean, `master` ahead of origin/master by 1).
```
M  .gitignore
M  CayleyBacharach.lean
A  CayleyBacharach/L14.lean
A  CayleyBacharach/L15Classical.lean
M  README.md
M  gate.sh
```

### Dropped
Nothing was dropped. No theorem needed set_option. The only declarations not carried over are the duplicate copies of L14 bridges, which are now imported from `CBL14`.
