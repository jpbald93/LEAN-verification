# Paper K promotion — report

Host: jack (`jackagent@100.72.132.55`, gmktec, x86_64). Repo: `~/paperK`. Battery finished 2026-11-10 17:51 UTC.

## Commit

- sha: `7ba9b9720ab55ea3ec912c0b9ed82a450d2e16ed`
- message: `Paper K: Lie form, cofactor point, degenerate cases, three dimensions`
- author = committer = `Josh Bald <jpbald93@gmail.com>`, no Co-Authored-By, single commit, `git status` clean (0 entries). No remote.

## lake build

`flock ~/pi.lock … lake build` → `Build completed successfully (8710 jobs).` (11.5 s, Mathlib oleans reused through the
symlink; no `lake update`, no `cache get`). One style warning only: `PaperK/TwoD.lean:272:38` unnecessary `<;>`
(linter.unnecessarySeqFocus) — left as is (files are frozen).

## Gate (layer 1)

```
PASS (24 declarations, standard axioms only)
```
REQUIRED (24): `PaperK.{B_self_eq_zero_iff, tangency_identity, B_eq_zero_iff_tangent, mulVec_cofactor, B_G_cofactor_row,
prop31, prop31_cofactor, explicit_power, explicit_power_indep, equal_power}`, `PaperK2.{equal_power, equilateral_PX,
square_apollonius, square_null_space, square_PX, equal_power_point_unique, PX_circumcentre}`,
`PaperK3.{B_self_zero_iff, tangency_identity, equal_power, tetra_PX_origin, tetra_tangent_B, tetra_thm36,
tetra_affineIndependent}`. All report `[propext, Classical.choice, Quot.sound]`.

## Tamper (layer 2)

```
ok    sorry      rejected (exit 1): FAIL: forbidden token
ok    ax2line    rejected (exit 1): FAIL: forbidden token
ok    evalfake   rejected (exit 1): FAIL: forbidden token
ok    macro      rejected (exit 1): FAIL: forbidden token
ok    wrap       rejected (exit 1): FAIL: nonstandard axioms: PaperK.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp   rejected (exit 1): FAIL: build
ok    falsestmt  rejected (exit 1): FAIL: build
ok    falsehyp2  rejected (exit 1): FAIL: build
ok    falsestmt2 rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
9 planted defects (the template's 5 infrastructure attacks + 4 Paper K semantic ones), no PASS line in any tampered run.
Semantic defects: falsehyp drops `(hY : B Y Y = 0)` from `PaperK.tangency_identity`; falsestmt changes the null-cone
`2*(X 3)*(X 4)` to `3*…` in `B_self_eq_zero_iff`; falsehyp2 drops `(hD : D3 a b ≠ 0)` from
`PaperK2.equal_power_point_unique`; falsestmt2 changes the enclosing radius `√3 + 1` to `√3 + 2` in `PaperK3.tetra_thm36`.

## Battery

Report: `~/leancheck/reports/paperK_20261110_171742.md` (log alongside; local copy
`/tmp/afmrun/paperK/promote/paperK_20261110_171742.md`). HEAD in report = 7ba9b97, uncommitted 0.

| check | result |
|---|---|
| gate (layer 1) | PASS (24 declarations, standard axioms only) |
| tamper (layer 2) | 9/9 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 3 of 3 files ok |
| conclusion mutations (layer 4) | **226/241 rejected** (226 by error, 0 by timeout/heartbeat); 15 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 37 probed ok — no-hyp 23 |
| satisfiability (layer 8) | 33/60 certified [3 with hypotheses, 24 hypothesis-free binders, 6 closed], 27 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 33/60 credited, 27 unresolved |
| hypothesis ablation (layer 6) | 119 needed, **2 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 3 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 21 notions, 3 has-bridge, 18 NO-BRIDGE (see inventory.md) |

Notes for triage (not resolved in this job):
- Layer 9: 18 NO-BRIDGE — expected, no bridge module exists; recorded as a gap. No bridges invented.
- Layer 4 survivors (15), first-pass read: 3 × `tetra_centre_norm` and 8 × `tetra_affineIndependent` are mutations of
  concrete numeric data that stay true (sign flips leave √(1+1+1); other vertex sets are still affinely independent) —
  equivalent mutants, not weakness. `equilateral_centre_unique` [x^2→x^3], `square_apollonius_radii_ne`
  [1→2], `square_PX` [P 1→P 2, P 3→P 4] also survive; the square_PX ones mean that statement is stronger than shown
  (P 1 = P 2 = 0 forced) and the `/P 4` one is `x/0 = 0` slack — worth a hand look. None are in the 24-name gate list
  except `tetra_affineIndependent` and `square_PX`.
- Layer 6 unused: `equilateral_PX_param (_h4 : B P (circ r a b) = 0)` and `square_PX (_hP : P 3 ≠ 0)` — both already
  underscore-named in the source, i.e. known-redundant by design (4th circle / non-degeneracy not needed).
- Layer 8: 27 unresolved (automated witness search did not certify; not failures).

## Files (sha256)

```
6a19ca206116e5f78c7ef3596fc46dc36851324c48b708cccf1951a375f97581  PaperK/LieCore.lean   (= scratch/paperK_lie_core.lean)
a77e2e53dd80ef77e3a6b95938ddf2ce91790b5e03e8a9c72320f3c20dca8c7e  PaperK/TwoD.lean      (= scratch/paperK_degenerate2d.lean)
57af2130ad173eb17cb4861d01b75b3679390d840ca332f92fe8b0bd04e41b19  PaperK/ThreeD.lean    (= john l13_inversion/scratch/paperK_3d.lean)
106e49a3bc9be664ce5fab44729ef18fe49cf11957ff1935ece663e6f8fc8400  PaperK.lean
c214a206b952af7be18a971a9fa389c201c0354788d026ca11d08a6f0f956c3e  gate.sh
1ac7bce784cb9fbf20574f96cff87d6693ebcd80a1d5a04966e498872d7873a8  tests/tamper.sh
9ee89d546b0411ac9872ff9d24cb9db337a310f79760b8e903774a04e35b4def  lakefile.toml
ab486de198559df0c65f6e73b1bbf3851f4410612b9344436ec734242ed22f8d  lake-manifest.json   (copied from x_paperi_inversion)
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain       (leanprover/lean4:v4.33.1)
```
Plus `.gitignore` (`.lake/`, `.gatecheck_*`, `src/`).

## Renames / adaptations

- Lean files: copied byte-for-byte (sha unchanged). All three already start with `import Mathlib`; no edits, no
  renames. Namespaces `PaperK` / `PaperK2` / `PaperK3` are disjoint and no declaration sits at the root namespace, so
  same-named helpers (`B`, `equal_power`, `tangency_identity`) do not clash. Each file ends with its own
  `#print axioms` lines (harmless; build info only).
- scp jack→john failed (`Permission denied (publickey…)` — jack has no key for john). Relayed instead via this VM:
  `ssh john cat … | ssh jack 'cat > ~/paperK/src/paperK_3d.lean'`; sha verified 57af2130… on both ends. `src/` is
  git-ignored (staging copy only; the committed copy is `PaperK/ThreeD.lean`).
- lakefile.toml: from x_paperi_inversion with `name = "paperK"`, `defaultTargets = ["PaperK"]`, `[[lean_lib]] name =
  "PaperK"`; same mathlib require (`v4.33.1`), same `relaxedAutoImplicit = false`.
- `.lake/packages` → `~/x_paperi_inversion/.lake/packages` (which itself chains to
  `~/gates/primitive-root-families/.lake/packages`).
- gate.sh: template with NS/LIB = `PaperK`, SOURCES = `PaperK/*.lean PaperK.lean`, header line, REQUIRED = the 24 names;
  logic unchanged.
- tests/tamper.sh: template paths/names switched to PaperK; the template's 4 Inversion-specific semantic defects
  replaced by the 4 Paper K ones above (brief said "six planted defects"; the template actually runs 9, kept 9).
