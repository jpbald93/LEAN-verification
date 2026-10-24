# Paper D: Layers 14 and 15 integration report

Date: 2026-10-22. Machine: jack (x86_64 Linux). Publication-ready copies: `jack:~/pubD_<repo>`.
**One local commit per repo, NOT pushed.**

## Summary

| repo | REQUIRED published → L14 → final | gate | tamper | dropped | commit (local, not pushed) |
|---|---|---|---|---|---|
| clifford | 20 → 38 → 63 | PASS (63 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none | `927f7f8` |
| cliffordchain | 32 → 53 → 63 | PASS (63 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none | `b6649f4` |
| fivecircles | 6 → 11 → 61 | PASS (61 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none | `6040681` |
| lester | 19 → 40 → 75 | PASS (75 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none | `d307293` |
| thebault | 12 → 24 → 34 | PASS (34 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none | `2edce1e` |
| kosnita | 11 → 18 → 25 | PASS (25 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none | `7eaae53` |
| blundon | 5 → 10 → 15 | PASS (15 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none | `50e1f17` |
| steinerlehmus | 3 → 8 → 10 | PASS (10 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED | none | `53b6246` |

Every gated declaration depends on a subset of `[propext, Classical.choice, Quot.sound]`.

**Writer statements shown false: none.** No Layer-15 file contains a `¬ classical_…` counterexample theorem, because none was produced. This agrees with the Layer-15 comparison (`jack:~/reformal/PAPERD_L15_COMPARE.md`): "No D classification against a writer statement was justified". It also agrees with the Layer-14 report: "no restatement was false or needed an extra hypothesis".

**Nothing was dropped.** No theorem needed `set_option`. The two proofs that timed out at the default heartbeat limit were split into lemmas (details per repo below).

## Method (same for every repo)

1. **Base = current GitHub HEAD (addendum a).** The L14 copies `john:~/lean/l14D_<repo>` were tarred over SSH (excluding `.lake`) to `jack:~/pubD_<repo>`. `.lake/packages` is a symlink to `~/barbier/.lake/packages`. `.lake/build` was seeded from the matching `~/l15D_<repo>`, which is at the same published commit, only to save build time. `git fetch origin` was run in every copy, and for all 8 repos `origin/main` equals the local HEAD (also checked with `git ls-remote`). So there were no later commits to fast-forward: no CITATION.cff, and the README and portable gate/tamper already at HEAD. The copies were on a detached HEAD at that commit. `git checkout main` (same SHA) was run before committing. No `scratch/` or stray logs were present in the L14 copies.
2. **gate.sh portability (addendum b).** No change was needed. All 8 published gates already use `chk=".gatecheck_$$.lean"` (no `mktemp --suffix`), and every `.gitignore` already lists `.gatecheck_*`.
3. **`<Lib>/L15Classical.lean`.** Source: `~/l15D_<repo>/scratch/L15_gaps.lean` where present (clifford, fivecircles, lester, thebault; it is a strict superset of `L15_compare.lean`, which is its first part), else `L15_compare.lean`. Transformation (script, mechanical):
   - `import <Lib>` was replaced by the root file's submodules, without `L14`. This avoids an import cycle, since the root now imports L15Classical. Lester's scratch also imported `Lester.Bridge`, which is among those submodules.
   - The required Layer-15 header docstring was added.
   - The namespace `PaperDClassical` was renamed to `<Lib>.Classical`. This is the only textual change to the writer's block.
   - All `#print axioms` lines were removed, as were all `set_option` lines (`linter.unusedVariables false` everywhere, plus `maxHeartbeats` in clifford, fivecircles and steinerlehmus). No `#check`, `#eval`, `macro`, `notation` or `run_cmd` was present.
   - Everything else is byte-for-byte the scratch file. A diff against the scratch, after only the steps above, is empty for cliffordchain, lester, thebault, kosnita, blundon and steinerlehmus. In clifford and fivecircles it differs only by the heartbeat splits described below.
   - The writer's definitions and the 18 `classical_*` `def … : Prop` statements are verbatim. All cov_*, gap_* ("NEW PROOF") lemmas and proved obligations are kept.
4. **Root file:** exactly one line, `import <Lib>.L15Classical`, was appended at the end.
5. **REQUIRED:** every `cov_*`, `gap_*` and obligation theorem of the new file was appended, fully qualified. Only that line of gate.sh changed. The `classical_*` Prop definitions and the few non-theorem helper `def`s (`planeIso`, `normalizeAt`, `gcross`, …) are not theorems, so they are not in REQUIRED. They are covered transitively.
6. **Checks:** `lake build` rc 0, `bash gate.sh`, `bash tests/tamper.sh`, the forbidden-token grep, and sha256 of every `.lean` file of the published commit.
7. **README.md:** the three declaration counts were updated (Status line, Verification sentence, Expected output), and a "Layers 14 and 15" section was added before "Build". No machine paths appear in any README; grep for `/home`, `/Users` and `~/` gave 0.
8. **Docstring/README claim fixes (addendum c):** one change, in cliffordchain's README only (see that section). No Lean file text was changed. Both the Layer-14 and Layer-15 reports found no false restatement.
9. **Commit (addendum d):** `git add -A` (the only changes were the 5 intended files), then one commit per repo with author and committer `Josh Bald <jpbald93@gmail.com>` and the requested message. **Not pushed.**

## clifford (`~/pubD_clifford`, base 209abaa = origin/main)

New files:

| file | lines | sha256 |
|---|---|---|
| `Clifford/L14.lean` | 700 | `9a8a9a5bcd9b68f67f3bd7fa284b2674e58643175cbef302c7d6feb8e7b2eb97` |
| `Clifford/L15Classical.lean` | 1328 | `e911c97872a2a6a41c7c7d01edd32e1ddbb6b95e321b8a43ec0a0005aea54732` |

REQUIRED: published 20 → L14 38 → final 63 (+25 Layer-15 names)

Added to REQUIRED: Clifford.Classical.cov_cospherical_transport Clifford.Classical.cov_collinear_transport Clifford.Classical.cov_cospherical_affine Clifford.Classical.cov_second_unique Clifford.Classical.cov_gp_normalize Clifford.Classical.cov_collinear_affine Clifford.Classical.cov_gam_cospherical Clifford.Classical.cov_D1_a_vertex0 Clifford.Classical.cov_D1_a_vertex1 Clifford.Classical.cov_D1_a_vertex2 Clifford.Classical.cov_D1_a_vertex3 Clifford.Classical.cov_D1_a_triples Clifford.Classical.cov_D1_a Clifford.Classical.cov_gamma_of_four Clifford.Classical.cov_D1_b Clifford.Classical.cov_mem_normalizeSphere Clifford.Classical.cov_D1_c_part Clifford.Classical.gap_gamma_of_four6 Clifford.Classical.gap_five_circle Clifford.Classical.gap_hz Clifford.Classical.gap_hn Clifford.Classical.gap_X_eq Clifford.Classical.gap_canon Clifford.Classical.cov_D1_c Clifford.Classical.cov_D1_c_exact

- build: `lake build` rc 0
- gate: `PASS (63 declarations, standard axioms only)`
- axioms: 60 depends on axioms: [propext, Classical.choice, Quot.sound];      3 depends on axioms: [propext, Quot.sound]
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on `Clifford/L15Classical.lean` (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check): 0 matches (0 including comments)

Hashes of the published `.lean` files (sha256 prefix, published commit → working tree):

| file | published | now | |
|---|---|---|---|
| `Clifford.lean` | `52390602933bbdaa` | `b8f194890b998f3c` | root: +2 import lines (L14, L15Classical) only |
| `Clifford/Basic.lean` | `af0870371913f189` | `af0870371913f189` | unchanged |
| `Clifford/Third.lean` | `8cc50f3de09a983a` | `8cc50f3de09a983a` | unchanged |

Dropped: none. Heartbeat restructuring: `cov_D1_a`: its 64-case `fin_cases` tail was moved verbatim into four helper lemmas, `cov_D1_a_vertex0..3`, plus a dispatcher `cov_D1_a_triples`. The statement of `cov_D1_a` is unchanged. The scratch's two `set_option maxHeartbeats 500000 in` (on `cov_gamma_of_four` and `gap_gamma_of_four6`) and the file-level `set_option maxHeartbeats 2000000` were simply removed: those proofs check at the default limit.

`git status --short` before commit:
```
 M Clifford.lean
 M README.md
 M gate.sh
?? Clifford/L14.lean
?? Clifford/L15Classical.lean
```
Commit: `927f7f82b3a1ae8342b1636b78bb9c04199c0d4b` (not pushed). `git status --short` after commit: empty.

`git log --oneline -3`:
```
927f7f8 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
209abaa Paper D: initial release (Lean 4.33.1, Mathlib 0df444a3)
```

## cliffordchain (`~/pubD_cliffordchain`, base ba083b2 = origin/main)

New files:

| file | lines | sha256 |
|---|---|---|
| `Clifford/L14.lean` | 671 | `57d5e7fece070b3022fbd92915a7526216772b70a26fcd0ada168b9e9253e110` |
| `Clifford/L15Classical.lean` | 474 | `87b27ab38ec19e4215f6cdba9cb0d360d9aef24f35473f05d247f2feac0ce3cd` |

REQUIRED: published 32 → L14 53 → final 63 (+10 Layer-15 names)

Added to REQUIRED: Clifford.Classical.cov_cospherical_transport Clifford.Classical.cov_collinear_transport Clifford.Classical.cov_D1_d_repository_classification Clifford.Classical.cov_D1_d_repository_counterexample Clifford.Classical.cov_D1_d_no_spherical_level_five Clifford.Classical.cov_D1_d_counterexample_not_writer_data Clifford.Classical.cov_D1_d_odd_three_part Clifford.Classical.cov_D1_d_even_repository_part Clifford.Classical.cov_D1_d_odd_repository_part Clifford.Classical.cov_D1_d_large_repository_failure

- build: `lake build` rc 0
- gate: `PASS (63 declarations, standard axioms only)`
- axioms: 63 depends on axioms: [propext, Classical.choice, Quot.sound]
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on `Clifford/L15Classical.lean` (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check): 0 matches (0 including comments)

Hashes of the published `.lean` files (sha256 prefix, published commit → working tree):

| file | published | now | |
|---|---|---|---|
| `Clifford.lean` | `c119b340423dff6c` | `69639406c62b6045` | root: +2 import lines (L14, L15Classical) only |
| `Clifford/Basic.lean` | `d5c14edbf2da8ec8` | `d5c14edbf2da8ec8` | unchanged |
| `Clifford/Bridge.lean` | `93eb80b639791dc7` | `93eb80b639791dc7` | unchanged |
| `Clifford/Classify.lean` | `ba4fc1b3c567f5d6` | `ba4fc1b3c567f5d6` | unchanged |
| `Clifford/Clean.lean` | `2a7cf40b4c473e56` | `2a7cf40b4c473e56` | unchanged |
| `Clifford/Counter6.lean` | `d6bf1cc913841fd4` | `d6bf1cc913841fd4` | unchanged |
| `Clifford/General.lean` | `90b42ad2f407f49b` | `90b42ad2f407f49b` | unchanged |

Dropped: none. No restructuring needed.

README claim fix (addendum c): the intro said `Counter6` is "an exact six-circle counterexample in general position". Layer 15 shows (`cov_D1_d_no_spherical_level_five`, `cov_D1_d_counterexample_not_writer_data`) that this family cannot meet the classical general-position hypotheses, because its level-five objects are forced to be lines. So the README now says "in general position in the sense of `GenPosN` (pairwise transversal, every triple `GenTriple`; weaker than requiring every intermediate circle to be a genuine circle)". The new README section states explicitly that `not_cliffordChain_of_six_le` concerns this repository's predicate and is not a counterexample to the classical theorem. No Lean docstring was changed: `Counter6.lean` already says "general position (`GenPosN`)".

`git status --short` before commit:
```
 M Clifford.lean
 M README.md
 M gate.sh
?? Clifford/L14.lean
?? Clifford/L15Classical.lean
```
Commit: `b6649f48bc4eaf192f729efd26a617fa2aeddfef` (not pushed). `git status --short` after commit: empty.

`git log --oneline -3`:
```
b6649f4 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
ba083b2 GENERAL_REPORT: correct the perturbation coefficient (exact: 4 - 4i + 50/eps)
df7d65c Classification: CliffordChain n ↔ n ≤ 5; exact six-circle counterexample (Clifford point at infinity)
```

## fivecircles (`~/pubD_fivecircles`, base f1fd9b7 = origin/main)

New files:

| file | lines | sha256 |
|---|---|---|
| `Fivecircles/L14.lean` | 136 | `57bb85e0cfb6a70c5c21aa3a5aea5af8397941c8f82be0fd821de9967a014ed2` |
| `Fivecircles/L15Classical.lean` | 1796 | `8fc8e84b629f95f49b2729018d621041ca7cfe2940e342343e1f9c00b781c99e` |

REQUIRED: published 6 → L14 11 → final 61 (+50 Layer-15 names)

Added to REQUIRED: Fivecircles.Classical.cov_cospherical_transport Fivecircles.Classical.cov_collinear_transport Fivecircles.Classical.cov_D2_part Fivecircles.Classical.gap_sphere_line Fivecircles.Classical.gap_idx_V Fivecircles.Classical.gap_idx_T Fivecircles.Classical.gap_idx_VT Fivecircles.Classical.gap_idx_ne Fivecircles.Classical.gap_idx_VQ Fivecircles.Classical.gap_idx_TQ Fivecircles.Classical.gap_D2_distinct Fivecircles.Classical.cov_D2_injQ Fivecircles.Classical.gap_core_distinct Fivecircles.Classical.gap_cd_degen Fivecircles.Classical.gap_core Fivecircles.Classical.gap_cd_perms Fivecircles.Classical.gap_cd_all_00 Fivecircles.Classical.gap_cd_all_01 Fivecircles.Classical.gap_cd_all_02 Fivecircles.Classical.gap_cd_all_03 Fivecircles.Classical.gap_cd_all_04 Fivecircles.Classical.gap_cd_all_10 Fivecircles.Classical.gap_cd_all_11 Fivecircles.Classical.gap_cd_all_12 Fivecircles.Classical.gap_cd_all_13 Fivecircles.Classical.gap_cd_all_14 Fivecircles.Classical.gap_cd_all_20 Fivecircles.Classical.gap_cd_all_21 Fivecircles.Classical.gap_cd_all_22 Fivecircles.Classical.gap_cd_all_23 Fivecircles.Classical.gap_cd_all_24 Fivecircles.Classical.gap_cd_all_30 Fivecircles.Classical.gap_cd_all_31 Fivecircles.Classical.gap_cd_all_32 Fivecircles.Classical.gap_cd_all_33 Fivecircles.Classical.gap_cd_all_34 Fivecircles.Classical.gap_cd_all_40 Fivecircles.Classical.gap_cd_all_41 Fivecircles.Classical.gap_cd_all_42 Fivecircles.Classical.gap_cd_all_43 Fivecircles.Classical.gap_cd_all_44 Fivecircles.Classical.gap_cd_all Fivecircles.Classical.gap_fivecircles Fivecircles.Classical.cov_D2 Fivecircles.Classical.cov_D2_exact Fivecircles.Classical.gap_line_ne_bot Fivecircles.Classical.gap_lines_meet Fivecircles.Classical.gap_idx_obl Fivecircles.Classical.cov_D2_obligation Fivecircles.Classical.cov_D2_obligation_exact

- build: `lake build` rc 0
- gate: `PASS (61 declarations, standard axioms only)`
- axioms: 7 depends on axioms: [propext];     54 depends on axioms: [propext, Classical.choice, Quot.sound]
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on `Fivecircles/L15Classical.lean` (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check): 0 matches (0 including comments)

Hashes of the published `.lean` files (sha256 prefix, published commit → working tree):

| file | published | now | |
|---|---|---|---|
| `Fivecircles.lean` | `a69693caa0b31f7d` | `62194e4bedd7bcf6` | root: +2 import lines (L14, L15Classical) only |
| `Fivecircles/Basic.lean` | `edb1ef3c43d75539` | `edb1ef3c43d75539` | unchanged |

Dropped: none. Heartbeat restructuring: `gap_cd_all`: the 625-case `fin_cases` proof (scratch: `set_option maxHeartbeats 4000000 in`) was split into 25 lemmas `gap_cd_all_ab`, one per first index pair (a, b), each with the original tactic text. `gap_cd_all` itself keeps its statement and dispatches to them.

`git status --short` before commit:
```
 M Fivecircles.lean
 M README.md
 M gate.sh
?? Fivecircles/L14.lean
?? Fivecircles/L15Classical.lean
```
Commit: `6040681ed19d180325f87162f690ebdad4a96961` (not pushed). `git status --short` after commit: empty.

`git log --oneline -3`:
```
6040681 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
f1fd9b7 Paper D: initial release (Lean 4.33.1, Mathlib 0df444a3)
```

## lester (`~/pubD_lester`, base 9f94754 = origin/main)

New files:

| file | lines | sha256 |
|---|---|---|
| `Lester/L14.lean` | 438 | `af92353822cd9daf8d2b8d55814aec27249dfff72b980e22bfc6dde907f12880` |
| `Lester/L15Classical.lean` | 871 | `aeb071baa900c902ce0204231ee75b9bbda5671780f04e82cb47acb54cc9a5ac` |

REQUIRED: published 19 → L14 40 → final 75 (+35 Layer-15 names)

Added to REQUIRED: Lester.Classical.cov_cospherical_transport Lester.Classical.cov_collinear_transport Lester.Classical.cov_D3_part Lester.Classical.gap_lineMap_coord Lester.Classical.gap_pt_ext Lester.Classical.gap_cross_of_mem Lester.Classical.gap_mem_of_cross Lester.Classical.gap_opp_cross_neg Lester.Classical.gap_same_cross_pos Lester.Classical.gap_iso_re Lester.Classical.gap_iso_im Lester.Classical.gap_ccw_iff Lester.Classical.gap_apex_alg Lester.Classical.gap_apex_char Lester.Classical.gap_ne_of_apex Lester.Classical.gap_outer_apex Lester.Classical.gap_inner_apex Lester.Classical.gap_mem_line_map Lester.Classical.gap_fermat_outer Lester.Classical.gap_fermat_inner Lester.Classical.cov_D3 Lester.Classical.cov_D3_exact Lester.Classical.gap_dist_sq Lester.Classical.gap_apx_dist Lester.Classical.gap_apx_cross Lester.Classical.gap_opp_of_cross_neg Lester.Classical.gap_same_of_cross_pos Lester.Classical.gap_ne_sq Lester.Classical.gap_apx_outer Lester.Classical.gap_apx_inner Lester.Classical.gap_concurrent Lester.Classical.gap_nondeg_alg Lester.Classical.gap_nondeg Lester.Classical.cov_D3_obligation Lester.Classical.cov_D3_obligation_exact

- build: `lake build` rc 0
- gate: `PASS (75 declarations, standard axioms only)`
- axioms: 75 depends on axioms: [propext, Classical.choice, Quot.sound]
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on `Lester/L15Classical.lean` (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check): 0 matches (0 including comments)

Hashes of the published `.lean` files (sha256 prefix, published commit → working tree):

| file | published | now | |
|---|---|---|---|
| `Lester.lean` | `43f0ce5334962300` | `9b8988d351c39d4d` | root: +2 import lines (L14, L15Classical) only |
| `Lester/Basic.lean` | `bf6ada6147870f60` | `bf6ada6147870f60` | unchanged |
| `Lester/Bridge.lean` | `0146ff68ccb97feb` | `0146ff68ccb97feb` | unchanged |
| `Lester/Proof.lean` | `927dbab69793a28c` | `927dbab69793a28c` | unchanged |

Dropped: none. No restructuring needed.

`git status --short` before commit:
```
 M Lester.lean
 M README.md
 M gate.sh
?? Lester/L14.lean
?? Lester/L15Classical.lean
```
Commit: `d307293ba23b92aece5f81b971704e6e11641bfa` (not pushed). `git status --short` after commit: empty.

`git log --oneline -3`:
```
d307293 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
9f94754 Paper D: initial release (Lean 4.33.1, Mathlib 0df444a3)
```

## thebault (`~/pubD_thebault`, base c37f92e = origin/main)

New files:

| file | lines | sha256 |
|---|---|---|
| `Thebault3/L14.lean` | 233 | `85859ee95d1fc587020e610d98172f35ccf1261d9cb2fded18b9d4fe0fa66836` |
| `Thebault3/L15Classical.lean` | 661 | `77474a3c4159f26b7d74086cae2006e918221ff57f8fdd824ee858d5cde00905` |

REQUIRED: published 12 → L14 24 → final 34 (+10 Layer-15 names)

Added to REQUIRED: Thebault3.Classical.cov_D4_part Thebault3.Classical.cov_D4_swapped_part Thebault3.Classical.cov_cross_zero_of_mem Thebault3.Classical.cov_sameSide_of_cross_pos Thebault3.Classical.cov_opp_cross_neg Thebault3.Classical.cov_D4 Thebault3.Classical.gap_opp_of_cross_neg Thebault3.Classical.gap_thebault_one Thebault3.Classical.cov_D4_obligation Thebault3.Classical.cov_D4_obligation_exact

- build: `lake build` rc 0
- gate: `PASS (34 declarations, standard axioms only)`
- axioms: 34 depends on axioms: [propext, Classical.choice, Quot.sound]
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on `Thebault3/L15Classical.lean` (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check): 0 matches (0 including comments)

Hashes of the published `.lean` files (sha256 prefix, published commit → working tree):

| file | published | now | |
|---|---|---|---|
| `Thebault3.lean` | `c573cb166c6288f9` | `fed48faffb0291e9` | root: +2 import lines (L14, L15Classical) only |
| `Thebault3/Basic.lean` | `4de2ef21bd68f4fb` | `4de2ef21bd68f4fb` | unchanged |

Dropped: none. No restructuring needed.

`git status --short` before commit:
```
 M Thebault3.lean
 M README.md
 M gate.sh
?? Thebault3/L14.lean
?? Thebault3/L15Classical.lean
```
Commit: `2edce1eecc7b97faefa8580bddaef955ab44bf73` (not pushed). `git status --short` after commit: empty.

`git log --oneline -3`:
```
2edce1e Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
c37f92e Paper D: initial release (Lean 4.33.1, Mathlib 0df444a3)
```

## kosnita (`~/pubD_kosnita`, base 702f026 = origin/main)

New files:

| file | lines | sha256 |
|---|---|---|
| `Kosnita/L14.lean` | 176 | `78f2026a1361f8556dbf7607e9600dc6ef01402fd6ab4e19f7353b96d7ab624c` |
| `Kosnita/L15Classical.lean` | 523 | `d3d3508a6785c73806059bac56bffc16e171a32f7349ea6af1c4dac805ca5c57` |

REQUIRED: published 11 → L14 18 → final 25 (+7 Layer-15 names)

Added to REQUIRED: Kosnita.Classical.cov_D5_obligation Kosnita.Classical.cov_D5_part Kosnita.Classical.cov_auxiliary_nondegenerate Kosnita.Classical.cov_D5_nonparallel_part Kosnita.Classical.cov_parallel_of_cross_zero Kosnita.Classical.cov_Kosnita_zero_locus Kosnita.Classical.cov_D5

- build: `lake build` rc 0
- gate: `PASS (25 declarations, standard axioms only)`
- axioms: 25 depends on axioms: [propext, Classical.choice, Quot.sound]
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on `Kosnita/L15Classical.lean` (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check): 0 matches (0 including comments)

Hashes of the published `.lean` files (sha256 prefix, published commit → working tree):

| file | published | now | |
|---|---|---|---|
| `Kosnita.lean` | `8e71f74002d1686f` | `613749ce831d108f` | root: +2 import lines (L14, L15Classical) only |
| `Kosnita/Basic.lean` | `fd896c45dd7ca525` | `fd896c45dd7ca525` | unchanged |

Dropped: none. No restructuring needed.

`git status --short` before commit:
```
 M Kosnita.lean
 M README.md
 M gate.sh
?? Kosnita/L14.lean
?? Kosnita/L15Classical.lean
```
Commit: `7eaae5300ce68cf3c0eb59fbc52d8456c4c7f819` (not pushed). `git status --short` after commit: empty.

`git log --oneline -3`:
```
7eaae53 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
702f026 Paper D: initial release (Lean 4.33.1, Mathlib 0df444a3)
```

## blundon (`~/pubD_blundon`, base 118b4c9 = origin/main)

New files:

| file | lines | sha256 |
|---|---|---|
| `Blundon/L14.lean` | 142 | `d97ede3de21a9885337c347c5d19001b497ffb4bdc3cb9d0ac2d2896da79b382` |
| `Blundon/L15Classical.lean` | 485 | `117d461c955e703db0c592c7cdd6be90bf18ca285940e4913615458d80042d3f` |

REQUIRED: published 5 → L14 10 → final 15 (+5 Layer-15 names)

Added to REQUIRED: Blundon.Classical.cov_D6_lower Blundon.Classical.cov_D6_upper Blundon.Classical.cov_radicand_core Blundon.Classical.cov_triangle_radicand Blundon.Classical.cov_D6_obligation

- build: `lake build` rc 0
- gate: `PASS (15 declarations, standard axioms only)`
- axioms: 15 depends on axioms: [propext, Classical.choice, Quot.sound]
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on `Blundon/L15Classical.lean` (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check): 0 matches (0 including comments)

Hashes of the published `.lean` files (sha256 prefix, published commit → working tree):

| file | published | now | |
|---|---|---|---|
| `Blundon.lean` | `1e39f6b38043d6e5` | `33eebfe1ba186291` | root: +2 import lines (L14, L15Classical) only |
| `Blundon/Basic.lean` | `1c8c6e3dc5fec32c` | `1c8c6e3dc5fec32c` | unchanged |

Dropped: none. No restructuring needed.

`git status --short` before commit:
```
 M Blundon.lean
 M README.md
 M gate.sh
?? Blundon/L14.lean
?? Blundon/L15Classical.lean
```
Commit: `50e1f17b92bd09d2fc515fb46133f2f84b46ff6c` (not pushed). `git status --short` after commit: empty.

`git log --oneline -3`:
```
50e1f17 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
118b4c9 Paper D: initial release (Lean 4.33.1, Mathlib 0df444a3)
```

## steinerlehmus (`~/pubD_steinerlehmus`, base a3a3d26 = origin/main)

New files:

| file | lines | sha256 |
|---|---|---|
| `SteinerLehmus/L14.lean` | 102 | `b9249d5fe2a2ff84c2fa035ddeae969ae95c828b925db46feee42182f7b4543e` |
| `SteinerLehmus/L15Classical.lean` | 402 | `8b7a7733ab665292f35441d936d7346e6ae3ae85bd6f1297b392897046c81abd` |

REQUIRED: published 3 → L14 8 → final 10 (+2 Layer-15 names)

Added to REQUIRED: SteinerLehmus.Classical.cov_D7 SteinerLehmus.Classical.cov_D7_obligation

- build: `lake build` rc 0
- gate: `PASS (10 declarations, standard axioms only)`
- axioms: 10 depends on axioms: [propext, Classical.choice, Quot.sound]
- tamper: `ALL TAMPERING TESTS REJECTED`
- forbidden grep on `SteinerLehmus/L15Classical.lean` (sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval|#check): 0 matches (0 including comments)

Hashes of the published `.lean` files (sha256 prefix, published commit → working tree):

| file | published | now | |
|---|---|---|---|
| `SteinerLehmus.lean` | `1669aa19e66ba804` | `c0a5e90ac4a8636d` | root: +2 import lines (L14, L15Classical) only |
| `SteinerLehmus/Basic.lean` | `41068d509f4ae50a` | `41068d509f4ae50a` | unchanged |

Dropped: none. Heartbeat restructuring: The scratch's file-level `set_option maxHeartbeats 2000000` before `cov_D7_obligation` was removed. The proof checks at the default limit, unchanged.

`git status --short` before commit:
```
 M SteinerLehmus.lean
 M README.md
 M gate.sh
?? SteinerLehmus/L14.lean
?? SteinerLehmus/L15Classical.lean
```
Commit: `53b62463cb50388b51e7a703afeb08e7c8f1ebdc` (not pushed). `git status --short` after commit: empty.

`git log --oneline -3`:
```
53b6246 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
a3a3d26 Paper D: initial release (Lean 4.33.1, Mathlib 0df444a3)
```
