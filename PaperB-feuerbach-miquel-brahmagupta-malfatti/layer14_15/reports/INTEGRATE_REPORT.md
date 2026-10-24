# Paper B: Layer 14/15 integration report

Machine: jack (`jack`). Output copies: `~/pubB_feuerbach`, `~/pubB_brahmagupta`, `~/pubB_miquel`, `~/pubB_malfatti`.
Each copy is `cp -a` of the matching `~/l14B_<repo>`. The copies keep `.git`, which holds the published history; nothing was committed or pushed. They also keep the `.lake/packages` symlink (→ `/home/jack/barbier/.lake/packages`). There was no `scratch/` directory and there were no stray logs to remove.

## What changed in each repo (same for all four)
- New file `<Lib>/L15Classical.lean`, made from `~/l15B_<repo>/scratch/L15_compare.lean`:
  - Removed: the `import` lines and the scratch header docstring. They are replaced by imports of the library modules (every module except the root file, so there is no import cycle) and the required Layer 15 docstring.
  - Removed: all `#print axioms` lines. These were the only forbidden commands in the scratch files: there was no `set_option`, `macro`, `notation`, `run_cmd`, `#check` or `#eval`.
  - Renamed the namespace `PaperBClassical` → `<Lib>.Classical`.
  - The writer's `def`s (`classical_*` and the helper definitions `tri`, `IsConvexQuad`, `quadArea`, `IsMalfattiTriple`) are byte-identical to the scratch file. The proofs are unchanged too. I checked this with `diff` against the scratch file after renaming the namespace on both sides.
  - Text edits:
    - Brahmagupta only: one comment line added before `cov_B3_remark_cyclic_iff_false`.
    - Malfatti only: in a docstring that I wrote (not the writer's), "writer's notation" became "writer's variables". The task's grep pattern `notation` matches inside comments, so this keeps that grep at 0.
    - Miquel only: the scratch header's note on carrying `E2` over to `ℂ` was dropped together with the rest of the scratch header. The README now states it.
- `<Lib>.lean`: the line `import <Lib>.L15Classical` is appended at the end. The L14 import line was already there.
- `gate.sh`: only the `REQUIRED=` line changed (`git diff gate.sh`: 1 line removed, 1 added). It gained every `cov_*` theorem, NEW PROOF lemma/def, obligation and counterexample. The writer's `classical_*` Prop definitions are not in REQUIRED.
- `README.md`: new section "Layers 14 and 15", inserted before "## Verification". The declaration count was updated in three places: the Status line, the gate description and the `PASS (...)` line. No machine paths appear in any README (grep for `/home|/Users|jack` finds 0).
- Nothing was dropped: no theorem used `set_option maxHeartbeats`. No theorem contains `sorry`.

The forbidden-token grep below was run on `<Lib>/L15Classical.lean`:
`grep -cE "sorry|admit|native_decide|axiom|set_option|macro|notation|run_cmd|#print|#eval"` → **0 in all four repos**, counting comments as well.

---

## feuerbach (`~/pubB_feuerbach`)
| new file | lines | sha256 |
|---|---|---|
| Feuerbach/L14.lean | 136 | bdc9d756ca2f85cc07789961645164e9f7b36bbae00041fef5839642db34ff51 |
| Feuerbach/L15Classical.lean | 233 | e34e0b6536a1cf7df68d2e9722eaea211326a5db2cd1242858ae2200131a4bee |

- REQUIRED: published 46 → L14 54 → **final 71** (+17: 5 cov from the repo (one is the excentre-existence obligation, proved from Mathlib), 10 NEW PROOF lemmas/defs for tangent lengths and `l15_equilateral_iff`, 2 cov remarks with new proofs)
- Build: `lake build` rc 0
- Gate: `PASS (71 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- Forbidden grep: 0
- Counterexamples: none. All 7 writer statements are proved.
- Dropped: nothing

| published library file | sha256 (HEAD) | working copy |
|---|---|---|
| Feuerbach/Algebra.lean | 015176ce7796f94bd69fe5756eed4cfa499e4241462ff3f51acd3468bee34c29 | same |
| Feuerbach/Bridge.lean | a42d8d13dd2eb57dab5549e68b06067464e961bac404ed4e29893c38c0de94cc | same |
| Feuerbach/Geometry.lean | 3e408628d2e56a5fcb98df45df068e40f1a3902ad2eed300f444e0d26e4eb1ab | same |
| Feuerbach/Main.lean | 2338aa8f0c6db79df52ffc610d749c6138a1891655cb3fba3f1b9b863e070ff2 | same |
| Feuerbach/Witness.lean | 8b19f930a99c816ea497d8e26f7224f6465a7ec77888c5d6613eba4c3b5c25f4 | same |

```
 M Feuerbach.lean
 M README.md
 M gate.sh
?? Feuerbach/L14.lean
?? Feuerbach/L15Classical.lean
```

## brahmagupta (`~/pubB_brahmagupta`)
| new file | lines | sha256 |
|---|---|---|
| Brahmagupta/L14.lean | 96 | 1a0e09bd8a65fb3a0480fd918298bd946ffb5a2a909b65c53a8f55aead827024 |
| Brahmagupta/L15Classical.lean | 282 | c8739e52a92cc178415d4fb288966e2eeba8ca2c7d09da75caf085cd42017097 |

- REQUIRED: published 30 → L14 35 → **final 50** (+15)
- Build: rc 0
- Gate: `PASS (50 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- Forbidden grep: 0
- **Writer statement shown false:** `classical_B3_remark_cyclic_iff`, refuted by `Brahmagupta.Classical.cov_B3_remark_cyclic_iff_false`. The collinear points A=0, D=1/4, C=1, B=2 satisfy `IsConvexQuad`, and the angle sum is 0+π. Four distinct collinear points are not cospherical. A one-line comment is in place. The forward direction is proved for positive side lengths (`cov_B3_remark_cyclic_iff_part`).
- B3(a), B3(b) and Bretschneider are proved for the shoelace area (`*_part`). For the writer's Lebesgue area they are proved only under the explicit hypothesis `AreaBridge` (`*_of_bridge`). The obligation is proved from Mathlib.
- Dropped: nothing

| published library file | sha256 (HEAD) | working copy |
|---|---|---|
| Brahmagupta/Basic.lean | 7c5a02a5aab18847d3a71dd8022458899851e4b2ff23783d8f2d32b564b0d4f8 | same |
| Brahmagupta/Bridge.lean | ee898182ccb1496ad71fc6585b824d730f9fa417d1481e967d93723599a687c8 | same |
| Brahmagupta/Cyclic.lean | 3214326b4ff6375223dace7a7788ab096fc3da20f8754da996970c745f98a534 | same |
| Brahmagupta/Examples.lean | e7736aae1b2499e0a9cc1563e1e195484250d4f28bb0f77327af36b13e30f2f3 | same |

```
 M Brahmagupta.lean
 M README.md
 M gate.sh
?? Brahmagupta/L14.lean
?? Brahmagupta/L15Classical.lean
```

## miquel (`~/pubB_miquel`)
| new file | lines | sha256 |
|---|---|---|
| Miquel/L14.lean | 168 | badaf583233e82825b967d3df5c88ea16863a24b8a9a3f1d2931c527b475d245 |
| Miquel/L15Classical.lean | 139 | e089803dc8e4ef75c4b965d3f9e362802e5b230a04eef65a617ed42671118317 |

- REQUIRED: published 84 → L14 91 → **final 101** (+10)
- Build: rc 0
- Gate: `PASS (101 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- Forbidden grep: 0
- Counterexamples: none. All 3 writer statements are proved: B2(a), B2(b), and the obligation (new proof).
- Dropped: nothing

| published library file | sha256 (HEAD) | working copy |
|---|---|---|
| Miquel/Basic.lean | 8c317d7e7fd11d31ffdeb8991b2451e9277885ee457495e7b5f8cde0c4f58352 | same |
| Miquel/Bridge.lean | ab22a5723f0a5648ed1fae50a48d63ef51c5954a8a24747483a00848cde97d3b | same |
| Miquel/Coeffs.lean | 675240428688a87ad38e30ff0542d4bd836145405d030dde881affc915aeeb6e | same |
| Miquel/Frame.lean | 1697ebafec3c663b4c14866f90d98d6574b19390890ee08ee511e4243b6eb5d4 | same |
| Miquel/Main.lean | 58b4bb105b10c5d381807845e4264f0054410ad60f175b8f6aa7c71420070944 | same |
| Miquel/Witness.lean | 71dd8ea7b9b0444ae3c448121bf6f54a527f149c0939813707377c4db6e78f2d | same |

```
 M Miquel.lean
 M README.md
 M gate.sh
?? Miquel/L14.lean
?? Miquel/L15Classical.lean
```

## malfatti (`~/pubB_malfatti`)
| new file | lines | sha256 |
|---|---|---|
| Malfatti/L14.lean | 138 | 38d872a600df614579f9ef306c9e8af868e58cbca61b13ebd2bcf4ed30c5dc82 |
| Malfatti/L15Classical.lean | 239 | 64507ae484f85a912efe249ac6ba44fec0852559fa75df91322086dac0b0a583 |

- REQUIRED: published 77 → L14 84 → **final 93** (+9)
- Build: rc 0
- Gate: `PASS (93 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- Forbidden grep: 0
- Counterexamples: none. Proved: B4(a) (with a new proof that each disc lies in the triangle), the B4(b) obligation, and B4(b) for the constructed triple (`cov_B4_b_part`). B4(b) for an arbitrary triple is proved only under the writer's uniqueness statement `classical_B4_a_unique` (`cov_B4_b_of_unique`); uniqueness itself is not proved.
- Dropped: nothing

| published library file | sha256 (HEAD) | working copy |
|---|---|---|
| Malfatti/Algebra.lean | 4e3b8617128e5caa6a58b2c3e9a4f9de405014c054bffe711537f7f793a6e9dc | same |
| Malfatti/Bridge.lean | d8cbe706503cf04754c46bdf1731e7b50f3969758b87f371146ae9af6e3d63d9 | same |
| Malfatti/Geometry.lean | c4a714e9fa5cf4af84b98130913c19dc885ebc9de78521ffdcdb508701ae6232 | same |
| Malfatti/Main.lean | ae27e5a2df244caafb545983f34278dc6888bda21ee7cdd67c3415a49b855507 | same |
| Malfatti/Witness.lean | 0eef993496fc0f8188ef544bb105f6776add0f6d7c9629e58445a769f135e6ee | same |

```
 M Malfatti.lean
 M README.md
 M gate.sh
?? Malfatti/L14.lean
?? Malfatti/L15Classical.lean
```

## Summary
| repo | REQUIRED pub → L14 → final | gate | tamper | forbidden grep | false writer statements | dropped |
|---|---|---|---|---|---|---|
| feuerbach | 46 → 54 → 71 | PASS (71) | all rejected | 0 | none | none |
| brahmagupta | 30 → 35 → 50 | PASS (50) | all rejected | 0 | `classical_B3_remark_cyclic_iff` | none |
| miquel | 84 → 91 → 101 | PASS (101) | all rejected | 0 | none | none |
| malfatti | 77 → 84 → 93 | PASS (93) | all rejected | 0 | none | none |

Notes:
- All published library files are byte-identical to HEAD.
- `git status` lists only the root file, `gate.sh` and `README.md` as modified, plus the two new files. `README.md` is modified because step 6 asked for it.

## Commit step

Applies to all four copies:
- **Branch fix.** Each copy was a detached HEAD at the cited commit, and local `main` was at origin's tip. The first `git stash` / `git merge --ff-only origin/main` attempt left `HEAD` where it was. I restored the working changes, re-stashed them (`stash -u`), ran `git checkout main` and then `git merge --ff-only origin/main` ("Already up to date": local `main` already equals `origin/main`), and ran `git stash pop`. The pop had no conflicts. The untracked L14/L15 files were byte-identical to the stashed copies. No stash entries are left over.
- **Merged origin commits.** In every copy `git log HEAD..origin/main` listed 2 commits: "README: cite commit …" and "Add Apache-2.0 licence and citation metadata". They touch only `README.md`, `LICENSE` and `CITATION.cff`. README: both texts kept (origin's "How to run the checks" section and new citation, plus our "Layers 14 and 15" section and updated declaration counts). gate.sh: origin did not change it. Our version has the portable `chk=".gatecheck_$$.lean"` line and the extended REQUIRED.
- **Gate fix (b): no.** gate.sh already uses `chk=".gatecheck_$$.lean"` (no `mktemp --suffix`), and `.gitignore` already contains `.gatecheck_*`.
- `lake build` rc 0 in all four. The commit author and committer are both `Josh Bald <jpbald93@gmail.com>`. Each copy is on `main`, 1 commit ahead of `origin/main` and 0 behind. **Nothing was pushed.**
- Each commit holds exactly 5 files: `<Lib>.lean`, `<Lib>/L14.lean`, `<Lib>/L15Classical.lean`, `README.md`, `gate.sh`.

### feuerbach (`~/pubB_feuerbach`)
- Origin commits merged: `0d74b3d` README: cite commit 2bf4190…; `6a24f74` Add Apache-2.0 licence and citation metadata
- Gate fix: no (already portable)
- Gate: `PASS (71 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- New commit: `83d2486e8c67c26e9642550be397652f72f16850`
```
83d2486 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
6a24f74 Add Apache-2.0 licence and citation metadata
0d74b3d README: cite commit 2bf41901548aed8b0e43d2f1bd10bb1a1d54ebf8
```
- `git status --short`: (empty)

### brahmagupta (`~/pubB_brahmagupta`)
- Origin commits merged: `7a9876c` README: cite commit c5c3ce0…; `df2833a` Add Apache-2.0 licence and citation metadata
- Gate fix: no (already portable)
- Gate: `PASS (50 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- New commit: `ded0ff1c47909479590b1d13ccba1d0d5d14ba26`
```
ded0ff1 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
df2833a Add Apache-2.0 licence and citation metadata
7a9876c README: cite commit c5c3ce014dc450ca212df76fade8948aa45421e0
```
- `git status --short`: (empty)

### miquel (`~/pubB_miquel`)
- Origin commits merged: `ebcbab9` README: cite commit 401de13…; `3190819` Add Apache-2.0 licence and citation metadata
- Gate fix: no (already portable)
- Gate: `PASS (101 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- New commit: `9f99fbf4ebc027ea5861abe11416e55bde85a7a6`
```
9f99fbf Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
3190819 Add Apache-2.0 licence and citation metadata
ebcbab9 README: cite commit 401de13c0c4e51f67f87f7252f147048084c4a01
```
- `git status --short`: (empty)

### malfatti (`~/pubB_malfatti`)
- Origin commits merged: `ad1261e` README: cite commit d395193…; `716cb46` Add Apache-2.0 licence and citation metadata
- Gate fix: no (already portable)
- Gate: `PASS (93 declarations, standard axioms only)`
- Tamper: `ALL TAMPERING TESTS REJECTED`
- New commit: `c0f16c5521c524eba5a787e68e7568fde738208f`
```
c0f16c5 Add Layer-14 (Mathlib-only restatements, witnesses) and Layer-15 (classical-statement comparison) files
716cb46 Add Apache-2.0 licence and citation metadata
ad1261e README: cite commit d39519346e71c9af8c349490a4dac5388de4d8f2
```
- `git status --short`: (empty)

### Re-verification (2026-10-22, later pass)
I re-ran the commit step on the four copies and found it already complete. Nothing was changed, re-committed or pushed.
- `git fetch origin`, then `git log HEAD..origin/main`: empty in all four. No new origin commits.
- `gate.sh` line 33 is the portable comment. There is no `mktemp --suffix`, and `.gitignore` has `.gatecheck_*`.
- `lake build` rc 0. The gate gives PASS (71 / 50 / 101 / 93). Tamper gives `ALL TAMPERING TESTS REJECTED` in all four.
- Each copy is on `main...origin/main [ahead 1]`. The HEAD commits are unchanged: feuerbach `83d2486`, brahmagupta `ded0ff1`, miquel `9f99fbf`, malfatti `c0f16c5`. Each is authored by Josh Bald <jpbald93@gmail.com>. `git status --short` is empty, and there are no stash entries.
