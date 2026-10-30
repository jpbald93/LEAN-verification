# Layer 13 — Comparer M, Paper H (blind_28 … blind_50)

Blind file: PaperHBlind.lean, sha256 `e257c271479a928f78fd921fe07747d30285031439fe2241e8125a20a8f08cbc`. I checked the copy on the VM and the copy on the arm64 machine (`~/lean/reformalH/PaperHBlind.lean`); they are identical. The Blind definitions (lines 10–81) are copied verbatim into each scratch file inside `namespace L13Blind`, and `diff` against the original shows no change. Each `blindK_stmt` is the blind binders, hypotheses and conclusion copied by script, with the ambient `variable`s turned into explicit `∀` binders at universes `u v`. The real side is always `type_of% @Repo.decl.{u, v}`.

No proof body uses a repository main theorem. Each proof uses only the premise, the agreement lemmas, unfolding, and general Mathlib (`sbtw_map_iff`, `lineMap_injective`, `angle_neg_right`, …).

## Result table

| pair | R→B | B→R | difference | note |
|---|---|---|---|---|
| 28 ↔ `FermatNapoleon.ptolemy_eq_iff` | ✔ `rb_28` | ✔ `br_28` | none | The collinear case is written differently on each side. Blind gives 8 explicit pairs of `Sbtw` chains; the repo gives `(Sbtw A B C ∨ Sbtw A D C) ∧ (Sbtw B A D ∨ Sbtw B C D)`. `agree_orders` shows they agree for distinct collinear points, by transporting along `lineMap A C` and doing a case split on the real line. A brute-force check over all 24 orderings also found 0 mismatches. The cospherical branch is syntactically identical. The `-- AMBIGUOUS` reading turned out to match the repo. |
| 29 ↔ `ErdosMordell.key_lemma_zero` | ✔ | ✔ | none | `BlindDistToLine` is definitionally the repo projection distance; `BlindInClosedTriangle` is the repo barycentric hypothesis (`Iff.rfl`). |
| 30 ↔ `key_lemma_one` | ✔ | ✔ | none | same |
| 31 ↔ `key_lemma_two` | ✔ | ✔ | none | same |
| 32 ↔ `erdos_mordell` | ✔ | ✔ | none | same |
| 33 ↔ `erdos_mordell_eq_iff` | ✔ | ✔ | none | Plus `BlindEquilateral` = the repo's conjunction (`Iff.rfl`). The centroid is the same term on both sides. |
| 34 ↔ `ErdosMordell.barrow` | ✔ | ✔ | none | `BlindStrictlyInside` = the repo's positive-weights hypothesis. The `-- AMBIGUOUS` bisector rendering (`∠BXU = ∠UXC` etc.) is literally what the repo uses. |
| 35 ↔ `ErdosMordell.fermat_min` | ✔ | ✔ | none | Identical up to hypothesis names. |
| 36 ↔ `ErdosMordell.fermat_torricelli` | ✔ | ✔ | none | Identical. Against `fermat_exists` alone, blind_36 → fermat_exists is a plain weakening (`b36_to_exists`, proved). The converse would need the minimality claim, so the right pairing is `fermat_torricelli`, not `fermat_exists`. |
| 37 ↔ `apex_outward` (i=0) | ✔ `rb_37` | ✔ jointly | none | The repo quantifies over `i : Fin 3`. |
| 38 ↔ `apex_outward` (i=1) | ✔ `rb_38` | ✔ jointly | none | `br_37_38_39 : b37 ∧ b38 ∧ b39 → apex_outward` (`fin_cases`). |
| 39 ↔ `apex_outward` (i=2) | ✔ `rb_39` | ✔ jointly | none | The `-- AMBIGUOUS` reading "strictly opposite sides" is exactly the repo's `SOppSide`. |
| 40 ↔ `napoleon_dist_eq`.1 | ✔ | ✔ jointly | none | `br_40_41 : b40 ∧ b41 → napoleon_dist_eq` |
| 41 ↔ `napoleon_dist_eq`.2 | ✔ | ✔ jointly | none | |
| 42 ↔ `napoleon_concurrent` | ✔ | ✔ | none | Apex agreement only. |
| 43 ↔ `napoleon_fermat` (angles) | ✔ | ✔ jointly | none | `br_43_44 : b43 ∧ b44 → napoleon_fermat`. The hypotheses match exactly: angles < 2π/3, F on AA′ and BB′. |
| 44 ↔ `napoleon_fermat` (length) | ✔ | ✔ jointly | none | |
| 45 ↔ `napoleon_angle`.1 | ✔ | ✔ jointly | none | `br_45_46_47`. The repo has a 4th conjunct, `angle(A′−A, B−B′) = π/3`. It follows from blind_45 by Mathlib `angle_neg_right` (a vector sign flip, which counts as repackaging). |
| 46 ↔ `napoleon_angle`.2 | ✔ | ✔ jointly | none | |
| 47 ↔ `napoleon_angle`.3 | ✔ | ✔ jointly | none | The `-- AMBIGUOUS` alternative (line angle π/3) is in fact the repo's 4th conjunct; both are covered. |
| 48 ↔ `napoleon`.1 | ✔ | ✔ jointly | none | `br_48_49_50` |
| 49 ↔ `napoleon`.2 | ✔ | ✔ jointly | none | |
| 50 ↔ `napoleon`.3 | ✔ | ✔ jointly | none | `t.centroid` is the abbrev for `Finset.univ.centroid ℝ t.points` (`agree_centroid`, rfl). |

**Summary:** for all 23 blind statements (28–50), both directions are proved. There are no REAL, no ARTEFACT, and no SAFE (Lean-more-general) differences. Several statements only map back jointly because the paper statement was split across them: {37,38,39}, {40,41}, {43,44}, {45,46,47}, {48,49,50}. Each blind statement follows individually from its repo theorem, and the conjunction of the group implies the repo theorem.

All the pairings given in the brief are correct. The only refinement is for blind_36: `fermat_torricelli` is the exact match, while `fermat_exists` is strictly weaker.

## Agreement lemmas (all proved, in the scratch files)
Mordell file:
- `agree_distToLine` (`BlindDistToLine = ErdosMordell.footDist`, rfl)
- `agree_distToLine'` (equals the projection form used in the theorems, rfl)
- `agree_closed`, `agree_inside` (barycentric hypotheses, `Iff.rfl`)
- `agree_equilateral` (`Iff.rfl`)

Fermat file:
- `agree_sign` (`BlindOrientationSign = triSign`, rfl)
- `agree_outerApex` (unfold + `mul_div_assoc`: `σ*π/3` vs `σ*(π/3)`)
- `agree_apexA/B/C` (`= napoleonApex o t 0/1/2`)
- `agree_centerA/B/C` (`= napoleonCenter o t 0/1/2`)
- `agree_centroid` (rfl)
- `agree_orders_real` and `agree_orders` (the Ptolemy collinear order conditions; uses repo definition-level bridge `FermatNapoleon.sbtw_real` plus Mathlib)

L14 files were not needed.

## Compile
On arm64 machine, `lake env lean scratch/L13_compare.lean`:
- `~/lean/l14h_mordell/scratch/L13_compare.lean`: **exit 0**. Only unused-variable linter warnings.
- `~/lean/l14h_fermat/scratch/L13_compare.lean`: **exit 0**. Only linter warnings.
  - The work copy was made by the prescribed tar pipeline from x86-64 machine. `lake build` finished with exit 0 (8713 jobs).

Scratch file sha256:
- mordell: `f2104f35cac4c1f3f4960c9ee28527981d8ca614d03b27341c69770209fd478b`
- fermat: `058ae71476af82d34b80989b826512f9e06e20801cbc4a10165d5d9152d10c27`

`scratch/` was added to `.git/info/exclude` in both copies, and `git status --short` is empty in both.

## Forbidden-token grep
`grep -n "sorry|admit|native_decide|axiom"` on both scratch files, excluding the `#print axioms` lines: **empty**.

## #print axioms
All 39 printed theorems depend on exactly `[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`.
- Mordell file (17): rb_29..36, br_29..36, b36_to_exists
- Fermat file (22): rb_28, br_28, rb_37/38/39, br_37_38_39, rb_40/41, br_40_41, rb_42, br_42, rb_43/44, br_43_44, rb_45/46/47, br_45_46_47, rb_48/49/50, br_48_49_50

The full output is in `layer13/L13M_scratch/axioms.txt`.

## Library hashes
Command: `find . -name "*.lean" -not -path "./.lake/*" -not -path "./scratch/*" | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`

| repo | before | after |
|---|---|---|
| l14h_mordell | 27ee1da8922b79b2df940148796f936a0de302700b7a1b87766b6d08f3806f90 | 27ee1da8922b79b2df940148796f936a0de302700b7a1b87766b6d08f3806f90 |
| l14h_fermat | b2ff757811152592568729c62c233d19817c7d265a8a2a3da794b5c7ea2ce1fd | b2ff757811152592568729c62c233d19817c7d265a8a2a3da794b5c7ea2ce1fd |

The hashes are unchanged; no library file was edited.

## Scratch paths
- arm64 machine:~/lean/l14h_mordell/scratch/L13_compare.lean (import ErdosMordell; pairs 29–36)
- arm64 machine:~/lean/l14h_fermat/scratch/L13_compare.lean (import FermatNapoleon; pairs 28, 37–50)
- Local copies: <paper-dir>/layer13/L13M_scratch/{L13_compare_mordell.lean, L13_compare_fermat.lean, axioms.txt}

DONE
