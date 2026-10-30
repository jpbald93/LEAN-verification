# Layer 15 — Classical comparer, Paper H (agent M)

Assigned: classical_P2, M1a, M1b, M2, F1a, F1b, F2a, F2b, F2c, F2d, F3.
Classical source: PaperHClassical.lean, sha256 `0ac73f94ec9efdb8e9d6337980d6e2ec8cc2521083c2026968373dd7d85eceb7`
(the local copy and arm64 machine `~/lean/reformalH/PaperHClassical.lean` hashes match).

The classical definitions block (everything from `variable {V P …}` up to `/-! ## E1–E12 -/`) and each assigned
statement are copied verbatim into namespace `L15CompareM`. Only two changes were made: `theorem classical_X` became `theorem cov_X`, and
`by sorry` was replaced by a proof. A script checked that each copied statement and the definitions block appear
character-for-character in the scratch files.

## Results

| classical | E/N/D/O | cov_ theorem(s) | what is missing / NEW PROOF | note |
|---|---|---|---|---|
| P2 (Ptolemy eq. + converse) | **E** | `cov_P2` | Nothing is missing. The bridge lemmas are NEW PROOF: `coplanar_of_cross`, `sbtw_of_concyclic`, `real_order_iff`, `col_iff`. | Uses `FermatNapoleon.ptolemy_eq_iff`. The two right-hand sides have different shapes. Repository: `Cospherical ∧ ∃X, Sbtw A X C ∧ Sbtw B X D` or `Collinear ∧ (Sbtw ABC ∨ Sbtw ADC) ∧ (Sbtw BAD ∨ Sbtw BCD)`. Classical: `Concyclic ∧ ∃X, Wbtw A X C ∧ Wbtw B X D` or `Collinear ∧ (Sbtw ABC ↔ ¬Sbtw ADC)`. For four distinct points they are equivalent. Crossing diagonals give coplanarity. On a sphere, three distinct points are not collinear, so weak crossing is strict. The collinear order conditions are compared on ℝ by case split, then transported along `lineMap A C`. |
| M1a (Erdős–Mordell) | **E** | `cov_M1a` | — | `ErdosMordell.erdos_mordell` plus Mathlib's `dist_orthogonalProjection_eq_infDist`. The definitions `ClassicalInsideOrOn` and `ClassicalDistToLine` unfold to exactly the repository's hypothesis and quantity. |
| M1b (equality case) | **E** | `cov_M1b` | — | `ErdosMordell.erdos_mordell_eq_iff`. The equality is written the other way round, and the repository's `c=a ∧ a=b` is reordered to the classical `a=b ∧ b=c`. Includes boundary points X (closed triangle), just like the repository. |
| M2 (Barrow) | **E** | `cov_M2` | — | `ErdosMordell.barrow`. The hypotheses are identical; only the conjunctions are split. |
| F1a (Fermat–Torricelli, ∃ + min) | **E** | `cov_F1a` | — | `ErdosMordell.fermat_torricelli`. The three angle conjuncts are permuted. |
| F1b (any 120° point is a minimiser) | **E** | `cov_F1b` | — | `ErdosMordell.fermat_min`. The repository result is stronger: it needs no `< 120°` hypothesis and no triangle, so the classical `h` is unused. |
| F2a (AA′ = BB′ = CC′) | **E** | `cov_F2a` | NEW PROOF bridge `apex_eq` / `classical_apexes`: an apex defined the classical way is exactly the repository's `napoleonApex o t i`, for the orientation `o` induced by any basis. | Uses `FermatNapoleon.napoleon_dist_eq`. The bridge argument: \|A′B\| = \|A′C\| = \|BC\| forces the area form ω(d, A′−B) = ±(√3/2)\|d\|². The wrong sign would put A′ on the same side as A. This contradicts `SOppSide` via the repository's `apex_outward` and `sOppSide_of_areaForm`. With the right sign, the repository's `decomp` pins A′ down. |
| F2b (concurrence) | **E** | `cov_F2b` | Same bridge (NEW PROOF). | `FermatNapoleon.napoleon_concurrent`. |
| F2c (meet at Fermat point, AA′ = FA+FB+FC) | **E** | `cov_F2c` | NEW PROOF `fermat_unique` (uniqueness of the 120° point), plus the apex bridge. | The repository's `napoleon_fermat` points the other way: it takes F on lines AA′ and BB′ and concludes the 120° angles and AA′ = ΣFX. The classical statement takes F with the 120° angles and asks that F lies on the lines. So I take the concurrence point F₀ (`napoleon_concurrent`), show it is a 120° point (`napoleon_fermat`), and conclude F = F₀ by uniqueness. The uniqueness proof: unit vectors at mutual 120° sum to 0, then equality in Cauchy–Schwarz. Valid in any real inner product space. |
| F2d (lines meet at 60°) | **E** | `cov_F2d` | Same bridge (NEW PROOF). | `FermatNapoleon.napoleon_angle`. The repository proves the vector angle is exactly 2π/3 for all three pairs, which is stronger. The classical "π/3 ∨ 2π/3" is closed by its right disjunct. |
| F3 (Napoleon) | **E** | `cov_F3` | Same bridge (NEW PROOF). | `FermatNapoleon.napoleon`. `napoleonCenter` unfolds definitionally to the classical `Finset.univ.centroid ℝ ![B, C, A′]`, and `t.centroid` is an abbreviation for `ClassicalCentroid t`. |

Summary: all 11 are E (COVERED); none is N, D or O. For P2 and F2a–F3, the agreement depends on the NEW PROOF bridge lemmas above. These translate between definitions only (the classical apex/order notions versus the repository's), plus Fermat-point uniqueness for F2c. They are not part of the repository.

## Build / checks (arm64 machine, `lake env lean scratch/L15_compare.lean`)

| repo | scratch file | lean exit | errors | forbidden grep (sorry/admit/native_decide/axiom) |
|---|---|---|---|---|
| `~/lean/l14h_mordell` | `scratch/L15_compare.lean` (sha256 `0adffac9…ecf7`) | 0 | 0 | 0 hits |
| `~/lean/l14h_fermat` | `scratch/L15_compare.lean` (sha256 `7f909fcd…0148`) | 0 | 0 | 0 hits |

The only remaining output is linter warnings: an unused variable `h` in `cov_F1b`, and unused simp arguments in `real_order_iff`.

### #print axioms
```
'L15CompareM.cov_M1a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_M1b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_M2' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_F1a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_F1b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_P2' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_F2a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_F2b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_F2c' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_F2d' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareM.cov_F3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Library hashes
Each hash is the sha256 of the sorted per-file `shasum -a 256` list over the library dir, the root `.lean`, lakefile, toolchain and manifest:
- l14h_mordell (ErdosMordell): before `b1e2a13458625b1153c866dd0f621e86bbedc4a449f3c9454d7fbc37dcac1618`, after `b1e2a13458625b1153c866dd0f621e86bbedc4a449f3c9454d7fbc37dcac1618` (unchanged). `git status --short` is empty.
- l14h_fermat (FermatNapoleon): before `d2ae07e639aaccbe8ebada1321d8cc103cf6c6c2391605f66402962a764af12b`, after the same value (unchanged). `git status --short` is empty.
  This work copy was created and built by the L13 agent (build log `~/lean/l14h_fermat_build.log`, "EXIT 0"). I did not rebuild it. Its "before" hash was taken right before my first compile.
- `scratch/` is listed in `.git/info/exclude` in both repos. No library files were edited. No `lake update` or `cache get` was run. No processes were killed.

## Scratch paths
- arm64 machine: `~/lean/l14h_mordell/scratch/L15_compare.lean`, `~/lean/l14h_fermat/scratch/L15_compare.lean`.
- local copies: `<paper-dir>/layer15/L15M/L15_compare_mordell.lean`, `…/L15M/L15_compare_fermat.lean`.
- generator and working files: `<work-dir>`.

DONE
