# Paper E — Layer 15 classical comparer (pilot)

Classical source: `~/reformal/PaperEClassical.lean`. sha256 `8e1e634a8ee183990c7d556a8a0fd2a756eef40eeb31f1ddf92ee35070b59c53`, matching the expected prefix 8e1e634a8ee18399. The file was not modified.
Repositories: `~/l15E_newton` (commit 48e94cf, namespace QuadNewton) and `~/l15E_miquel` (commit 011c9ec, namespace QuadMiquel).
Split: E1–E4 are compared in QuadNewton and E5–E8 in QuadMiquel. Newton–Gauss and Bodenmiller exist only in QuadNewton. QuadMiquel has its own orthocentre collinearity and non-collapse theorems (`orthocentres_collinear'`, `orthocentres_not_all_eq'`), which E8 uses.

## Method
Each scratch file is built mechanically by `gen/build.py`, which copies the classical file and makes four kinds of change:
- It swaps `import Mathlib` for `import QuadNewton` or `import QuadMiquel`.
- It inserts a bridge block after `carrier`. The block maps classical line `i` to a repository line `rl i = ⟨anchorA i, anchorB i - anchorA i⟩` and proves `GenPos (rl 0) (rl 1) (rl 2) (rl 3)` from `nonparallel` and `noTriple` via the repository's `genPos_iff`.
- It replaces the two `sorry`s of the construction obligations with real proofs.
- It replaces the block of `classical_*` theorems with the `cov_*` theorems.

`gen/verify.py` checks two things:
1. Removing the inserted blocks gives back the classical definitions region exactly.
2. Every `cov_X` statement, after normalising whitespace, is identical to `classical_X`. Result: **VERBATIM for all 12 classical statements.**

Classical index `i` corresponds to repository line `L_{i+1}`. The classical `triangle i` omits line `i`, which is the repository's T_{i+1}.

## Table

| classical statement | class | Lean theorem(s) | what is missing from the repo | note |
|---|---|---|---|---|
| E1_a Newton–Gauss collinear | **E** | `cov_E1_a` ← `newton_gauss` | — | `midpoint ℝ a b = (a+b)/2` bridge |
| E1_b midpoints not all equal | **E** | `cov_E1_b` ← `diag_midpoints_ne` | — | |
| E2_a orthocentres collinear | **E** | `cov_E2_a` ← `orthocentres_collinear` + `ortho_eq_orthocenter` | — | classical orthocentre is Mathlib's `Affine.Triangle.orthocenter` |
| E2_b orthocentres not all equal | **E** | `cov_E2_b` ← `orthocentres_not_all_eq` | — | |
| E3_a equal power wrt the 3 diameter circles | **E** | `cov_E3_a` ← `bodenmiller` (`pw` = classical `power` of `diameterCircle`) | — | |
| E3_b a line is the exact radical locus of every pair | **N → fully proved with a NEW PROOF** | `cov_E3_b` | The repo gives equal powers at the orthocentres and pairwise distinct centres (`bodenmiller_coaxal`). It never states that the equal-power set **equals** a line. | NEW lemma `radical_eq_line`: two circles with distinct centres whose radical locus contains H ≠ H' have radical locus exactly line[H,H'] (real-coordinate algebra). Goes beyond the paper's stated claim, but follows cheaply from it. |
| E4_a Newton–Gauss and orthocentre lines exist and are perpendicular | **E** (with glue) | `cov_E4_a` ← `newton_gauss`, `diag_midpoints_ne`, `orthocentres_collinear`, `orthocentres_not_all_eq`, `orthocentre_line_perp_inner` | Nothing mathematical. The repo states perpendicularity as `inner (m₂−m₁) (H₂−H₁)=0` for orthocentres, not as `AffineSubspace` lines with the `Perpendicular` property. | The carrier lines are `line[m₀,m₁]` and `line[Hᵢ,Hⱼ]`. Membership uses `Collinear.mem_affineSpan_of_mem_of_ne`; perpendicularity of every pair of direction vectors comes from `vectorSpan_pair`. |
| E5_a a Miquel point exists (∃) | **E** | `cov_E5_a` ← `miquel` | — | **The stronger ∃! reading is also covered:** `cov_E5_a_unique` ← `miquelPt_unique`. |
| E6_a circumcentres and any Miquel point are cospherical | **E** | `cov_E6_a` ← `steiner_circle` | — | "Any Miquel point" reduces to `miquelPt` by uniqueness (`eq_miquelPt`). |
| E7_a feet of a Miquel point are collinear | **E** | `cov_E7_a` ← `simson` + `foot_eq_orthogonalProjection` | — | classical `foot` is Mathlib's `orthogonalProjection` onto `carrier i` |
| E7_b feet not all equal, for **any** M | **N → fully proved with a NEW PROOF** | `cov_E7_b_part` (M a Miquel point ← `simson_feet_ne`, which gives pairwise distinct feet, a stronger property); `cov_E7_b` (full statement) | The repo proves distinct feet only for the Miquel point. The classical statement covers arbitrary M. | NEW proof: a common foot would lie on lines 0, 1 and 2, which contradicts `noTriple`. This uses no repository theorem. |
| E8_a Simson and orthocentre lines exist and are parallel (Mathlib `Parallel`) | **E** | `cov_E8_a` ← `steiner_parallel_line`, `simson_feet_ne`, `orthocentres_collinear'`, `orthocentres_not_all_eq'`, `miquelPt_unique` | — | The repo proves the line through the Simson feet parallel to `affineSpan` of all four orthocentres, with **no perpendicularity side condition**, so `steiner_parallel_affine`'s `L₁ ⊥̸ L₂` hypothesis is not needed. **Strictly parallel (distinct lines) is NOT proved by the repo** and I did not attempt it. Mathlib's `Parallel` allows the two lines to coincide, and that weaker form is what is covered. |

No statement is **D** (different). The only statement that strictly goes beyond the paper's claims is E7_b for a non-Miquel point M, which could count as **O**; I classified it N because the paper does prove the Miquel-point case.

## NEW PROOFS (comparer-written, beyond the repositories)
- `radical_eq_line` and the elementary lemma `cross_iff_dot`: an exact radical locus is a line (used for E3_b).
- `cov_E7_b`: noncollapse of the feet for arbitrary M, from `noTriple`.
- Glue, not new mathematics: the configuration bridge (`rl`, `genPos`, `vertex_eq`, `tv0..tv3`), the identification of circumcircle, circumcentre, orthocentre and foot with the repository definitions, and the classical Miquel predicate ⇔ the repository's four sphere memberships.

## Construction obligations
Both are **PROVED**, in both scratch files, with no hypotheses added:
- `Configuration.vertex_exists_unique`: witness `meet (rl i) (rl j)`, via `meet_eq_iff`, `carrier_eq_line` and `parallel_iff_cr` with `nonparallel`.
- `Configuration.triangle_independent`: via `genPos_triangles` (non-collinearity) and `affineIndependent_iff_not_collinear_set`.

## Compile / checks
- `cd ~/l15E_newton && lake env lean scratch/L15_compare.lean`: **exit 0**, 0 errors (only linter warnings).
- `cd ~/l15E_miquel && lake env lean scratch/L15_compare.lean`: **exit 0**, 0 errors.
- Forbidden-token grep (`sorry|admit|native_decide|axiom|sorryAx`, excluding `#print axioms` lines): **0 hits** in both files.
- `#print axioms`: 9 in each file. All 18 report exactly `[propext, Classical.choice, Quot.sound]`; no other axiom lists.
  - Newton file: vertex_exists_unique, triangle_independent, cov_E1_a, cov_E1_b, cov_E2_a, cov_E2_b, cov_E3_a, cov_E3_b, cov_E4_a.
  - Miquel file: vertex_exists_unique, triangle_independent, cov_E5_a, cov_E5_a_unique, cov_E6_a, cov_E7_a, cov_E7_b_part, cov_E7_b, cov_E8_a.

## Library hashes (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs sha256sum | sha256sum`)
- l15E_newton: before `b9e7fd2a70ac294e0d882e6536117b71cfbef4dea301a31836ef838494da751d`, after the same. **Unchanged.**
- l15E_miquel: before `6d8896a0d9412b802c6652a3f1fd894ad25fbab727ea5a729ca07dd9c6f945e8`, after the same. **Unchanged.**
- PaperEClassical.lean: sha256 unchanged (8e1e634a…59c53).

## Scratch paths
- `~/l15E_newton/scratch/L15_compare.lean` (sha256 d73e7364…3c1b) and `~/l15E_newton/scratch/L15_out.txt`
- `~/l15E_miquel/scratch/L15_compare.lean` (sha256 08255320…cd6b) and `~/l15E_miquel/scratch/L15_out.txt`
- The generator pieces (`build.py`, `verify.py`, A/V/B/T/tail fragments) are on the comparer host under `pilotE/l15c/gen/`.

## Wall time
Started 18:43:44 EDT and finished 19:12:45 EDT: **about 29 minutes**. No background tasks or subagents were used. No `lake update` or `cache get` was run, and no processes were killed. The battery directories were not touched.
