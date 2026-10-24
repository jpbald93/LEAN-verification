# Layer 15, Paper F: classical comparer, Setting B (complete quadrangle)

Repository: `john:~/lean/l15_quadrangle`. Classical source: `~/lean/PaperFClassical.lean` (sha256 `afe16593f65ef05be32ba0cab87257fb82b0c76509eca6930fc2095d68441062`).
Scratch file: `scratch/L15_compare.lean` (1159 lines, sha256 `9fe754b0171c573f6a5576bd7b071ec6f6d3c313e9d395754c01e5b1795477f5`). It starts with `import QuadMiquel` / `import Mathlib`.

**Verbatim check (scripted).** These were copied character for character from the classical file, with the namespace renamed `ClassicalSource` → `L15CmpB`:
- the prelude (`Point` … `triangleSide`);
- every definition in `section CompleteQuadrangle`.

A script also confirms that each `cov_classical_X` statement is textually identical to `classical_X`, for all 10. The Setting-A definitions (quadrilateral/parabola) are not needed and were not copied.

## Summary table

| classical statement | class | Lean theorem(s) proving it | what the repository lacks | note |
|---|---|---|---|---|
| `classical_D1_a` (a common point of the 4 nine-point circles exists) | **E** | `cov_classical_D1_a` ← `l14_ninepoint_concur` (non-orthocentric), `l14_orthocentric_ninePointCircle_eq` + Mathlib `eulerPoint_mem_ninePointCircle` (orthocentric) | nothing | Orthocentric case is glue: the four circles are equal, and any point on them works. |
| `classical_D1_b` (unique if not orthocentric) | **E** | `cov_classical_D1_b` ← `l14_poncelet_on_ninepoint` | nothing | The classical `¬OrthocentricSystem` (∃ i) yields the repository's `d ≠ Tabc.orthocenter` at i = 3. |
| `classical_D1_c` (a rectangular conic centred at every common point passes through the 4 points; degenerate pair of lines allowed) | **O** → proved | `cov_classical_D1_c` ← `tpar_generic`, `tpar_orth`, `conic_core`, `d1c_of_tpar` (**NEW PROOF**) | The paper has no Lean theorem about the hyperbola; "centre of the rectangular hyperbola" appears only in the docstring of `poncelet` | Generic case: `l14b_P` identifies P with the repository's `poncelet` formula. A new ring identity in `pN`/`pD` then shows the vectors w²−2wP (w = vertex − d) are pairwise ℝ-parallel, which gives a unit u with all four points on Im((z−P)²ū²) = const. Orthocentric case: new `linear_combination` certificate (cofactors found with sympy/Gröbner) from the circumcircle relations and P on the nine-point circle. |
| `classical_D1_d` (proper hyperbola unless P is the meet of perpendicular opposite joins) | **O** → proved | `cov_classical_D1_d` ← `cov_classical_D1_c` + `degen_of_k0` (**NEW PROOF**) | as above | If k = 0, each point lies on one of the two perpendicular asymptotes through P. No three of the points are collinear, so it is exactly 2+2, which is the classical `IsDegenerateRectangularCenter`. The classical exclusion is shown to be exactly what is needed (k ≠ 0). |
| `classical_D2` (orthocentric ⇒ all 4 Mathlib nine-point circles are equal) | **E** | `cov_classical_D2` ← `l14_orthocentric_ninePointCircle_eq` via `orth_core` | nothing | Classical orthocentricity may sit at any index k; handled by relabelling (`setup_i`) plus the l14 bridge lemmas `l14b_tri_cases` and `l14b_ninePointCircle_eq_of_range_eq`. |
| `classical_D3_a` (∃! positive-radius pedal circle of `Q.points i` w.r.t. triangle i, and it passes through P) | **N** → gap closed | `cov_classical_D3_a` ← `l14_poncelet_on_pedal_d` (non-orthocentric) + `d3_cosph_orth`, `feet_ne`, `d3_of_cosph` (**NEW PROOF**) | (1) `l14_poncelet_on_pedal_*` assume the quadrangle is **not orthocentric**, but classical only excludes concyclic. (2) The repository gives only `Cospherical`: no positive radius, no uniqueness of the circle, and no distinctness of the feet. | NEW: in the orthocentric case the feet are the altitude feet (`foot_orth`), hence on the nine-point circle, which contains P. NEW: the three feet are pairwise distinct (`feet_ne`, via the repository's `eq_meet_of_foot_eq`), so they are affinely independent; that gives a positive radius and uniqueness through the circumsphere. `¬OnCircumcircle` is bridged to the repository's `¬Cospherical {a,b,c,d}` (`onCirc_of_cosph`). |
| `classical_D3_b` (same, as `Cospherical (range feet ∪ {P})`) | **N** → gap closed | `cov_classical_D3_b` ← `d3_cosph` (= `l14_poncelet_on_pedal_d` ∪ NEW orthocentric case) | the orthocentric case, as for D3_a | |
| `classical_D4` (P on the circumcircle of the diagonal triangle, opposite joins non-parallel) | **N** → gap closed | `cov_classical_D4` ← `l14_poncelet_on_diagonal_circle` (non-orthocentric) + NEW orthocentric branch | `l14_poncelet_on_diagonal_circle` assumes **not orthocentric**; the classical statement does not | NEW: in an orthocentric quadrangle the three diagonal points are the altitude feet of triangle p0p1p2 (`foot_mem_face`, `foot_mem_vertex_orth`, `l14b_diag`), so they lie on its nine-point circle with P. The `intersection` (ε-choice) is shown to be the repository's `diagPt` (`diagV_eq`, `meets`). |
| `classical_D5_a` (common-point predicate depends only on the point set) | **E** | `cov_classical_D5_a` ← `pall` (from `l14b_tri_cases`, `l14b_ninePointCircle_eq_of_range_eq`) | `l14_poncelet_S4` itself is stated under non-orthocentric | The classical version holds in all cases. The proof uses only the repository's l14b bridge lemmas, not the hypothesis, so it is covered. |
| `classical_D5_b` (single-valued, non-orthocentric) | **E** | `cov_classical_D5_b` ← `cov_classical_D1_b` + `cov_classical_D5_a` | nothing | |

No **D** (different) cases. In every case the classical statement and the repository agree where both apply. The repository is narrower only in excluding the orthocentric configuration (D3, D4) and in not stating D1_c/D1_d at all.

## NEW PROOFS (not in the repository)
1. `diagonal_triangle_independent` (construction obligation): see below.
2. `tpar_generic` / `gen_pair`: a ring identity showing the repository's `poncelet` formula is the centre of a rectangular conic through the 4 points.
3. `tpar_orth` (+ `orth_xy`, `orth_xz`, `orth_yz`, with explicit cofactors): the orthocentric analogue, for every point P of the common nine-point circle.
4. `conic_core`, `common_dir`, `unit_sqrt`, `dot_prod`: turn pairwise parallelism into a `RectangularConic`, giving D1_c.
5. `degen_of_k0`, `degen_of`, `col3`: k = 0 forces `IsDegenerateRectangularCenter`, giving D1_d.
6. `foot_orth`, `span_face`, `d3_cosph_orth`: D3 in the orthocentric case.
7. `foot_vertex`, `feet_ne`, `d3_of_cosph`: the pedal feet are distinct, which gives positive radius and uniqueness of the pedal circle.
8. `foot_mem_vertex_orth`, `foot_mem_face`, plus the orthocentric branch of `cov_classical_D4`: D4 in the orthocentric case.
9. `orth_all`: every point of an orthocentric quadrangle is the orthocentre of the other three. It is proved but not used in the final chain.

## Construction obligations
- `diagonal_triangle_independent`: **PROVED**. The statement is verbatim; the `sorry` is replaced by a proof, and `Quadrangle.diagonalTriangle` uses this proved theorem. The proof is `diag_ncol` (diagonal points of a `QGen` quadrangle with non-parallel opposite joins are not collinear), assembled from the repository's own `diag1C`–`diag3C`, `diagPt_frame` and `diagK`, with `diagV_eq` identifying the ε-chosen `intersection` with `diagPt`.
- `quadrilateral_triangle_independent` belongs to Setting A and is not needed here.
- No hypothesis was added to any `cov_` theorem.

## Compile, forbidden tokens, axioms
- `cd ~/lean/l15_quadrangle && ~/lean/jl lake env lean scratch/L15_compare.lean` → **exit 0**, no errors, no warnings. The output is only the `#print axioms` lines.
- Forbidden-token grep (`sorry|admit|native_decide|axiom|implemented_by|extern|opaque|unsafe`, excluding `#print axioms` lines): the only hit is line 45, the verbatim classical docstring "…does not read any external data." That is the word "external" matching `extern`, not a token.
- `#print axioms`: each of the 10 `cov_classical_*` and `diagonal_triangle_independent` depends on **[propext, Classical.choice, Quot.sound]** only (11/11).

## Library hash
`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`
- before: `5caf441740b0450729edbfc450d8e05e56244683b6ca42e64e81f72d73e96fda`
- after:  `5caf441740b0450729edbfc450d8e05e56244683b6ca42e64e81f72d73e96fda` (unchanged)

## Files
- `john:~/lean/l15_quadrangle/scratch/L15_compare.lean`: the only scratch file. Temporary test files `scratch/test_*.lean` were deleted.
- `john:~/lean/l15_quadrangle/L15_COMPARE_B.md`: this report.
- No library files were edited, no `lake update` or cache fetch was run, and no other repositories were touched.
