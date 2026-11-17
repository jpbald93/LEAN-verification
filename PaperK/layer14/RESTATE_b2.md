# RESTATE_b2 — Layer 14b repair (rows 7 and 8)

Host: john (`~/lean/l13_inversion`, Mathlib v4.33.1, warm cache). Everything was run one at a time; total Lean wall time was about 20 s, well inside the 3600 s budget.

Result: **8 of 8 rows compile. Nothing was dropped, and no statement changed.** All four errors were in the proofs, not in what the rows claim.

## Hashes

| file | sha256 (local = john) |
|---|---|
| input `paperK_l14b.lean` | `7afd0872e86cb447562e72c1644b0a931cdb0f9378e9758f395104e60f28287f` |
| deliverable `paperK_l14b_fix.lean` | `6f09e922ebd1f7ef74fad1d9e1d33ab94f7c8588a55eaac94e98512b1af87aa7` |

Locally I checked with `sha256sum`; on john with `shasum -a 256`. The two digests match.

## Rows

Verdict key (my reading of the letters): **E** = exact restatement of the source claim. **W** = Mathlib-vocabulary form that adds side hypotheses. **O** = goes beyond the source (a strengthening or correction). **N** = not stated.

| row | claim | verdict | how it was stated | what changed |
|---|---|---|---|---|
| 1 | `tangency_identity` | E | `−2 X₃Y₃·lieB X Y = (X₀Y₃ − Y₀X₃)² − dist(Y₃•cen X, X₃•cen Y)²` on the null cone, with no nonvanishing hypothesis. A normalised `sph` version is also given (needs X₃, Y₃ ≠ 0). | nothing |
| 2 | `B_eq_zero_iff_tangent` | E (+W) | `lieB X Y = 0 ↔ dist centres = abs(r_X − r_Y)`. There are two extra variants using Mathlib's `Sphere.IsIntTangent` / `IsExtTangent`, and these add sign hypotheses on the radii. | nothing |
| 3 | `mulVec_cofactor` | E (+O) | `M *ᵥ cofactor M = 0`, with `cofactor` written as signed `Matrix.det ∘ submatrix`. Also proved: the cofactor vector lies in `ker M.mulVecLin`, and it is nonzero when the rows are linearly independent. | nothing |
| 4 | `B_G_cofactor_row` | E | `(toLinearMap₂' ℝ G).IsOrtho (G *ᵥ cofactor M) (M i)`, plus versions for scalar multiples and for any kernel vector. | nothing. Note: `IsOrtho` is deprecated, which gives warnings only. |
| 5 | `prop31_cofactor` | E | `Collinear ℝ {pX (G *ᵥ cofactor M), pX A, pX A'}` in `EuclideanSpace ℝ (Fin 2)`, under the source's span hypothesis. | nothing |
| 6 | `explicit_power_indep` | E | The `Sphere.power`s of the four circles `⟨c i, ρ − r i⟩` at the explicit Cramer point are independent of `i` (given `det4 r a b 1 ≠ 0`). | nothing |
| 7 | `square_null_space` (+ kernel and rank) | E (+O) | Source form: `(∀ i, lieB P (circ 1 (sqc i)) = 0) ↔ P₁ = 0 ∧ P₂ = 0 ∧ P₄ = P₀ + P₃/2`. Mathlib form: `ker Msq.mulVecLin = span {v1, v2}`, `finrank ker = 2`, `Msq.rank = 3`, and the kernel is not the span of any single vector. | **proof only**, in `ker_Msq_not_span_singleton` (line 389 error). The `v = 0` branch was a `simp` that made no progress. Both cases are now handled together: `finrank_span_le_card` gives `finrank (span {v}) ≤ 1`, and `omega` closes it against `= 2`. |
| 8 | `equal_power_point_unique` (+ D3 / circumcentre bridge, coordinate form) | E (+O) | Mathlib form: for an `Affine.Triangle` `s`, equal `Sphere.power` (radius `ρ − r₀`) to the three vertex circles `↔ x = s.circumcenter`. Bridge 1: `D3 a b ≠ 0 ↔ AffineIndependent ℝ (tri a b)`. Bridge 2: the circumcentre equals `!₂[ccx, ccy]`. Source form: the coordinate statement, derived from the Mathlib statement. | **proofs only**: (a) line 430, `⟨rfl, rfl⟩` became `⟨trivial, trivial⟩`, because after `simp only` the goals are already `True`. (b) line 480: the coefficients of the `linear_combination` had the wrong sign; it is now `-(b 2 − b 0)·ha1 − (b 1 − b 0)·ha2`. (c) line 554: a trailing `simp` came after the goal was already closed by `rw`, so it was deleted. |

Note on where the errors were: the brief put both the `simp` and the `rfl` errors in row 7. In fact only line 389 is in row 7. Line 430 is in row 8's main theorem `equal_power_point_unique`, so rows 7 and 8 had one and three errors. The brief's conclusion still holds: all four errors were in rows 7–8.

The full diff from the input is four hunks: lines 387–391, 430, 480 and 554 of the original.

## Gate output (john)

```
$ cd ~/lean/l13_inversion
$ lake env lean scratch/paperK_l14b_fix.lean
compile rc=0          (0 errors; warnings only: deprecated IsOrtho, unused simp arg, seq-focus linter)
$ grep -nE 'sorry|admit|native_decide|axiom' scratch/paperK_l14b_fix.lean
grep rc=1             (no match)
```

`#print axioms` covered all 52 declarations. I ran it on a temporary copy, `scratch/_l14b_axcheck.lean` (the deliverable plus one `#print axioms` line per declaration), and deleted the copy afterwards. Its rc was 0. Every line is shown below:

```
'PaperKL14b.G' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.lieB' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.lieB_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.cen' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.pX' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.sph' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.circ' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.dist_sq2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.tangency_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.tangency_identity_sph' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.tangency_of_B_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.B_eq_zero_iff_tangent' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.B_eq_zero_iff_isIntTangent' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.B_eq_zero_iff_isExtTangent' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.cofactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.det_cons_eq_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.cofactor_mem_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.mulVec_cofactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.cofactor_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.lieB_G_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.B_G_ker_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.B_G_cofactor_row_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.B_G_cofactor_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.prop31' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.prop31_cofactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.det4' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.det4_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.row_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.explicit_power_sphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.explicit_power_indep' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.sqc' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.Msq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.Msq_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.square_null_space' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.mem_ker_Msq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.v1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.v2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.ker_Msq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.v1_v2_linearIndependent' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.finrank_ker_Msq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.rank_Msq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.ker_Msq_not_span_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.D3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.ccx' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.ccy' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.tri' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.equal_power_point_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.D3_ne_zero_iff_affineIndependent' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.cc_generic' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.triS' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.circumcenter_eq_cc' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14b.equal_power_point_unique_coords' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## git status

**This check does not meet the brief's wording.** The brief wants `git status --short` to show only `?? scratch/`. On john it shows nothing at all. The reason is that `scratch/` is listed in `.git/info/exclude` (line 7), so git ignores it rather than reporting it as untracked. `git status --short --ignored` shows `!! .lake/` and `!! scratch/` and nothing else. The tracked tree is clean: no `git add`, no commit, nothing changed outside `scratch/`.

On john, `scratch/` now contains `paperK_l14b.lean` (the input copy) and `paperK_l14b_fix.lean` (the deliverable). The axiom-check copy has been removed.

## Dropped / why

Nothing was dropped.

## Statement-level note (not a change)

Row 7 includes `ker_Msq_not_span_singleton`, which the input file's own docstring labels a "correction to the brief". The kernel of the square's four unit circles is 2-dimensional (rank 3, not 4). Anything quoting this row must say "2-dimensional kernel", not "1-dimensional".
