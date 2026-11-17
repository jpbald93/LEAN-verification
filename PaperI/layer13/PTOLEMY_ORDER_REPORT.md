# PTOLEMY_ORDER_REPORT — L15 item I2b, direction (⇒)

File: `~/lean/l13_inversion/scratch/ptolemy_order.lean` (namespace `PtolemyOrder`, imports `Inversion`).
No library file was edited. No `sorry` / `admit` / `axiom` / `native_decide` / `set_option`.

## Status

**Both alternatives are proved, so the whole equivalence is closed.** I2b is no longer "narrower":
`classical_I2b` below has exactly the statement of `PaperIClassical.classical_I2b`. That
statement carries the pairwise-distinct hypotheses already marked EXTRA HYPOTHESIS there.

## Exact statements

```lean
local notation "E2" => EuclideanSpace ℝ (Fin 2)

-- verbatim copy of the classical definition
def ClassicalLineCyclicOrder (A B C D : E2) : Prop :=
  (Sbtw ℝ A B C ∧ Sbtw ℝ B C D) ∨ (Sbtw ℝ B C D ∧ Sbtw ℝ C D A) ∨
    (Sbtw ℝ C D A ∧ Sbtw ℝ D A B) ∨ (Sbtw ℝ D A B ∧ Sbtw ℝ A B C)

/-- I2b, direction (⇒) — the missing one. -/
theorem classical_I2b_mp (A B C D : E2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (heq : dist A B * dist C D + dist B C * dist D A = dist A C * dist B D) :
    (Cospherical ({A, B, C, D} : Set E2) ∧ ∃ X : E2, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
      ClassicalLineCyclicOrder A B C D

/-- I2b, direction (⇐) — same proof as `cov_classical_I2b_mpr` in scratch/L15_compare.lean. -/
theorem classical_I2b_mpr (A B C D : E2) :
    ((Cospherical ({A, B, C, D} : Set E2) ∧ ∃ X : E2, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
        ClassicalLineCyclicOrder A B C D) →
      dist A B * dist C D + dist B C * dist D A = dist A C * dist B D

/-- I2b, full equivalence; same statement as PaperIClassical.classical_I2b. -/
theorem classical_I2b (A B C D : E2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    dist A B * dist C D + dist B C * dist D A = dist A C * dist B D ↔
      (Cospherical ({A, B, C, D} : Set E2) ∧ ∃ X : E2, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
        ClassicalLineCyclicOrder A B C D
```

Helper lemmas in the file: `inner2`, `normsq2` (coordinates in `E2`); `eq_smul_of_cross`
(zero cross product ⇒ `y = k • x`); `real_order` (four distinct reals with
`(a-b)(b-c)(c-d)(d-a) < 0` are monotone in one of the 8 rotations/reflections of `a,b,c,d`);
`sbtw_param` (monotone parameters on `B + t•a` ⇒ `Sbtw`); `norm_sq_convex`;
`invPt_one_injective`; `core`; `line_cyclic`; `ptolemy_eq_of_sbtw`.

## Proof outline (⇒)

1. Translate so that `B = 0`: `a = A-B`, `c = C-B`, `d = D-B`.
2. Invert at `B` with `R = 1`. `Inversion.ptolemy_iff_dist_add_dist_invPt` turns the equality into
   `|a'd'| + |d'c'| = |a'c'|`, and `dist_add_dist_eq_iff` then gives `Wbtw ℝ a' d' c'`.
   So `d' = (1-t)a' + t c'`, and `0 < t < 1` because the points are distinct.
3. `core`: undo the inversion. This gives `d = α a + β c` with
   `α = ‖d‖²(1-t)/‖a‖² > 0` and `β = ‖d‖² t/‖c‖² > 0`, so `‖d‖² = α‖a‖² + β‖c‖²`.
   The identity `‖(1-t)x+ty‖² = (1-t)‖x‖² + t‖y‖² − t(1-t)‖x-y‖²` with `a' ≠ c'` gives `α + β > 1`.
4. If `0, a, c` are not collinear (cross product ≠ 0), the concyclic case holds:
   - Circle: an explicit circumcentre `K` (coordinates) satisfies `⟪p,K⟫ = ‖p‖²/2` for
     `p = a, c`, and by linearity also for `d`. So `A, B, C, D` lie on the sphere with centre
     `B + K` and radius `‖K‖`.
   - Diagonals cross: `X = B + (α+β)⁻¹ • d`. We have `(α+β)⁻¹•d = lineMap a c (β/(α+β))`, so
     `Sbtw A X C`. We also have `(α+β)⁻¹•d = lineMap 0 d (α+β)⁻¹` with `(α+β)⁻¹ ∈ (0,1)`, so
     `Sbtw B X D`. Both use `sbtw_lineMap_iff`.
5. If `0, a, c` are collinear, the collinear case holds. Then `c = s•a` and `d = r•a` with
   `r = α + βs`. Eliminating `α, β` gives `s = r(s(1-t)+t)`, and so
   `s(s-r)(r-1) = r² t(1-t)(s-1)² > 0`. This is `(1-0)(0-s)(s-r)(r-1) < 0` for the line
   parameters `1, 0, s, r` of `A, B, C, D`. `real_order` gives one of 8 monotone orders, and
   `line_cyclic`/`sbtw_param` turn each one into the matching disjunct of
   `ClassicalLineCyclicOrder`.

The inverse-image circle criterion was not needed as a separate lemma. In the concyclic case,
step 3's identity `‖d‖² = α‖a‖² + β‖c‖²` puts `d` on the circle through `0, a, c` directly.

## Lemmas used

From the repository (`Inversion`): `ptolemy_iff_dist_add_dist_invPt`, `invPt`,
`norm_sq_invPt`, `invPt_invPt`.

From Mathlib:
- Betweenness: `dist_add_dist_eq_iff`, `sbtw_lineMap_iff`, `sbtw_const_add_iff`,
  `Sbtw.symm`, `Wbtw.trans_expand_left`, `Sbtw.angle₁₂₃_eq_pi`.
- Affine maps: `AffineMap.lineMap_apply_module`, `AffineMap.lineMap_apply_module'`.
- Ptolemy for cospherical points (⇐ direction only): `mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`.
- Inner products and norms: `norm_add_sq_real`, `norm_sub_sq_real`, `real_inner_smul_left`,
  `real_inner_smul_right`, `inner_add_left`, `norm_smul`, `PiLp.inner_apply`,
  `EuclideanSpace.real_norm_sq_eq`, `sq_eq_sq₀`.
- Distances: `dist_add_left`, `dist_self_add_left`.
- Arithmetic: `inv_lt_one_of_one_lt₀`, `div_lt_one`, plus the tactics
  `field_simp` / `linear_combination` / `nlinarith` / `positivity`.
- Definition: `Cospherical` (an explicit centre and radius are given).

## Compile output

```
$ ssh john@100.101.160.66 'cd ~/lean/l13_inversion && PATH=$HOME/.elan/bin:$PATH lake env lean scratch/ptolemy_order.lean; echo "exit=$?"'
'PtolemyOrder.classical_I2b_mp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PtolemyOrder.classical_I2b' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

No errors and no warnings. Only the standard axioms are used.

## What remains

Nothing for I2b in the scratch file. Optional follow-ups:
- Move `classical_I2b` into `scratch/L15_compare.lean` next to `cov_classical_I2b_mpr` (and/or a
  library file plus the gate's REQUIRED list). Then the Layer-15 row for I2b can change from
  **narrower** to **equivalent**.
  Note: `ClassicalLineCyclicOrder` is redefined here inside `PtolemyOrder`, with the same text as
  `L15CmpInversion.ClassicalLineCyclicOrder`. When it is merged, the copy should be dropped in
  favour of the existing definition.
- The theorem is stated for `EuclideanSpace ℝ (Fin 2)`, as in the classical statement. It uses
  coordinates for the circumcentre and the collinearity test, so it does not generalise to
  arbitrary inner-product spaces as written.
