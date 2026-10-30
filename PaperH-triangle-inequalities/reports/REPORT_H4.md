# REPORT — Paper H, group H4: Ptolemy equality and the Fermat–Napoleon configuration

Repository: `paperh_fermat` (library `FermatNapoleon`), 1102 Lean lines in total
(Basic 44, Lemmas 81, Bridges 346, Ptolemy 352, Main 274, root 5). Nothing is committed (per the brief).

## Prior art (re-checked in the pinned Mathlib)
* Ptolemy's inequality: `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist` (Inversion/Basic.lean).
* Equality for cospherical points with crossing diagonals:
  `EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical` (Sphere/Ptolemy.lean).
* Not in Mathlib: the converse/characterisation, Napoleon's theorem, the Fermat–Napoleon lines.
  (Grep of Mathlib for "napoleon"/"ptolemy" finds only those two files.)

## Numerical sanity (mpmath, 30 digits; scripts numerics.py, sym*.py)
* Collinear Ptolemy equality holds exactly for the orders ABCD, ADCB, BADC, BCDA, CBAD, CDAB, DABC,
  DCBA. Equivalently: (B or D strictly between A and C) and (A or C strictly between B and D).
  This was checked on all 24 orders and on 2000 random collinear quadruples.
* Concyclic points in cyclic order give equality; points in non-separated order give strict inequality.
* Napoleon/Fermat: AA' = BB' = CC'; the explicit F lies on all three lines; the angles are 2π/3 when all
  triangle angles are < 2π/3; AA' = FA + FB + FC; the angles between the directions are 2π/3; the Napoleon
  triangle is equilateral and has centroid G (500 random triangles).

## Definitions (FermatNapoleon/Basic.lean)
* `triSign o t` (:29): 1 if ω(B−A, C−A) > 0, otherwise −1.
* `outerApex o t X Y` (:33): `o.rotation (−triSign·π/3) (Y −ᵥ X) +ᵥ X`.
* `napoleonApex o t i` (:37): `outerApex o t (t.points (i+1)) (t.points (i+2))`.
* `napoleonCenter o t i` (:41): `Finset.univ.centroid ℝ ![t.points (i+1), t.points (i+2), napoleonApex o t i]`.

## Theorems
Every one below is **proved**. Axioms line for each: `[propext, Classical.choice, Quot.sound]`.

### H4.1 — `FermatNapoleon.ptolemy_eq_iff` (FermatNapoleon/Ptolemy.lean:238) — proved (full iff)
```lean
theorem ptolemy_eq_iff {A B C D : P} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) :
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D ↔
      (Cospherical ({A, B, C, D} : Set P) ∧ ∃ X : P, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
      (Collinear ℝ ({A, B, C, D} : Set P) ∧
        (Sbtw ℝ A B C ∨ Sbtw ℝ A D C) ∧ (Sbtw ℝ B A D ∨ Sbtw ℝ B C D))
```
This holds in any real inner product space; no dimension hypothesis is needed. Supporting results:
`ptolemy_real` (:51, four reals: `|a−c||b−d| = |a−b||c−d| + |b−c||a−d| ↔ (Sbtw a b c ∨ Sbtw a d c) ∧ (Sbtw b a d ∨ Sbtw b c d)`)
and `ptolemy_collinear` (:71, the same statement for collinear points).

### H4.2 (planar: `[Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))`, `t : Affine.Triangle ℝ P`)
* `FermatNapoleon.apex_outward` (Main.lean:20) — proved:
  `(line[ℝ, t.points (i + 1), t.points (i + 2)]).SOppSide (t.points i) (napoleonApex o t i)`.
* (i) `FermatNapoleon.napoleon_dist_eq` (Main.lean:63) — proved:
  `dist A A' = dist B B' ∧ dist B B' = dist C C'` (written with `t.points i` and `napoleonApex o t i`).
* (ii) `FermatNapoleon.napoleon_concurrent` (Main.lean:99) — proved:
  `∃ F, F ∈ line[ℝ, A, A'] ∧ F ∈ line[ℝ, B, B'] ∧ F ∈ line[ℝ, C, C']`.
* (iii) `FermatNapoleon.napoleon_fermat` (Main.lean:111) — proved:
  hypotheses `∠ B A C < 2π/3`, `∠ C B A < 2π/3`, `∠ A C B < 2π/3`, `F ∈ line[ℝ, A, A']`, `F ∈ line[ℝ, B, B']`.
  Conclusion: `∠ A F B = 2π/3 ∧ ∠ B F C = 2π/3 ∧ ∠ C F A = 2π/3 ∧ dist A A' = dist F A + dist F B + dist F C`.
  This holds for *any* point on the two lines, so it applies to the common point of (ii).
  The explicit point is given by `fermat_point_spec` (Main.lean:72).

### H4.3 — `FermatNapoleon.napoleon` (Main.lean:222) — proved
`dist N₀ N₁ = dist N₁ N₂ ∧ dist N₁ N₂ = dist N₂ N₀ ∧ Finset.univ.centroid ℝ ![N₀, N₁, N₂] = t.centroid`,
where `Nᵢ = napoleonCenter o t i`. This came cheaply: the centres differ by (uᵢ − uⱼ)/3, and the uᵢ have a known Gram matrix.

### H4.4 (stretch) — `FermatNapoleon.napoleon_angle` (Main.lean:258) — proved
`angle (A'−A) (B'−B) = 2π/3`, `angle (B'−B) (C'−C) = 2π/3`, `angle (C'−C) (A'−A) = 2π/3`, and
`angle (A'−A) (B − B') = π/3`. So the lines make the angle π/3.

## Bridges (all proved; all in gate REQUIRED)
`decomp`, `cramer`, `triSign_mul_pos`, `triSign_sq`, `outerApex_vsub` (rotation = ½v ∓ (√3/2)Jv),
`napoleonApex_zero/one/two`, `gram_pos`, `areaForm_smul_J_left/right`.
`apex_frame` writes A', B', C' in the frame p = B−A, q = C−A, using α > 0 with 4α²(b²c²−k²) = 3.
Also `apex_inner`, `apex_sum`, `napoleonCenter_vsub` (centroid bridge), `fermat_frame`, and
`sOppSide_of_areaForm` (Bridges.lean). Helper lemmas are in Lemmas.lean; some are adapted with attribution from the
Erdős–Mordell repository.

## Open items
None. No `Open.lean` was needed.

## Gate
`bash gate.sh` → `PASS (47 declarations, standard axioms only)`
(REQUIRED = all 4 definitions, all bridge and helper lemmas, all theorems, fully qualified.)

## Tamper
`bash tests/tamper.sh` → `ALL TAMPERING TESTS REJECTED`
(sorry, ax2line, evalfake, macro → forbidden token; wrap → nonstandard axioms;
falsehyp = drop `hA` from `napoleon_fermat`, falsehyp2 = drop `hFB` from `napoleon_fermat`,
falsehyp3 = drop `hAB` from `ptolemy_eq_iff`, falsestmt = π/3 → π/4 in `napoleon_angle` → each FAIL: build).
