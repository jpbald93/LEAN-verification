# REPORT — Paper G, Group B: the symmedian point and the Brocard points

Library `Brocard` (Lean v4.33.1, Mathlib v4.33.1). Files: `Brocard/Basic.lean` (definitions),
`Brocard/Lemmas.lean` (coordinate machinery and bridges), `Brocard/Main.lean` (theorems).
No `Brocard/Open.lean`: nothing is left open.

## Summary
- Every requested statement is proved: B1 (6 angle equalities plus interior), B2, B3(i), and both
  forms of B3(ii).
- The optional items are proved too: the converse of B2, B3(iii) `0 < ω ≤ π/6`, and the second
  Brocard point with its mirrored angle equalities.
- **Brocard weight order:** the scout's claim is correct. A 30-digit mpmath check on random
  triangles shows that weights proportional to `(1/b², 1/c², 1/a²)` give `∠ΩAB = ∠ΩBC = ∠ΩCA`.
  The other order `(1/c², 1/a², 1/b²)` gives `Ω'` with `∠Ω'BA = ∠Ω'CB = ∠Ω'AC`.
- **Area:** `area t := (1/2) * dist A B * dist A C * Real.sin (∠ B A C)`, as specified. Two bridges
  are proved: `Brocard.area_eq_sqrt` (Gram / cross-product form `½√(|u|²|v|² − ⟪u,v⟫²)`) and
  `Brocard.area_eq_sqrt_dist` (Heron form in `a², b², c²`).
- **Hypotheses:** only the B2 converse uses `[Fact (Module.finrank ℝ V = 2)]`. It is needed there
  so that every point `X` lies in the plane of the triangle. All other results hold in any
  dimension, so they carry no finrank hypothesis. The non-degeneracy of the triangle comes from
  `t : Affine.Triangle` (affine independence).

## Definitions (`Brocard/Basic.lean`)
| Name | Line |
|---|---|
| `Affine.Triangle.symmedianWeights` | 18 |
| `Affine.Triangle.symmedianPoint` | 25 |
| `Affine.Triangle.brocardWeights₁` | 30 |
| `Affine.Triangle.brocardPoint₁` | 37 |
| `Affine.Triangle.brocardWeights₂` | 42 |
| `Affine.Triangle.brocardPoint₂` | 49 |
| `Affine.Triangle.area` | 53 |

## Theorems

### B1 symmedian angle equalities (6) — `Brocard.symmedian_angles`
- Proved: **Y**
- Location: `Brocard/Main.lean:22`
- Axioms: `'Brocard.symmedian_angles' depends on axioms: [propext, Classical.choice, Quot.sound]`

```lean
theorem symmedian_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let K := t.symmedianPoint
    ∠ B A K = ∠ (midpoint ℝ B C) A C ∧ ∠ C A K = ∠ (midpoint ℝ B C) A B ∧
    ∠ C B K = ∠ (midpoint ℝ C A) B A ∧ ∠ A B K = ∠ (midpoint ℝ C A) B C ∧
    ∠ A C K = ∠ (midpoint ℝ A B) C B ∧ ∠ B C K = ∠ (midpoint ℝ A B) C A
```

### B1 K interior — `Brocard.symmedianPoint_mem_interior`
- Proved: **Y**
- Location: `Brocard/Main.lean:100`
- Axioms: `'Brocard.symmedianPoint_mem_interior' depends on axioms: [propext, Classical.choice, Quot.sound]`

```lean
theorem symmedianPoint_mem_interior (t : Affine.Triangle ℝ P) :
    ∃ w : Fin 3 → ℝ, ∑ i, w i = 1 ∧ (∀ i, 0 < w i) ∧
      t.symmedianPoint = Finset.univ.affineCombination ℝ t.points w
```

### B2 pedal centroid — `Brocard.symmedianPoint_eq_centroid_pedal`
- Proved: **Y**
- Location: `Brocard/Main.lean:115`
- Axioms: `'Brocard.symmedianPoint_eq_centroid_pedal' depends on axioms: [propext, Classical.choice, Quot.sound]`

```lean
theorem symmedianPoint_eq_centroid_pedal (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let K := t.symmedianPoint
    Finset.univ.centroid ℝ ![(orthogonalProjection line[ℝ, B, C] K : P),
      (orthogonalProjection line[ℝ, C, A] K : P), (orthogonalProjection line[ℝ, A, B] K : P)] = K
```

### B2 converse (optional) — `Brocard.eq_symmedianPoint_of_eq_centroid_pedal`
- Proved: **Y**
- Location: `Brocard/Main.lean:150`
- Axioms: `'Brocard.eq_symmedianPoint_of_eq_centroid_pedal' depends on axioms: [propext, Classical.choice, Quot.sound]`

```lean
theorem eq_symmedianPoint_of_eq_centroid_pedal [Fact (Module.finrank ℝ V = 2)]
    (t : Affine.Triangle ℝ P) (X : P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    Finset.univ.centroid ℝ ![(orthogonalProjection line[ℝ, B, C] X : P),
      (orthogonalProjection line[ℝ, C, A] X : P), (orthogonalProjection line[ℝ, A, B] X : P)] = X →
    X = t.symmedianPoint
```

### B3(i) Brocard angle equalities — `Brocard.brocardPoint₁_angles`
- Proved: **Y**
- Location: `Brocard/Main.lean:233`
- Axioms: `'Brocard.brocardPoint₁_angles' depends on axioms: [propext, Classical.choice, Quot.sound]`

```lean
theorem brocardPoint₁_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let Ω := t.brocardPoint₁
    ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A
```

### second Brocard point (optional) — `Brocard.brocardPoint₂_angles`
- Proved: **Y**
- Location: `Brocard/Main.lean:280`
- Axioms: `'Brocard.brocardPoint₂_angles' depends on axioms: [propext, Classical.choice, Quot.sound]`

```lean
theorem brocardPoint₂_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let Ω' := t.brocardPoint₂
    ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C
```

### B3(ii) cot ω = Σ cot — `Brocard.cot_brocardAngle_eq_sum_cot`
- Proved: **Y**
- Location: `Brocard/Main.lean:327`
- Axioms: `'Brocard.cot_brocardAngle_eq_sum_cot' depends on axioms: [propext, Classical.choice, Quot.sound]`

```lean
theorem cot_brocardAngle_eq_sum_cot (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let Ω := t.brocardPoint₁
    Real.cot (∠ Ω A B) = Real.cot (∠ B A C) + Real.cot (∠ A B C) + Real.cot (∠ A C B)
```

### B3(ii) cot ω = (a²+b²+c²)/(4Δ) — `Brocard.cot_brocardAngle_eq_div_area`
- Proved: **Y**
- Location: `Brocard/Main.lean:366`
- Axioms: `'Brocard.cot_brocardAngle_eq_div_area' depends on axioms: [propext, Classical.choice, Quot.sound]`

```lean
theorem cot_brocardAngle_eq_div_area (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let Ω := t.brocardPoint₁
    Real.cot (∠ Ω A B) = (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (4 * t.area)
```

### B3(iii) 0 < ω ≤ π/6 (optional) — `Brocard.brocardAngle_pos_le`
- Proved: **Y**
- Location: `Brocard/Main.lean:402`
- Axioms: `'Brocard.brocardAngle_pos_le' depends on axioms: [propext, Classical.choice, Quot.sound]`

```lean
theorem brocardAngle_pos_le (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1
    let Ω := t.brocardPoint₁
    0 < ∠ Ω A B ∧ ∠ Ω A B ≤ Real.pi / 6
```

## Bridge lemmas (`Brocard/Lemmas.lean`, all proved and in REQUIRED)
`symmedianPoint_vsub` (248), `brocardPoint₁_vsub` (264), `brocardPoint₂_vsub` (286),
`sum_symmedianWeights` (237), `orthogonalProjection_vsub` (308: Mathlib's `orthogonalProjection`
onto `line[ℝ,Y,Z]` equals the explicit foot), `centroid_vsub` (330: Mathlib's `Finset.centroid`),
`affineCombination_vsub` (135), `area_eq_sqrt` (201), `area_eq_sqrt_dist` (209),
`angle_eq_of_coords` (89), `angle_eq_angle_of_inner` (69), `cot_angle_coords` (122),
`cot_angle_eq_inner` (117), `inner_uu`/`inner_vv`/`inner_uv` (153/157/161: the Gram entries
`c², b², (b²+c²−a²)/2`), `gram_det_pos` (186), `gram`, `inner_comb`, `gram_pos`, `gram_det`,
`midpoint_vsub_coords`.

**Method:** each angle equality becomes "equal squared cosines and nonnegative product of the
cosines' numerators". For the sign condition, the product of the inner products is shown equal to
an explicit square-times-positive expression, found with sympy. These certificates, and the foot
parameters `s = (a²−b²+3c²)/(2S)` etc., were found with sympy and checked numerically with mpmath
before the Lean proofs were written. The closing step everywhere is `field_simp; ring`; the B2
converse uses `linear_combination` with explicit cofactors.

## Open items
None.

## Gate
`PASS (38 declarations, standard axioms only)`. REQUIRED covers all 7 definitions, all 9 theorems
and 22 bridge/helper lemmas.

## Tamper
```
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: Brocard.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
`falsehyp` deletes `[Fact (Module.finrank ℝ V = 2)]` from
`Brocard.eq_symmedianPoint_of_eq_centroid_pedal`.

## Size
Lean source lines: `Brocard.lean` 3 + `Basic.lean` 57 + `Lemmas.lean` 338 + `Main.lean` 463 = **861**.
