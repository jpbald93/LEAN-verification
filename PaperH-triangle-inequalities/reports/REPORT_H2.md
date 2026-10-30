# REPORT — Paper H, group H2: The Erdős–Mordell inequality and the Fermat–Torricelli point

Repository: `~/lean/paperh_mordell` on the arm64 machine (local git repo, no remote, nothing committed).
Library `ErdosMordell`; Lean v4.33.1; Mathlib as pinned in `lake-manifest.json`.

## Summary
| Item | Lean name | Proved | file:line |
|---|---|---|---|
| H2.1 Erdős–Mordell inequality | `ErdosMordell.erdos_mordell` | Y | ErdosMordell/Mordell.lean:179 |
| H2.1 equality case (stretch) | `ErdosMordell.erdos_mordell_eq_iff` | Y | ErdosMordell/Mordell.lean:386 |
| H2.2 key lemma at A | `ErdosMordell.key_lemma_zero` | Y | ErdosMordell/Mordell.lean:130 |
| H2.2 key lemma at B | `ErdosMordell.key_lemma_one` | Y | ErdosMordell/Mordell.lean:146 |
| H2.2 key lemma at C | `ErdosMordell.key_lemma_two` | Y | ErdosMordell/Mordell.lean:162 |
| H2.3 Barrow (stretch) | `ErdosMordell.barrow` | Y | ErdosMordell/Barrow.lean:283 |
| H2.4 minimality | `ErdosMordell.fermat_min` | Y | ErdosMordell/Fermat.lean:44 |
| H2.4 existence + minimality | `ErdosMordell.fermat_torricelli` | Y | ErdosMordell/Fermat.lean:291 |

Every main theorem and every lemma reports `depends on axioms: [propext, Classical.choice, Quot.sound]`.
No dimension hypothesis (`Fact (finrank ℝ V = 2)`) was needed anywhere.

H2.2 pairing (checked numerically before proving): `a·XA ≥ b·d_C(X) + c·d_B(X)`, where
`d_C` = distance to line AB, `d_B` = distance to line CA, `b = CA`, `c = AB`. The other pairing,
`b·d_B + c·d_C`, is false.

## Exact statements
### H2.2 key lemma (vertex A) — `ErdosMordell.key_lemma_zero`
Proved: **Y** — `ErdosMordell/Mordell.lean:130`
Axioms: `'ErdosMordell.key_lemma_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`
```lean
theorem key_lemma_zero (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    dist (t.points 2) (t.points 0) *
        dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P) +
      dist (t.points 0) (t.points 1) *
        dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) ≤
      dist (t.points 1) (t.points 2) * dist X (t.points 0)
```

### H2.2 key lemma (vertex B) — `ErdosMordell.key_lemma_one`
Proved: **Y** — `ErdosMordell/Mordell.lean:146`
Axioms: `'ErdosMordell.key_lemma_one' depends on axioms: [propext, Classical.choice, Quot.sound]`
```lean
theorem key_lemma_one (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    dist (t.points 0) (t.points 1) *
        dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) +
      dist (t.points 1) (t.points 2) *
        dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P) ≤
      dist (t.points 2) (t.points 0) * dist X (t.points 1)
```

### H2.2 key lemma (vertex C) — `ErdosMordell.key_lemma_two`
Proved: **Y** — `ErdosMordell/Mordell.lean:162`
Axioms: `'ErdosMordell.key_lemma_two' depends on axioms: [propext, Classical.choice, Quot.sound]`
```lean
theorem key_lemma_two (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    dist (t.points 1) (t.points 2) *
        dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) +
      dist (t.points 2) (t.points 0) *
        dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) ≤
      dist (t.points 0) (t.points 1) * dist X (t.points 2)
```

### H2.1 Erdős–Mordell inequality — `ErdosMordell.erdos_mordell`
Proved: **Y** — `ErdosMordell/Mordell.lean:179`
Axioms: `'ErdosMordell.erdos_mordell' depends on axioms: [propext, Classical.choice, Quot.sound]`
```lean
theorem erdos_mordell (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    2 * (dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) +
        dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) +
        dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P)) ≤
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)
```

### H2.1 equality case — `ErdosMordell.erdos_mordell_eq_iff`
Proved: **Y** — `ErdosMordell/Mordell.lean:386`
Axioms: `'ErdosMordell.erdos_mordell_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]`
```lean
theorem erdos_mordell_eq_iff (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    2 * (dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) +
        dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) +
        dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P)) =
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) ↔
    (dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
      dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)) ∧
    X = Finset.univ.centroid ℝ t.points
```

### H2.3 Barrow — `ErdosMordell.barrow`
Proved: **Y** — `ErdosMordell/Barrow.lean:283`
Axioms: `'ErdosMordell.barrow' depends on axioms: [propext, Classical.choice, Quot.sound]`
```lean
theorem barrow (t : Triangle ℝ P) (X U V' W : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w)
    (hU : Wbtw ℝ (t.points 1) U (t.points 2)) (hV : Wbtw ℝ (t.points 2) V' (t.points 0))
    (hW : Wbtw ℝ (t.points 0) W (t.points 1))
    (hUa : ∠ (t.points 1) X U = ∠ U X (t.points 2))
    (hVa : ∠ (t.points 2) X V' = ∠ V' X (t.points 0))
    (hWa : ∠ (t.points 0) X W = ∠ W X (t.points 1)) :
    2 * (dist X U + dist X V' + dist X W) ≤
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)
```

### H2.4 minimality — `ErdosMordell.fermat_min`
Proved: **Y** — `ErdosMordell/Fermat.lean:44`
Axioms: `'ErdosMordell.fermat_min' depends on axioms: [propext, Classical.choice, Quot.sound]`
```lean
theorem fermat_min (A B C F : P) (hAB : ∠ A F B = 2 * π / 3) (hBC : ∠ B F C = 2 * π / 3)
    (hCA : ∠ C F A = 2 * π / 3) (X : P) :
    dist F A + dist F B + dist F C ≤ dist X A + dist X B + dist X C
```

### H2.4 existence (auxiliary) — `ErdosMordell.fermat_exists`
Proved: **Y** — `ErdosMordell/Fermat.lean:163`
Axioms: `'ErdosMordell.fermat_exists' depends on axioms: [propext, Classical.choice, Quot.sound]`
```lean
theorem fermat_exists (t : Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) :
    ∃ F : P, ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧ ∠ (t.points 2) F (t.points 0) = 2 * π / 3
```

### H2.4 Fermat–Torricelli — `ErdosMordell.fermat_torricelli`
Proved: **Y** — `ErdosMordell/Fermat.lean:291`
Axioms: `'ErdosMordell.fermat_torricelli' depends on axioms: [propext, Classical.choice, Quot.sound]`
```lean
theorem fermat_torricelli (t : Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) :
    ∃ F : P, ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
      ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
      ∀ X : P, dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2) ≤
        dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)
```

## Open items
None. All statements, including the stretch goals (H2.1 equality, H2.3 Barrow), are proved.
No `ErdosMordell/Open.lean` was needed.

Notes on the formulation:
* H2.1 equality: "the centre" is taken to be Mathlib's `Finset.univ.centroid ℝ t.points`.
  For an equilateral triangle this coincides with the incentre and circumcentre.
  "Equilateral" is stated as `dist A B = dist B C ∧ dist B C = dist C A`.
* H2.3: "the bisector of ∠BXC meets BC at U" is stated as `Wbtw ℝ B U C ∧ ∠ B X U = ∠ U X C`;
  X is strictly inside (all weights `> 0`). On the boundary, X can coincide with a vertex and the
  angles degenerate.
* H2.4: existence uses an explicit point with weights `∝ 1/xᵢ`, `x_A = G + √3⟪B−A, C−A⟫`
  (cyclically, `G` = twice the area). Minimality holds over all X in the space.

## Obstacles met (all resolved; details in PROGRESS.md)
* `linear_combination` needed the unfolded `orthogonalProjection` form to match the hypotheses.
* `field_simp` sometimes closed goals itself, so a following `ring` failed with "no goals".
* Implicit-argument mis-unification in `eq_pos`; fixed by naming the arguments.
* Barrow: heartbeat timeouts in a monolithic `nlinarith` and the final assembly; fixed by
  splitting into scalar lemmas and avoiding `▸` casts.

## Verification
* Gate: `PASS (48 declarations, standard axioms only)`. REQUIRED covers every theorem, the
  definition `footDist`, and every bridge/auxiliary lemma (48 names, fully qualified).
* Tamper: `ALL TAMPERING TESTS REJECTED`. 7/7 rejected: sorry, ax2line, evalfake, macro → forbidden
  token; wrap → nonstandard axioms; falsehyp (in `erdos_mordell`, `0 ≤ w i` weakened to `w i = w i`)
  → FAIL: build; falsehyp_ext (`hCA` dropped from `fermat_min`) → FAIL: build.
* Library sources contain no `sorry`/`admit`/`native_decide`/`axiom`/`set_option`/`#eval`/`#print`/
  `macro`/`notation`/`run_cmd`.
* Total lines: 1185 Lean (Basic 116, Mordell 431, Fermat 306, Barrow 328, root 4).
* Numerics (mpmath, 30 digits): H2.1, H2.2 over 2000 random triangles incl. near-boundary points;
  Fermat point angles = 2π/3 to 1e-28, and a random local search found no better point; Barrow over 3000 random
  interior points. All polynomial identities were certified with sympy before being used in Lean.
