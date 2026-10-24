# BRIDGE_REPORT — QuadMiquel layer 10 (definition bridges)

New file: `QuadMiquel/Bridge.lean` (682 lines, `namespace QuadMiquel`, `import QuadMiquel.Simson`).
Root file `QuadMiquel.lean`: exactly one line appended at the end, `import QuadMiquel.Bridge`.
No existing library `.lean` file was edited. `gate.sh`: only its REQUIRED list was extended, with 19 new names.

## Result
* **Gate:** `PASS (51 declarations, standard axioms only)` (32 old + 19 new; every one uses only [propext, Classical.choice, Quot.sound]).
* **Tamper** (`~/lean/jl tamper`): sorry, ax2line, evalfake, macro → FAIL: forbidden token; wrap → FAIL: nonstandard axioms; falsehyp → FAIL: build. **ALL TAMPERING TESTS REJECTED**.

## Corrections and findings
* **M2 needed an extra hypothesis.** Under GenPos, H₃ = ortho T₃ and H₄ = ortho T₄ coincide **exactly when L₁ ⊥ L₂**. Both triangles then have their right angle at A₁₂, so H₃ = H₄ = A₁₂. This is proved as `ortho34_eq_iff`, and `steiner_parallel` (Simson.lean) uses exactly this pair. The sibling's example (L₁ = real axis, L₂ = imaginary axis, L₃ through 1 and i, L₄ through 2 and −2i) satisfies GenPos and gives H₃ = H₄ = 0 (checked numerically). So `line[H₄, H₃]` collapses to a point, and the Parallel statement is false there. It fails because a nondegenerate line can't be parallel to a point: `AffineSubspace.Parallel` requires equal directions. So `steiner_parallel_affine` adds `hperp : (conj L₁.d * L₂.d).re ≠ 0` (L₁ not perpendicular to L₂). By `ortho34_eq_iff` this is equivalent to H₃ ≠ H₄, so it is the minimal hypothesis. In numerical tests with L₂ forced perpendicular to L₁ (5 random cases), |H₃−H₄| < 1e-15 and |H₃−A₁₂| < 1e-15.
* **M1:** Under GenPos the Miquel point is **none of the six vertices** (`miquelPt_ne_vertices`). In particular M ≠ A₁₂, so the circumcircles of T₃ and T₄ are never tangent at A₁₂. Also, **A₁₂ is on neither of the circumcircles of T₁ and T₂** (`A12_not_on_circ`). In the normalised frame the power of A₁₂ with respect to circle T₁ is −|v|²t ≠ 0, and with respect to circle T₂ it is −|u|²s ≠ 0. The two centres O₄ and O₃ differ, and A₁₂ is not on the line O₄O₃ (`A12_not_mem_centres`: the cross product is a nonzero multiple of |u|²|v|²(s−t)). So both the reflection characterisation and uniqueness hold, with no extra hypothesis:
  - `miquelPt_spec`: M ≠ A₁₂, O₄ ≠ O₃, and M = `EuclideanGeometry.reflection (line[ℝ, O₄, O₃]) A₁₂`.
  - `miquelPt_unique`: any point on the circumcircles of T₄, T₃ and T₁ equals M. This is stronger than "on all four circles". It is proved with Mathlib's `eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`.
* **M3** is stronger than asked: all **six pairs of feet are distinct** (`simson_feet_ne`). If two feet coincide, M is the meet of the two lines (`eq_meet_of_foot_eq`), which contradicts `miquelPt_ne_vertices`.
* **B5** was proved in the **full Mathlib form**, `foot z L = ↑(EuclideanGeometry.orthogonalProjection line[ℝ, L.p, L.p + L.d] z)`, via `inter_eq_singleton_orthogonalProjection`. The characterisation `foot_mem` / `foot_perp` is also exported.
* **B6** is split in two: `genPos_triangles` (four non-collinear triangles) and `genPos_vertices_ne` (15 pairwise inequalities).
* **B7** was proved as a full **iff** (`genPos_iff`), in Mathlib terms: `AffineSubspace.Parallel` of the `line[ℝ, p, p+d]`s, plus "no common point of three carriers". Helper: `parallel_iff_cr`.
* **Degenerate inputs**, checked in Python and matching the hypotheses:
  - B1: if d = 0, the carrier is all of ℂ (`cr 0 _ = 0`) but `line[p, p] = {p}`, so `hd` is needed.
  - B2: if the lines are parallel, `meet` divides by 0.
  - B3/B4: for collinear points the `circ` denominator is 0 (example: 0, 1, 2), so the non-collinearity hypothesis is needed.

## Numerical checks (Python, `num/check.py`, `num/check2.py`; 20000 random GenPos configurations)
| check | worst error / smallest value |
|---|---|
| B1 points p + r d satisfy cr = 0 | 1.8e-15 |
| B2 meet lies on both lines | 7.3e-12 |
| B3 circ vs. linear-solve circumcentre (relative) | 7.6e-12 |
| B4 ortho vs. intersection of altitudes (relative) | 2.7e-11 |
| B5 foot vs. projection | 9.0e-15 |
| B6 smallest relative cross product of a triangle / smallest vertex separation | 6e-10 / 2e-5 (never 0) |
| M on all four circumcircles | 5.7e-6 (relative, from ill-conditioned samples) |
| M1 M = reflection of A₁₂ in O₄O₃ | 4.3e-7 |
| M ≠ each vertex; A₁₂ off circles T₁ and T₂; O₄ ≠ O₃ | minima > 1e-6, never 0; a Nelder–Mead search for tangency (M → A₁₂) only pushes the configuration toward degeneracy (ratio to the smallest vertex separation stays > 0) |
| M3 feet pairwise distinct | minimum 6e-7, never 0 |
| Steiner cr(F₂−F₁, H₃−H₄) | 2.2e-12 |
| H₃ ≠ H₄ in random configurations / forced L₁ ⊥ L₂ | minimum 3e-4 / < 1e-15 (counterexample, see above) |

Symbolic check (sympy) of M minus each vertex in the frame: these are the products of nonzero factors that the Lean proofs use, (s−1), (t−1), u, v, (u−v), (su−tv), each divided by D.

## Exact Lean statements
### B1: `QuadMiquel.carrier_eq_line` — QuadMiquel/Bridge.lean:28
```lean
theorem carrier_eq_line (L : Line) (hd : L.d ≠ 0) :
    L.carrier = (line[ℝ, L.p, L.p + L.d] : Set ℂ) := by
```

### B2: `QuadMiquel.meet_eq_iff` — QuadMiquel/Bridge.lean:35
```lean
theorem meet_eq_iff {L M : Line} (h : cr M.d L.d ≠ 0) (z : ℂ) :
    (z ∈ L.carrier ∧ z ∈ M.carrier) ↔ z = meet L M := by
```

### B3: `QuadMiquel.circ_eq_circumcenter` — QuadMiquel/Bridge.lean:94
```lean
theorem circ_eq_circumcenter {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    circ a b c =
      (⟨![a, b, c], affineIndependent_iff_not_collinear_set.2 h⟩ : Affine.Triangle ℝ ℂ).circumcenter := by
```

### B4: `QuadMiquel.ortho_eq_orthocenter` — QuadMiquel/Bridge.lean:118
```lean
theorem ortho_eq_orthocenter {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    ortho a b c = Affine.Triangle.orthocenter
      (⟨![a, b, c], affineIndependent_iff_not_collinear_set.2 h⟩ : Affine.Triangle ℝ ℂ) := by
```

### B5: `QuadMiquel.foot_eq_orthogonalProjection` — QuadMiquel/Bridge.lean:129
```lean
theorem foot_eq_orthogonalProjection (z : ℂ) (L : Line) (hd : L.d ≠ 0) :
    foot z L = (EuclideanGeometry.orthogonalProjection (line[ℝ, L.p, L.p + L.d]) z : ℂ) := by
```

### B6a: `QuadMiquel.genPos_triangles` — QuadMiquel/Bridge.lean:240
```lean
theorem genPos_triangles {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    ¬ Collinear ℝ ({meet L₁ L₂, meet L₁ L₃, meet L₂ L₃} : Set ℂ) ∧
    ¬ Collinear ℝ ({meet L₁ L₂, meet L₁ L₄, meet L₂ L₄} : Set ℂ) ∧
    ¬ Collinear ℝ ({meet L₁ L₃, meet L₁ L₄, meet L₃ L₄} : Set ℂ) ∧
    ¬ Collinear ℝ ({meet L₂ L₃, meet L₂ L₄, meet L₃ L₄} : Set ℂ) := by
```

### B6b: `QuadMiquel.genPos_vertices_ne` — QuadMiquel/Bridge.lean:201
```lean
theorem genPos_vertices_ne {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    meet L₁ L₂ ≠ meet L₁ L₃ ∧ meet L₁ L₂ ≠ meet L₁ L₄ ∧ meet L₁ L₂ ≠ meet L₂ L₃ ∧
    meet L₁ L₂ ≠ meet L₂ L₄ ∧ meet L₁ L₂ ≠ meet L₃ L₄ ∧
    meet L₁ L₃ ≠ meet L₁ L₄ ∧ meet L₁ L₃ ≠ meet L₂ L₃ ∧ meet L₁ L₃ ≠ meet L₂ L₄ ∧
    meet L₁ L₃ ≠ meet L₃ L₄ ∧
    meet L₁ L₄ ≠ meet L₂ L₃ ∧ meet L₁ L₄ ≠ meet L₂ L₄ ∧ meet L₁ L₄ ≠ meet L₃ L₄ ∧
    meet L₂ L₃ ≠ meet L₂ L₄ ∧ meet L₂ L₃ ≠ meet L₃ L₄ ∧ meet L₂ L₄ ≠ meet L₃ L₄ := by
```

### B7: `QuadMiquel.genPos_iff` — QuadMiquel/Bridge.lean:645
```lean
theorem genPos_iff (L₁ L₂ L₃ L₄ : Line) :
    GenPos L₁ L₂ L₃ L₄ ↔
      (L₁.d ≠ 0 ∧ L₂.d ≠ 0 ∧ L₃.d ≠ 0 ∧ L₄.d ≠ 0) ∧
      (¬ line[ℝ, L₁.p, L₁.p + L₁.d].Parallel line[ℝ, L₂.p, L₂.p + L₂.d] ∧
        ¬ line[ℝ, L₁.p, L₁.p + L₁.d].Parallel line[ℝ, L₃.p, L₃.p + L₃.d] ∧
        ¬ line[ℝ, L₁.p, L₁.p + L₁.d].Parallel line[ℝ, L₄.p, L₄.p + L₄.d] ∧
        ¬ line[ℝ, L₂.p, L₂.p + L₂.d].Parallel line[ℝ, L₃.p, L₃.p + L₃.d] ∧
        ¬ line[ℝ, L₂.p, L₂.p + L₂.d].Parallel line[ℝ, L₄.p, L₄.p + L₄.d] ∧
        ¬ line[ℝ, L₃.p, L₃.p + L₃.d].Parallel line[ℝ, L₄.p, L₄.p + L₄.d]) ∧
      (¬ ∃ z, z ∈ L₁.carrier ∧ z ∈ L₂.carrier ∧ z ∈ L₃.carrier) ∧
      (¬ ∃ z, z ∈ L₁.carrier ∧ z ∈ L₂.carrier ∧ z ∈ L₄.carrier) ∧
      (¬ ∃ z, z ∈ L₁.carrier ∧ z ∈ L₃.carrier ∧ z ∈ L₄.carrier) ∧
      (¬ ∃ z, z ∈ L₂.carrier ∧ z ∈ L₃.carrier ∧ z ∈ L₄.carrier) := by
```

### M1a: `QuadMiquel.miquelPt_spec` — QuadMiquel/Bridge.lean:468
```lean
theorem miquelPt_spec {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    miquelPt L₁ L₂ L₃ L₄ ≠ meet L₁ L₂ ∧
    circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ≠ circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄) ∧
    miquelPt L₁ L₂ L₃ L₄ = EuclideanGeometry.reflection
      (line[ℝ, circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃),
        circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄)]) (meet L₁ L₂) := by
```

### M1b: `QuadMiquel.miquelPt_unique` — QuadMiquel/Bridge.lean:496
```lean
theorem miquelPt_unique {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) {z : ℂ}
    (h4 : z ∈ Metric.sphere (circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃))
      (dist (meet L₁ L₂) (circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃))))
    (h3 : z ∈ Metric.sphere (circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄))
      (dist (meet L₁ L₂) (circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄))))
    (h1 : z ∈ Metric.sphere (circ (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄))
      (dist (meet L₂ L₃) (circ (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄)))) :
    z = miquelPt L₁ L₂ L₃ L₄ := by
```

### M1 aux: `QuadMiquel.miquelPt_ne_vertices` — QuadMiquel/Bridge.lean:365
```lean
theorem miquelPt_ne_vertices {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    miquelPt L₁ L₂ L₃ L₄ ≠ meet L₁ L₂ ∧ miquelPt L₁ L₂ L₃ L₄ ≠ meet L₁ L₃ ∧
    miquelPt L₁ L₂ L₃ L₄ ≠ meet L₁ L₄ ∧ miquelPt L₁ L₂ L₃ L₄ ≠ meet L₂ L₃ ∧
    miquelPt L₁ L₂ L₃ L₄ ≠ meet L₂ L₄ ∧ miquelPt L₁ L₂ L₃ L₄ ≠ meet L₃ L₄ := by
```

### M1 aux: `QuadMiquel.A12_not_on_circ` — QuadMiquel/Bridge.lean:401
```lean
theorem A12_not_on_circ {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    dist (meet L₁ L₂) (circ (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄)) ≠
        dist (meet L₂ L₃) (circ (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄)) ∧
      dist (meet L₁ L₂) (circ (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄)) ≠
        dist (meet L₁ L₃) (circ (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄)) := by
```

### M1 aux: `QuadMiquel.A12_not_mem_centres` — QuadMiquel/Bridge.lean:431
```lean
theorem A12_not_mem_centres {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ≠ circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄) ∧
    meet L₁ L₂ ∉ line[ℝ, circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃),
      circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄)] := by
```

### M2: `QuadMiquel.steiner_parallel_affine` — QuadMiquel/Bridge.lean:606
```lean
theorem steiner_parallel_affine {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄)
    (hperp : (conj L₁.d * L₂.d).re ≠ 0) :
    line[ℝ, foot (miquelPt L₁ L₂ L₃ L₄) L₁, foot (miquelPt L₁ L₂ L₃ L₄) L₂].Parallel
      line[ℝ, ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃),
        ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄)] := by
```

### M2 aux: `QuadMiquel.ortho34_eq_iff` — QuadMiquel/Bridge.lean:577
```lean
theorem ortho34_eq_iff {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄) = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ↔
      (conj L₁.d * L₂.d).re = 0 := by
```

### M3: `QuadMiquel.simson_feet_ne` — QuadMiquel/Bridge.lean:555
```lean
theorem simson_feet_ne {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    foot (miquelPt L₁ L₂ L₃ L₄) L₁ ≠ foot (miquelPt L₁ L₂ L₃ L₄) L₂ ∧
    foot (miquelPt L₁ L₂ L₃ L₄) L₁ ≠ foot (miquelPt L₁ L₂ L₃ L₄) L₃ ∧
    foot (miquelPt L₁ L₂ L₃ L₄) L₁ ≠ foot (miquelPt L₁ L₂ L₃ L₄) L₄ ∧
    foot (miquelPt L₁ L₂ L₃ L₄) L₂ ≠ foot (miquelPt L₁ L₂ L₃ L₄) L₃ ∧
    foot (miquelPt L₁ L₂ L₃ L₄) L₂ ≠ foot (miquelPt L₁ L₂ L₃ L₄) L₄ ∧
    foot (miquelPt L₁ L₂ L₃ L₄) L₃ ≠ foot (miquelPt L₁ L₂ L₃ L₄) L₄ := by
```

### B5 aux: `QuadMiquel.foot_mem` — QuadMiquel/Bridge.lean:520
```lean
theorem foot_mem (z : ℂ) (L : Line) : foot z L ∈ L.carrier := by
```

### B5 aux: `QuadMiquel.foot_perp` — QuadMiquel/Bridge.lean:524
```lean
theorem foot_perp (z : ℂ) (L : Line) (hd : L.d ≠ 0) : (conj L.d * (z - foot z L)).re = 0 := by
```

## Hashes (shasum -a 256)
Before:
```
95b548bc2ee7b7c87bbaa7ff03c74cf3722ce41ad2a26d634d9cf97101b47938  QuadMiquel/Algebra.lean
f7b4da7d2abf6c1f66b987defd25bf99be4bf10a6cf081c97af51dd1f52dcf12  QuadMiquel/Basic.lean
1e7cbfc90348e6884806654ff0c60085c6b3d807a6c2dec15aa7d3e126703fc8  QuadMiquel/Frame.lean
5ce67f6891f4ec1c36c4ff6f1a789f076bef4fa567a579f63c03d7efa9f785a5  QuadMiquel/Miquel.lean
69b49c142ec7435ebfbea2fb2851f66a20c96fbdb9e48be3e67ecc0fae2936ce  QuadMiquel/Simson.lean
e7cd79fd2fce9554bf33a507a020b51d7cb0d5118f841d2da143498eb07b5dac  QuadMiquel.lean
5e02cb3a58df711eab7a0d0e2f4cb47a3f11243936d20d000d4bdfa330b1243a  gate.sh
```
After:
```
95b548bc2ee7b7c87bbaa7ff03c74cf3722ce41ad2a26d634d9cf97101b47938  QuadMiquel/Algebra.lean   (unchanged)
f7b4da7d2abf6c1f66b987defd25bf99be4bf10a6cf081c97af51dd1f52dcf12  QuadMiquel/Basic.lean     (unchanged)
1e7cbfc90348e6884806654ff0c60085c6b3d807a6c2dec15aa7d3e126703fc8  QuadMiquel/Frame.lean     (unchanged)
5ce67f6891f4ec1c36c4ff6f1a789f076bef4fa567a579f63c03d7efa9f785a5  QuadMiquel/Miquel.lean    (unchanged)
69b49c142ec7435ebfbea2fb2851f66a20c96fbdb9e48be3e67ecc0fae2936ce  QuadMiquel/Simson.lean    (unchanged)
fb6f3e39230d5279dee671a62c70748ed1969d32df77815ba49f3145b68b29fa  QuadMiquel/Bridge.lean    (new)
0863878da234cad198cbf8b9a10a569d1de1e95bae538a561f23719b8e7aa887  QuadMiquel.lean           (+1 line: import QuadMiquel.Bridge)
890b78b689af6a1c6e8b63e3b774b90282e19de9ac9b36627d91ccec0816d5f3  gate.sh                   (REQUIRED extended)
```
