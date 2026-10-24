# BRIDGE_REPORT — QuadNewton layer 10 (definition bridges)

New file: `QuadNewton/Bridge.lean` (367 lines, namespace `QuadNewton`, `import QuadNewton.Quad`).
Root file `QuadNewton.lean`: one line `import QuadNewton.Bridge` appended at the end. No existing library .lean file was edited.

## Summary
| Bridge | Lean name | Line | Numeric check | Hypothesis change |
|---|---|---|---|---|
| B1 | carrier_eq_line | Bridge.lean:25 | OK (16 000 random checks with d≠0, incl. points forced onto the line); FALSE for d=0 (4 000/4 000) | none: the specified `hd` is needed and is enough |
| B2 | meet_eq_iff | Bridge.lean:39 | OK (random inputs; forced parallel inputs are excluded by `h`) | none |
| B3 | circ_eq_circumcenter | Bridge.lean:124 | OK (equidistance; forced collinear inputs excluded) | none |
| B4 | ortho_eq_orthocenter | Bridge.lean:140 | OK (altitude conditions) | none |
| B5 | foot_eq_orthogonalProjection | Bridge.lean:152 | OK (on line + perpendicular; d=0 excluded by `hd`) | none. The **full Mathlib `EuclideanGeometry.orthogonalProjection` form** is proved, not the fallback characterisation |
| B6 | genPos_triangles | Bridge.lean:174 | OK (13 333 GenPos samples; forced concurrent samples correctly fail GenPos) | none |
| B7 | genPos_iff (+ parallel_iff_cr) | Bridge.lean:334 (303) | OK: 0 mismatches over 95 121 integer-grid samples (34 108 of them non-GenPos: parallel/concurrent) | full iff proved |
| N1 | pw_eq_power | Bridge.lean:232 | OK (incl. P=Q) | none |
| N2 | bodenmiller_coaxal | Bridge.lean:243 | OK: the three centres are pairwise distinct in every sample | strengthened: pairwise distinct (not just "not all equal") |
| N3 | perp_iff_inner (+ orthocentre_line_perp_inner) | Bridge.lean:283 (287) | OK | none. Mathlib has `inner ℝ w z = (z * conj w).re` (`Complex.inner`, rfl); the iff holds for (a, b) as stated (the form is symmetric anyway) |

Extra helper theorem, also in REQUIRED: `collinear_iff_cr` (Bridge.lean:60): `Collinear ℝ {a,b,c} ↔ cr (b-a) (c-a) = 0`.

### Notes / counterexamples
* B1 without `hd`: for L.d = 0, `L.carrier = {z | cr 0 _ = 0} = ℂ` but `line[ℝ, p, p] = {p}`. The requested statement already has `hd`, so nothing needed correcting.
* No requested statement was false as written; all are proved in the specified form.
* B4: proved from Mathlib's `Affine.Triangle.orthocenter_vsub_circumcenter_eq_sum_vsub` (H − O = Σ(Aᵢ − O)) plus B3, which gives `ortho = a+b+c−2·circ` directly. B3 uses `Affine.Simplex.eq_circumcenter_of_dist_eq` (affine span = ⊤ via finrank ℝ ℂ = 2).
* B6: the six vertices' distinctness is stated as `List.Pairwise (· ≠ ·) [A₁₂, A₁₃, A₁₄, A₂₃, A₂₄, A₃₄]`.
* N2: `diamCircle P Q := ⟨(P+Q)/2, dist P Q / 2⟩` (Bridge.lean:238) is exactly the sphere in N1. The power equalities are `bodenmiller` rewritten through N1. Distinctness of centres: 1-vs-2 is `diag_midpoints_ne`; 1-vs-3 and 2-vs-3 are new.
* B7: Mathlib's `∥` notation is scoped, so the statement uses `AffineSubspace.Parallel` directly; `Line.toAffine L := line[ℝ, L.p, L.p + L.d]` (Bridge.lean:300). "No three through a point" is `¬ ∃ z, z ∈ Lᵢ ∧ z ∈ Lⱼ ∧ z ∈ Lₖ` for the four triples.

## Exact statements

Bridge.lean:25
```lean
theorem carrier_eq_line (L : Line) (hd : L.d ≠ 0) :
    L.carrier = (line[ℝ, L.p, L.p + L.d] : Set ℂ) := by
```

Bridge.lean:39
```lean
theorem meet_eq_iff {L M : Line} (h : cr M.d L.d ≠ 0) (z : ℂ) :
    (z ∈ L.carrier ∧ z ∈ M.carrier) ↔ z = meet L M := by
```

Bridge.lean:60
```lean
theorem collinear_iff_cr (a b c : ℂ) :
    Collinear ℝ ({a, b, c} : Set ℂ) ↔ cr (b - a) (c - a) = 0 := by
```

Bridge.lean:124
```lean
theorem circ_eq_circumcenter {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    circ a b c = (⟨![a, b, c], affineIndependent_iff_not_collinear_set.2 h⟩ :
      Affine.Triangle ℝ ℂ).circumcenter := by
```

Bridge.lean:140
```lean
theorem ortho_eq_orthocenter {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    ortho a b c = Affine.Triangle.orthocenter (⟨![a, b, c],
      affineIndependent_iff_not_collinear_set.2 h⟩ : Affine.Triangle ℝ ℂ) := by
```

Bridge.lean:152
```lean
theorem foot_eq_orthogonalProjection (z : ℂ) (L : Line) (hd : L.d ≠ 0) :
    foot z L = (EuclideanGeometry.orthogonalProjection (line[ℝ, L.p, L.p + L.d]) z : ℂ) := by
```

Bridge.lean:174
```lean
theorem genPos_triangles {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    ¬ Collinear ℝ ({meet L₂ L₃, meet L₂ L₄, meet L₃ L₄} : Set ℂ) ∧
    ¬ Collinear ℝ ({meet L₁ L₃, meet L₁ L₄, meet L₃ L₄} : Set ℂ) ∧
    ¬ Collinear ℝ ({meet L₁ L₂, meet L₁ L₄, meet L₂ L₄} : Set ℂ) ∧
    ¬ Collinear ℝ ({meet L₁ L₂, meet L₁ L₃, meet L₂ L₃} : Set ℂ) ∧
    List.Pairwise (· ≠ ·)
```

Bridge.lean:232
```lean
theorem pw_eq_power (z P Q : ℂ) :
    pw z P Q = (⟨(P + Q) / 2, dist P Q / 2⟩ : EuclideanGeometry.Sphere ℂ).power z := by
```

Bridge.lean:238
```lean
noncomputable def diamCircle (P Q : ℂ) : EuclideanGeometry.Sphere ℂ := ⟨(P + Q) / 2, dist P Q / 2⟩
```

Bridge.lean:243
```lean
theorem bodenmiller_coaxal {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    (∀ H ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
      (diamCircle (meet L₁ L₂) (meet L₃ L₄)).power H =
        (diamCircle (meet L₁ L₃) (meet L₂ L₄)).power H ∧
      (diamCircle (meet L₁ L₂) (meet L₃ L₄)).power H =
        (diamCircle (meet L₁ L₄) (meet L₂ L₃)).power H) ∧
    (diamCircle (meet L₁ L₂) (meet L₃ L₄)).center ≠ (diamCircle (meet L₁ L₃) (meet L₂ L₄)).center ∧
    (diamCircle (meet L₁ L₂) (meet L₃ L₄)).center ≠ (diamCircle (meet L₁ L₄) (meet L₂ L₃)).center ∧
    (diamCircle (meet L₁ L₃) (meet L₂ L₄)).center ≠ (diamCircle (meet L₁ L₄) (meet L₂ L₃)).center := by
  refine ⟨fun H hH => ?_, diag_midpoints_ne h, ?_, ?_⟩
```

Bridge.lean:283
```lean
theorem perp_iff_inner (a b : ℂ) : (a * conj b).re = 0 ↔ inner ℝ a b = 0 := by
```

Bridge.lean:287
```lean
theorem orthocentre_line_perp_inner {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    ∀ H₁ ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
    ∀ H₂ ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
      inner ℝ ((meet L₁ L₃ + meet L₂ L₄) / 2 - (meet L₁ L₂ + meet L₃ L₄) / 2) (H₂ - H₁) = 0 :=
  fun H₁ h₁ H₂ h₂ => (perp_iff_inner _ _).mp (orthocentre_line_perp h H₁ h₁ H₂ h₂)
```

Bridge.lean:300
```lean
noncomputable def Line.toAffine (L : Line) : AffineSubspace ℝ ℂ := line[ℝ, L.p, L.p + L.d]
```

Bridge.lean:303
```lean
theorem parallel_iff_cr {L M : Line} (hL : L.d ≠ 0) (hM : M.d ≠ 0) :
    L.toAffine.Parallel M.toAffine ↔ cr L.d M.d = 0 := by
```

Bridge.lean:334
```lean
theorem genPos_iff {L₁ L₂ L₃ L₄ : Line} :
    GenPos L₁ L₂ L₃ L₄ ↔
      (L₁.d ≠ 0 ∧ L₂.d ≠ 0 ∧ L₃.d ≠ 0 ∧ L₄.d ≠ 0) ∧
      (¬ L₁.toAffine.Parallel L₂.toAffine ∧ ¬ L₁.toAffine.Parallel L₃.toAffine ∧
        ¬ L₁.toAffine.Parallel L₄.toAffine ∧ ¬ L₂.toAffine.Parallel L₃.toAffine ∧
        ¬ L₂.toAffine.Parallel L₄.toAffine ∧ ¬ L₃.toAffine.Parallel L₄.toAffine) ∧
      (¬ ∃ z, z ∈ L₁.toAffine ∧ z ∈ L₂.toAffine ∧ z ∈ L₃.toAffine) ∧
      (¬ ∃ z, z ∈ L₁.toAffine ∧ z ∈ L₂.toAffine ∧ z ∈ L₄.toAffine) ∧
      (¬ ∃ z, z ∈ L₁.toAffine ∧ z ∈ L₃.toAffine ∧ z ∈ L₄.toAffine) ∧
      (¬ ∃ z, z ∈ L₂.toAffine ∧ z ∈ L₃.toAffine ∧ z ∈ L₄.toAffine) := by
  have r : ∀ {a b : ℂ}, cr a b ≠ 0 → cr b a ≠ 0 := fun hh => by
    rw [cr_comm]; exact neg_ne_zero.mpr hh
```

## Gate
REQUIRED (gate.sh) gained 13 names (QuadNewton.-qualified): carrier_eq_line meet_eq_iff collinear_iff_cr circ_eq_circumcenter ortho_eq_orthocenter foot_eq_orthogonalProjection genPos_triangles pw_eq_power bodenmiller_coaxal perp_iff_inner orthocentre_line_perp_inner parallel_iff_cr genPos_iff.
```
PASS (35 declarations, standard axioms only)
```
All 35 reports are [propext, Classical.choice, Quot.sound]. Bridge.lean contains no forbidden token.

## Tamper (bash tests/tamper.sh)
```
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: QuadNewton.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```

## sha256 before
```
3f42fa0236da4916454768a17e3015c4c4db0e19bceef7f6c2490e699d44c45d  QuadNewton.lean
7514740705648ce85f70f0ad0c991a963baaa4b2ac8e5ae6c2b503e03d7040c3  QuadNewton/Basic.lean
b005e0198ac9477785862cf89ea5e1768cf66df900f9d4e5808cb6720c9f86fb  QuadNewton/Core.lean
55d37f730c57fddb76b9744ece554b1dfa73a16b422453c1bcaa6274d5aba9d7  QuadNewton/Lines.lean
06783cf3344b232b4d3e321821e978a03500862c8593fbb1ceb0b202f3736aaa  QuadNewton/Quad.lean
6b8cb4cc23a851e42be38e67328ef97ca500daf32ff3458a943109100545903a  gate.sh
a20034ad5e6ac7ec090841d18f8cc04e894cc9739ce8725eddfa9cc1ad682c6c  tests/tamper.sh
```
## sha256 after
```
5cb4e2e86eefa5a8aad6f60461a9bba2dbc67654cc4e1bdfe377743380366bf4  QuadNewton.lean
7514740705648ce85f70f0ad0c991a963baaa4b2ac8e5ae6c2b503e03d7040c3  QuadNewton/Basic.lean
902c885b3fe53ae1ccccf11e3d9e2a436945257f0d8b2269937f27f379bc1974  QuadNewton/Bridge.lean
b005e0198ac9477785862cf89ea5e1768cf66df900f9d4e5808cb6720c9f86fb  QuadNewton/Core.lean
55d37f730c57fddb76b9744ece554b1dfa73a16b422453c1bcaa6274d5aba9d7  QuadNewton/Lines.lean
06783cf3344b232b4d3e321821e978a03500862c8593fbb1ceb0b202f3736aaa  QuadNewton/Quad.lean
9e6a53a07316b53d70a485340bcd0537e6487f3e03a371716fb06abb2158f04f  gate.sh
a20034ad5e6ac7ec090841d18f8cc04e894cc9739ce8725eddfa9cc1ad682c6c  tests/tamper.sh
```
Basic.lean, Lines.lean, Core.lean, Quad.lean and tests/tamper.sh are byte-identical. QuadNewton.lean changed only by the appended `import QuadNewton.Bridge`; gate.sh changed only on its REQUIRED line. Bridge.lean is new.

Numeric scripts (agent host): br_n/py/check.py (output `failures {'B1(d=0)': 4000}`, i.e. only the excluded d=0 case) and br_n/py/check_b7.py (0 mismatches).
