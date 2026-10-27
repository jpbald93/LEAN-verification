import Brocard.Main
import Brocard.Extensions

/-!
# Layer 14: Mathlib-only restatements and witnesses for the Brocard theorems

Every `l14_*` theorem below has a statement mentioning only Mathlib notions: the library's
`symmedianPoint`, `brocardPoint₁`, `brocardPoint₂`, `area` and `lemoinePoints` are unfolded into
explicit `Finset.univ.affineCombination`s, `AffineMap.lineMap`s and `Real.sin` expressions in the
squared side lengths `a² = dist B C ^ 2`, `b² = dist C A ^ 2`, `c² = dist A B ^ 2`. Each is proved
from the corresponding library theorem. The `l14w_*` theorems are explicit witnesses in
`EuclideanSpace ℝ (Fin 2)` (non-vacuity); the `l14b_*` lemmas are coordinate helpers for them.
-/

namespace Brocard

open EuclideanGeometry
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ### Restatements -/

/-- B1: the symmedians are the reflections of the medians in the angle bisectors. -/
theorem l14_symmedian_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
    ∠ B A K = ∠ (midpoint ℝ B C) A C ∧ ∠ C A K = ∠ (midpoint ℝ B C) A B ∧
    ∠ C B K = ∠ (midpoint ℝ C A) B A ∧ ∠ A B K = ∠ (midpoint ℝ C A) B C ∧
    ∠ A C K = ∠ (midpoint ℝ A B) C B ∧ ∠ B C K = ∠ (midpoint ℝ A B) C A :=
  symmedian_angles t

/-- B1: the symmedian point lies in the interior (positive barycentric weights). -/
theorem l14_symmedianPoint_mem_interior (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
    ∃ w : Fin 3 → ℝ, ∑ i, w i = 1 ∧ (∀ i, 0 < w i) ∧
      K = Finset.univ.affineCombination ℝ t.points w :=
  symmedianPoint_mem_interior t

/-- B2: the symmedian point is the centroid of its pedal triangle. -/
theorem l14_symmedianPoint_eq_centroid_pedal (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
    Finset.univ.centroid ℝ ![(orthogonalProjection line[ℝ, B, C] K : P),
      (orthogonalProjection line[ℝ, C, A] K : P), (orthogonalProjection line[ℝ, A, B] K : P)] = K :=
  symmedianPoint_eq_centroid_pedal t

/-- B2 (converse, in the plane): a point that is the centroid of its pedal triangle is the
symmedian point. -/
theorem l14_eq_symmedianPoint_of_eq_centroid_pedal [Fact (Module.finrank ℝ V = 2)]
    (t : Affine.Triangle ℝ P) (X : P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
    Finset.univ.centroid ℝ ![(orthogonalProjection line[ℝ, B, C] X : P),
      (orthogonalProjection line[ℝ, C, A] X : P), (orthogonalProjection line[ℝ, A, B] X : P)] = X →
    X = K :=
  eq_symmedianPoint_of_eq_centroid_pedal t X

/-- B3: the first Brocard point, `∠ Ω A B = ∠ Ω B C = ∠ Ω C A`. -/
theorem l14_brocardPoint₁_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let Ω := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A :=
  brocardPoint₁_angles t

/-- B3: the second Brocard point, `∠ Ω' B A = ∠ Ω' C B = ∠ Ω' A C`. -/
theorem l14_brocardPoint₂_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let Ω' := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / c2, 1 / a2, 1 / b2] i / (1 / a2 + 1 / b2 + 1 / c2)
    ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C :=
  brocardPoint₂_angles t

/-- B4: `cot ω = cot A + cot B + cot C`. -/
theorem l14_cot_brocardAngle_eq_sum_cot (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let Ω := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    Real.cot (∠ Ω A B) = Real.cot (∠ B A C) + Real.cot (∠ A B C) + Real.cot (∠ A C B) :=
  cot_brocardAngle_eq_sum_cot t

/-- B4: `cot ω = (a² + b² + c²) / (4 Δ)` with `Δ = ½ · AB · AC · sin A`. -/
theorem l14_cot_brocardAngle_eq_div_area (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let Ω := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    Real.cot (∠ Ω A B) = (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) /
      (4 * ((1 / 2) * dist A B * dist A C * Real.sin (∠ B A C))) :=
  cot_brocardAngle_eq_div_area t

/-- B4: `0 < ω ≤ π / 6`. -/
theorem l14_brocardAngle_pos_le (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let Ω := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    0 < ∠ Ω A B ∧ ∠ Ω A B ≤ Real.pi / 6 :=
  brocardAngle_pos_le t

/-- D1: the two Brocard points are isogonal conjugates (equal Brocard angles at each vertex). -/
theorem l14_brocardPoints_isogonal (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let Ω₁ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    let Ω₂ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / c2, 1 / a2, 1 / b2] i / (1 / a2 + 1 / b2 + 1 / c2)
    ∠ Ω₁ A B = ∠ Ω₂ A C ∧ ∠ Ω₁ B C = ∠ Ω₂ B A ∧ ∠ Ω₁ C A = ∠ Ω₂ C B :=
  brocardPoints_isogonal t

/-- D1: the Brocard points are equidistant from the circumcentre. -/
theorem l14_dist_circumcenter_brocardPoint (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let Ω₁ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    let Ω₂ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / c2, 1 / a2, 1 / b2] i / (1 / a2 + 1 / b2 + 1 / c2)
    dist t.circumcenter Ω₁ = dist t.circumcenter Ω₂ :=
  dist_circumcenter_brocardPoint t

/-- D2: `O`, `K`, `Ω₁`, `Ω₂` lie on the circle with diameter `OK` (the Brocard circle). -/
theorem l14_brocardCircle (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let O := t.circumcenter
    let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
    let Ω₁ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    let Ω₂ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / c2, 1 / a2, 1 / b2] i / (1 / a2 + 1 / b2 + 1 / c2)
    (∀ X ∈ ({O, K, Ω₁, Ω₂} : Set P), dist X (midpoint ℝ O K) = dist O K / 2) ∧
      Cospherical ({O, K, Ω₁, Ω₂} : Set P) :=
  ⟨brocardCircle t, cospherical_brocardCircle t⟩

/-- D2: `∠ O Ω₁ K = ∠ O Ω₂ K = π / 2`. -/
theorem l14_brocardCircle_right_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let O := t.circumcenter
    let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
    let Ω₁ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    let Ω₂ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / c2, 1 / a2, 1 / b2] i / (1 / a2 + 1 / b2 + 1 / c2)
    ⟪O -ᵥ Ω₁, K -ᵥ Ω₁⟫ = 0 ∧ ⟪O -ᵥ Ω₂, K -ᵥ Ω₂⟫ = 0 ∧
    ∠ O Ω₁ K = Real.pi / 2 ∧ ∠ O Ω₂ K = Real.pi / 2 :=
  brocardCircle_right_angles t

/-- D2: the Brocard circle degenerates exactly for equilateral triangles. -/
theorem l14_brocardCircle_degenerate (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let O := t.circumcenter
    let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
    let Ω₁ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    let Ω₂ := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / c2, 1 / a2, 1 / b2] i / (1 / a2 + 1 / b2 + 1 / c2)
    ((Ω₁ = O ∨ Ω₁ = K ∨ Ω₂ = O ∨ Ω₂ = K ∨ K = O) ↔ (dist A B = dist B C ∧ dist B C = dist C A)) ∧
    (dist A B = dist B C → dist B C = dist C A → Ω₁ = O ∧ Ω₂ = O ∧ K = O) :=
  ⟨brocardCircle_degenerate t, brocard_eq_circumcenter_of_equilateral t⟩

/-- D3: the six points where the parallels through `K` to the sides meet the other sides are
concyclic (first Lemoine circle, centre the midpoint of `O K`). The six points are given
explicitly; each lies on the stated side and on the stated parallel through `K`. -/
theorem l14_lemoineCircle (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let S := a2 + b2 + c2
    let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
    let L : Fin 6 → P := ![AffineMap.lineMap C A (a2 / S), AffineMap.lineMap A B ((b2 + c2) / S),
      AffineMap.lineMap B C ((c2 + a2) / S), AffineMap.lineMap A B (b2 / S),
      AffineMap.lineMap B C (c2 / S), AffineMap.lineMap C A ((a2 + b2) / S)]
    ((L 0 ∈ line[ℝ, C, A] ∧ L 0 ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction) ∧
    (L 1 ∈ line[ℝ, A, B] ∧ L 1 ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction) ∧
    (L 2 ∈ line[ℝ, B, C] ∧ L 2 ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction) ∧
    (L 3 ∈ line[ℝ, A, B] ∧ L 3 ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction) ∧
    (L 4 ∈ line[ℝ, B, C] ∧ L 4 ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction) ∧
    (L 5 ∈ line[ℝ, C, A] ∧ L 5 ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction)) ∧
    (∀ i, dist (L i) (midpoint ℝ t.circumcenter K) = dist (L 0) (midpoint ℝ t.circumcenter K)) ∧
    Cospherical (Set.range L) :=
  ⟨lemoinePoints_mem t, lemoineCircle t, cospherical_lemoinePoints t⟩

/-- D4 (Droz-Farny). -/
theorem l14_drozFarny [Fact (Module.finrank ℝ V = 2)] (t : Affine.Triangle ℝ P) (d₁ d₂ : V)
    (hperp : ⟪d₁, d₂⟫ = 0)
    (h₁a : d₁ ∉ (line[ℝ, t.points 1, t.points 2]).direction)
    (h₁b : d₁ ∉ (line[ℝ, t.points 2, t.points 0]).direction)
    (h₁c : d₁ ∉ (line[ℝ, t.points 0, t.points 1]).direction)
    (h₂a : d₂ ∉ (line[ℝ, t.points 1, t.points 2]).direction)
    (h₂b : d₂ ∉ (line[ℝ, t.points 2, t.points 0]).direction)
    (h₂c : d₂ ∉ (line[ℝ, t.points 0, t.points 1]).direction)
    {X₁ Y₁ X₂ Y₂ X₃ Y₃ : P}
    (hX₁ : X₁ ∈ line[ℝ, t.points 1, t.points 2]) (hX₁' : X₁ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁))
    (hY₁ : Y₁ ∈ line[ℝ, t.points 1, t.points 2]) (hY₁' : Y₁ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂))
    (hX₂ : X₂ ∈ line[ℝ, t.points 2, t.points 0]) (hX₂' : X₂ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁))
    (hY₂ : Y₂ ∈ line[ℝ, t.points 2, t.points 0]) (hY₂' : Y₂ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂))
    (hX₃ : X₃ ∈ line[ℝ, t.points 0, t.points 1]) (hX₃' : X₃ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁))
    (hY₃ : Y₃ ∈ line[ℝ, t.points 0, t.points 1]) (hY₃' : Y₃ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂)) :
    Collinear ℝ ({midpoint ℝ X₁ Y₁, midpoint ℝ X₂ Y₂, midpoint ℝ X₃ Y₃} : Set P) :=
  drozFarny t d₁ d₂ hperp h₁a h₁b h₁c h₂a h₂b h₂c hX₁ hX₁' hY₁ hY₁' hX₂ hX₂' hY₂ hY₂' hX₃ hX₃'
    hY₃ hY₃'

/-! ### Witnesses -/


theorem l14b_dist_sq (x y : EuclideanSpace ℝ (Fin 2)) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem l14b_not_collinear (X Y Z : EuclideanSpace ℝ (Fin 2))
    (h : (Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0) ≠ 0) :
    ¬ Collinear ℝ ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hc
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hc
  obtain ⟨v, hv⟩ := hc
  obtain ⟨r, hr⟩ := hv Y (by simp)
  obtain ⟨s, hs⟩ := hv Z (by simp)
  apply h
  have h0 := congrArg (· 0) hr; have h1 := congrArg (· 1) hr
  have h2 := congrArg (· 0) hs; have h3 := congrArg (· 1) hs
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]; ring

theorem l14b_ne (X Y : EuclideanSpace ℝ (Fin 2)) (h : X 0 ≠ Y 0 ∨ X 1 ≠ Y 1) : X ≠ Y := by
  rintro rfl; tauto

theorem l14b_eq (X : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) (h0 : X 0 = a) (h1 : X 1 = b) : X = !₂[a, b] := by
  ext i; fin_cases i <;> simp [h0, h1]

theorem l14b_tri : ¬ Collinear ℝ ({!₂[0, 0], !₂[4, 0], !₂[1, 3]} : Set (EuclideanSpace ℝ (Fin 2))) :=
  l14b_not_collinear _ _ _ (by simp)

/-- The witness triangle `A = (0,0)`, `B = (4,0)`, `C = (1,3)`. -/
noncomputable def l14T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![!₂[0, 0], !₂[4, 0], !₂[1, 3]], affineIndependent_iff_not_collinear_set.2 l14b_tri⟩

theorem l14T_a2 : dist (l14T.points 1) (l14T.points 2) ^ 2 = 18 := by
  rw [l14b_dist_sq]; simp [l14T]; norm_num
theorem l14T_b2 : dist (l14T.points 2) (l14T.points 0) ^ 2 = 10 := by
  rw [l14b_dist_sq]; simp [l14T]; norm_num
theorem l14T_c2 : dist (l14T.points 0) (l14T.points 1) ^ 2 = 16 := by
  rw [l14b_dist_sq]; simp [l14T]; norm_num

theorem l14b_ac (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (w : Fin 3 → ℝ) (hw : w 0 + w 1 + w 2 = 1) :
    Finset.univ.affineCombination ℝ t.points w =
      !₂[w 0 * t.points 0 0 + w 1 * t.points 1 0 + w 2 * t.points 2 0,
        w 0 * t.points 0 1 + w 1 * t.points 1 1 + w 2 * t.points 2 1] := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa [Fin.sum_univ_three] using hw)]
  ext i; fin_cases i <;> simp [Fin.sum_univ_three]

theorem l14T_K : (Finset.univ.affineCombination ℝ l14T.points fun i =>
    ![dist (l14T.points 1) (l14T.points 2) ^ 2, dist (l14T.points 2) (l14T.points 0) ^ 2,
      dist (l14T.points 0) (l14T.points 1) ^ 2] i /
    (dist (l14T.points 1) (l14T.points 2) ^ 2 + dist (l14T.points 2) (l14T.points 0) ^ 2 +
      dist (l14T.points 0) (l14T.points 1) ^ 2)) = !₂[14/11, 12/11] := by
  rw [l14T_a2, l14T_b2, l14T_c2, l14b_ac _ _ (by simp; norm_num)]
  simp [l14T]; norm_num

theorem l14T_O : l14T.circumcenter = !₂[2, 1] := by
  refine (l14T.eq_circumcenter_of_dist_eq (r := √5) ?_ ?_).symm
  · rw [l14T.span_eq_top (by simp)]; exact AffineSubspace.mem_top _ _ _
  · intro i
    rw [← sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num), l14b_dist_sq]
    fin_cases i <;> simp [l14T] <;> norm_num

theorem l14T_H : l14T.orthocenter = !₂[1, 1] := by
  rw [Affine.Triangle.orthocenter_eq_smul_vsub_vadd_circumcenter, l14T_O, Finset.centroid,
    l14b_ac _ _ (by simp; norm_num)]
  ext i; fin_cases i <;> simp [l14T] <;> norm_num


theorem l14b_lineMap (X Y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    AffineMap.lineMap X Y r = !₂[X 0 + r * (Y 0 - X 0), X 1 + r * (Y 1 - X 1)] := by
  rw [AffineMap.lineMap_apply_module']
  ext i; fin_cases i <;> simp <;> ring

theorem l14b_ne' (X Y : EuclideanSpace ℝ (Fin 2)) (h : X 0 ≠ Y 0 ∨ X 1 ≠ Y 1) : X ≠ Y := by
  rintro rfl; tauto

theorem l14T_Ω₁ : (Finset.univ.affineCombination ℝ l14T.points fun i =>
    ![1 / dist (l14T.points 2) (l14T.points 0) ^ 2, 1 / dist (l14T.points 0) (l14T.points 1) ^ 2,
      1 / dist (l14T.points 1) (l14T.points 2) ^ 2] i /
    (1 / dist (l14T.points 1) (l14T.points 2) ^ 2 + 1 / dist (l14T.points 2) (l14T.points 0) ^ 2 +
      1 / dist (l14T.points 0) (l14T.points 1) ^ 2)) = !₂[220/157, 120/157] := by
  rw [l14T_a2, l14T_b2, l14T_c2, l14b_ac _ _ (by simp; norm_num)]
  simp [l14T]; norm_num

theorem l14T_Ω₂ : (Finset.univ.affineCombination ℝ l14T.points fun i =>
    ![1 / dist (l14T.points 0) (l14T.points 1) ^ 2, 1 / dist (l14T.points 1) (l14T.points 2) ^ 2,
      1 / dist (l14T.points 2) (l14T.points 0) ^ 2] i /
    (1 / dist (l14T.points 1) (l14T.points 2) ^ 2 + 1 / dist (l14T.points 2) (l14T.points 0) ^ 2 +
      1 / dist (l14T.points 0) (l14T.points 1) ^ 2)) = !₂[232/157, 216/157] := by
  rw [l14T_a2, l14T_b2, l14T_c2, l14b_ac _ _ (by simp; norm_num)]
  simp [l14T]; norm_num

/-- Witness (B1, B2, D2): for `A = (0,0)`, `B = (4,0)`, `C = (1,3)` the symmedian point is
`K = (14/11, 12/11)`, distinct from the vertices, the centroid `(5/3, 1)` and `O = (2, 1)`;
the Brocard points are `Ω₁ = (220/157, 120/157)` and `Ω₂ = (232/157, 216/157)`, and
`O, K, Ω₁, Ω₂` are pairwise distinct. -/
theorem l14w_brocard :
    ∃ t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[1, 3]] ∧
      let A := t.points 0; let B := t.points 1; let C := t.points 2
      let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
      let O := t.circumcenter
      let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
      let Ω₁ := Finset.univ.affineCombination ℝ t.points
        fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
      let Ω₂ := Finset.univ.affineCombination ℝ t.points
        fun i => ![1 / c2, 1 / a2, 1 / b2] i / (1 / a2 + 1 / b2 + 1 / c2)
      a2 = 18 ∧ b2 = 10 ∧ c2 = 16 ∧
      O = !₂[2, 1] ∧ K = !₂[14/11, 12/11] ∧ Ω₁ = !₂[220/157, 120/157] ∧
      Ω₂ = !₂[232/157, 216/157] ∧
      K ≠ A ∧ K ≠ B ∧ K ≠ C ∧ K ≠ Finset.univ.centroid ℝ t.points ∧
      Ω₁ ≠ A ∧ Ω₁ ≠ B ∧ Ω₁ ≠ C ∧ Ω₂ ≠ A ∧ Ω₂ ≠ B ∧ Ω₂ ≠ C ∧
      K ≠ O ∧ Ω₁ ≠ O ∧ Ω₂ ≠ O ∧ Ω₁ ≠ K ∧ Ω₂ ≠ K ∧ Ω₁ ≠ Ω₂ ∧
      ¬ (dist A B = dist B C ∧ dist B C = dist C A) := by
  refine ⟨l14T, rfl, ?_⟩
  dsimp only
  rw [l14T_K, l14T_Ω₁, l14T_Ω₂, l14T_O, l14T_a2, l14T_b2, l14T_c2, Finset.centroid,
    l14b_ac _ _ (by simp; norm_num)]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 16
  · rintro ⟨h, -⟩
    have h2 := congrArg (· ^ 2) h
    rw [l14T_c2, l14T_a2] at h2; norm_num at h2
  all_goals (apply l14b_ne'; simp [l14T]; try norm_num)


/-- Witness (B4): for the same triangle `Δ = 6`, so `cot ω = 44 / 24 = 11 / 6` and in particular
`ω < π / 6` (strict, as the triangle is not equilateral). -/
theorem l14w_brocardAngle :
    ∀ t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[1, 3]] →
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let Ω := Finset.univ.affineCombination ℝ t.points
      fun i => ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2)
    (1 / 2) * dist A B * dist A C * Real.sin (∠ B A C) = 6 ∧ Real.cot (∠ Ω A B) = 11 / 6 ∧
      0 < ∠ Ω A B ∧ ∠ Ω A B < Real.pi / 6 := by
  intro t ht
  obtain rfl : t = l14T := Affine.Simplex.ext fun i => by rw [ht]; rfl
  intro A B C a2 b2 c2 Ω
  have harea : (1 / 2) * dist A B * dist A C * Real.sin (∠ B A C) = 6 := by
    have h := area_eq_sqrt_dist l14T
    simp only [Affine.Triangle.area] at h
    rw [dist_comm (l14T.points 0) (l14T.points 2), dist_comm (l14T.points 2) (l14T.points 0)] at h
    show (1 / 2) * dist (l14T.points 0) (l14T.points 1) * dist (l14T.points 0) (l14T.points 2) *
      Real.sin (∠ (l14T.points 1) (l14T.points 0) (l14T.points 2)) = 6
    rw [h, dist_comm (l14T.points 0) (l14T.points 2), l14T_c2, l14T_b2, l14T_a2]
    rw [show (16 : ℝ) * 10 - ((10 + 16 - 18) / 2) ^ 2 = 12 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  have hcot : Real.cot (∠ Ω A B) = 11 / 6 := by
    have h := l14_cot_brocardAngle_eq_div_area l14T
    simp only at h
    rw [harea] at h
    show Real.cot _ = _
    rw [h, l14T_a2, l14T_b2, l14T_c2]; norm_num
  obtain ⟨hpos, hle⟩ := l14_brocardAngle_pos_le l14T
  refine ⟨harea, hcot, hpos, lt_of_le_of_ne hle fun he => ?_⟩
  rw [show ∠ Ω A B = Real.pi / 6 from he, Real.cot_eq_cos_div_sin, Real.cos_pi_div_six,
    Real.sin_pi_div_six] at hcot
  have h3 : Real.sqrt 3 = 11 / 6 := by linarith
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [h3] at this; norm_num at this

theorem l14T_L :
    let t := l14T
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let S := a2 + b2 + c2
    (![AffineMap.lineMap C A (a2 / S), AffineMap.lineMap A B ((b2 + c2) / S),
      AffineMap.lineMap B C ((c2 + a2) / S), AffineMap.lineMap A B (b2 / S),
      AffineMap.lineMap B C (c2 / S), AffineMap.lineMap C A ((a2 + b2) / S)] : Fin 6 → (EuclideanSpace ℝ (Fin 2))) =
    ![!₂[13/22, 39/22], !₂[26/11, 0], !₂[37/22, 51/22], !₂[10/11, 0], !₂[32/11, 12/11],
      !₂[4/11, 12/11]] := by
  intro t A B C a2 b2 c2 S
  simp only [S, a2, b2, c2, A, B, C, t, l14T_a2, l14T_b2, l14T_c2, l14b_lineMap]
  ext i j; fin_cases i <;> fin_cases j <;> simp [l14T] <;> try norm_num

/-- Witness (D3): for the same triangle the six Lemoine points are
`(13/22, 39/22)`, `(26/11, 0)`, `(37/22, 51/22)`, `(10/11, 0)`, `(32/11, 12/11)`, `(4/11, 12/11)`,
pairwise distinct (so the concyclicity is a statement about six distinct points). -/
theorem l14w_lemoine :
    ∀ t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[1, 3]] →
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let S := a2 + b2 + c2
    let L : Fin 6 → (EuclideanSpace ℝ (Fin 2)) := ![AffineMap.lineMap C A (a2 / S), AffineMap.lineMap A B ((b2 + c2) / S),
      AffineMap.lineMap B C ((c2 + a2) / S), AffineMap.lineMap A B (b2 / S),
      AffineMap.lineMap B C (c2 / S), AffineMap.lineMap C A ((a2 + b2) / S)]
    Function.Injective L := by
  intro t ht
  obtain rfl : t = l14T := Affine.Simplex.ext fun i => by rw [ht]; rfl
  intro A B C a2 b2 c2 S L
  show Function.Injective (![AffineMap.lineMap C A (a2 / S), AffineMap.lineMap A B ((b2 + c2) / S),
      AffineMap.lineMap B C ((c2 + a2) / S), AffineMap.lineMap A B (b2 / S),
      AffineMap.lineMap B C (c2 / S), AffineMap.lineMap C A ((a2 + b2) / S)] : Fin 6 → (EuclideanSpace ℝ (Fin 2)))
  rw [l14T_L]
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso; have h0 := congrArg (· 0) h; have h1 := congrArg (· 1) h
       simp at h0 h1 <;> (revert h0 h1; norm_num))


instance l14b_fact_finrank : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨finrank_euclideanSpace_fin⟩

/-- Witness (B2, converse): for the witness triangle the centroid `G` is not the centroid of its
own pedal triangle (because `G ≠ K`), while `K` is; so the converse distinguishes points. -/
theorem l14w_pedal :
    ∀ t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[1, 3]] →
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a2 := dist B C ^ 2; let b2 := dist C A ^ 2; let c2 := dist A B ^ 2
    let K := Finset.univ.affineCombination ℝ t.points fun i => ![a2, b2, c2] i / (a2 + b2 + c2)
    let G := Finset.univ.centroid ℝ t.points
    Finset.univ.centroid ℝ ![(orthogonalProjection line[ℝ, B, C] K : EuclideanSpace ℝ (Fin 2)),
      (orthogonalProjection line[ℝ, C, A] K : EuclideanSpace ℝ (Fin 2)), (orthogonalProjection line[ℝ, A, B] K : EuclideanSpace ℝ (Fin 2))] = K ∧
    Finset.univ.centroid ℝ ![(orthogonalProjection line[ℝ, B, C] G : EuclideanSpace ℝ (Fin 2)),
      (orthogonalProjection line[ℝ, C, A] G : EuclideanSpace ℝ (Fin 2)), (orthogonalProjection line[ℝ, A, B] G : EuclideanSpace ℝ (Fin 2))] ≠ G := by
  intro t ht
  obtain rfl : t = l14T := Affine.Simplex.ext fun i => by rw [ht]; rfl
  intro A B C a2 b2 c2 K G
  refine ⟨l14_symmedianPoint_eq_centroid_pedal l14T, fun h => ?_⟩
  have hGK := l14_eq_symmedianPoint_of_eq_centroid_pedal l14T G h
  have hw := l14w_brocard
  obtain ⟨t', ht', -, -, -, -, -, -, -, -, -, -, hKG, -⟩ := hw
  have e : t' = l14T := Affine.Simplex.ext fun i => by rw [ht']; rfl
  subst e
  exact hKG hGK.symm

theorem l14b_mem_line (X Y Z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (h : Z = AffineMap.lineMap X Y r) : Z ∈ line[ℝ, X, Y] :=
  h ▸ AffineMap.lineMap_mem_affineSpan_pair _ _ _

theorem l14b_mem_mk' (H Z : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)) (a : ℝ) (h0 : Z 0 = H 0 + a * d 0)
    (h1 : Z 1 = H 1 + a * d 1) : Z ∈ AffineSubspace.mk' H (ℝ ∙ d) := by
  rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  refine ⟨a, ?_⟩
  ext i; fin_cases i <;> simp [h0, h1]

theorem l14b_notMem_dir (X Y d : EuclideanSpace ℝ (Fin 2))
    (h : d 0 * (X 1 - Y 1) - d 1 * (X 0 - Y 0) ≠ 0) : d ∉ (line[ℝ, X, Y]).direction := by
  rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  apply h
  have h0 := congrArg (· 0) ha; have h1 := congrArg (· 1) ha
  simp at h0 h1
  rw [← h0, ← h1]; ring

/-- Witness (D4): for the witness triangle (`H = (1, 1)`) and the perpendicular directions
`d₁ = (1, 2)`, `d₂ = (2, -1)` (not parallel to any side), the six intersection points are
`X₁ = (5/3, 7/3)`, `Y₁ = (5, -1)`, `X₂ = (-1, -3)`, `Y₂ = (3/7, 9/7)`, `X₃ = (1/2, 0)`,
`Y₃ = (3, 0)`, and the three midpoints `(10/3, 2/3)`, `(-2/7, -6/7)`, `(7/4, 0)` are pairwise
distinct (and collinear, by `l14_drozFarny`). -/
theorem l14w_drozFarny :
    ∀ t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[1, 3]] →
    let d₁ : EuclideanSpace ℝ (Fin 2) := !₂[1, 2]; let d₂ : EuclideanSpace ℝ (Fin 2) := !₂[2, -1]
    let X₁ : EuclideanSpace ℝ (Fin 2) := !₂[5/3, 7/3]; let Y₁ : EuclideanSpace ℝ (Fin 2) := !₂[5, -1]
    let X₂ : EuclideanSpace ℝ (Fin 2) := !₂[-1, -3]; let Y₂ : EuclideanSpace ℝ (Fin 2) := !₂[3/7, 9/7]
    let X₃ : EuclideanSpace ℝ (Fin 2) := !₂[1/2, 0]; let Y₃ : EuclideanSpace ℝ (Fin 2) := !₂[3, 0]
    t.orthocenter = !₂[1, 1] ∧ ⟪d₁, d₂⟫ = 0 ∧
    d₁ ∉ (line[ℝ, t.points 1, t.points 2]).direction ∧
    d₁ ∉ (line[ℝ, t.points 2, t.points 0]).direction ∧
    d₁ ∉ (line[ℝ, t.points 0, t.points 1]).direction ∧
    d₂ ∉ (line[ℝ, t.points 1, t.points 2]).direction ∧
    d₂ ∉ (line[ℝ, t.points 2, t.points 0]).direction ∧
    d₂ ∉ (line[ℝ, t.points 0, t.points 1]).direction ∧
    (X₁ ∈ line[ℝ, t.points 1, t.points 2] ∧ X₁ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁)) ∧
    (Y₁ ∈ line[ℝ, t.points 1, t.points 2] ∧ Y₁ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂)) ∧
    (X₂ ∈ line[ℝ, t.points 2, t.points 0] ∧ X₂ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁)) ∧
    (Y₂ ∈ line[ℝ, t.points 2, t.points 0] ∧ Y₂ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂)) ∧
    (X₃ ∈ line[ℝ, t.points 0, t.points 1] ∧ X₃ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁)) ∧
    (Y₃ ∈ line[ℝ, t.points 0, t.points 1] ∧ Y₃ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂)) ∧
    midpoint ℝ X₁ Y₁ = !₂[10/3, 2/3] ∧ midpoint ℝ X₂ Y₂ = !₂[-2/7, -6/7] ∧
    midpoint ℝ X₃ Y₃ = !₂[7/4, 0] ∧
    midpoint ℝ X₁ Y₁ ≠ midpoint ℝ X₂ Y₂ ∧ midpoint ℝ X₁ Y₁ ≠ midpoint ℝ X₃ Y₃ ∧
    midpoint ℝ X₂ Y₂ ≠ midpoint ℝ X₃ Y₃ := by
  intro t ht
  obtain rfl : t = l14T := Affine.Simplex.ext fun i => by rw [ht]; rfl
  intro d₁ d₂ X₁ Y₁ X₂ Y₂ X₃ Y₃
  have hH : l14T.orthocenter = !₂[1, 1] := l14T_H
  have m1 : midpoint ℝ X₁ Y₁ = !₂[10/3, 2/3] := by
    rw [midpoint_eq_smul_add]; ext i; fin_cases i <;> simp [X₁, Y₁] <;> norm_num
  have m2 : midpoint ℝ X₂ Y₂ = !₂[-2/7, -6/7] := by
    rw [midpoint_eq_smul_add]; ext i; fin_cases i <;> simp [X₂, Y₂] <;> norm_num
  have m3 : midpoint ℝ X₃ Y₃ = !₂[7/4, 0] := by
    rw [midpoint_eq_smul_add]; ext i; fin_cases i <;> simp [X₃, Y₃] <;> norm_num
  rw [hH, m1, m2, m3]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [d₁, d₂, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  all_goals first
    | (apply l14b_notMem_dir; simp [l14T, d₁, d₂]; try norm_num)
    | (apply l14b_ne'; simp; try norm_num)
    | skip
  · exact l14b_mem_line _ _ _ (7/9) (by rw [l14b_lineMap]; ext i; fin_cases i <;> simp [X₁, l14T] <;> norm_num)
  · exact l14b_mem_mk' _ _ _ (2/3) (by simp [X₁, d₁]; norm_num) (by simp [X₁, d₁]; norm_num)
  · exact l14b_mem_line _ _ _ (-1/3) (by rw [l14b_lineMap]; ext i; fin_cases i <;> simp [Y₁, l14T] <;> norm_num)
  · exact l14b_mem_mk' _ _ _ 2 (by simp [Y₁, d₂]; norm_num) (by simp [Y₁, d₂]; norm_num)
  · exact l14b_mem_line _ _ _ 2 (by rw [l14b_lineMap]; ext i; fin_cases i <;> simp [X₂, l14T] <;> norm_num)
  · exact l14b_mem_mk' _ _ _ (-2) (by simp [X₂, d₁]; norm_num) (by simp [X₂, d₁]; norm_num)
  · exact l14b_mem_line _ _ _ (4/7) (by rw [l14b_lineMap]; ext i; fin_cases i <;> simp [Y₂, l14T] <;> norm_num)
  · exact l14b_mem_mk' _ _ _ (-2/7) (by simp [Y₂, d₂]; norm_num) (by simp [Y₂, d₂]; norm_num)
  · exact l14b_mem_line _ _ _ (1/8) (by rw [l14b_lineMap]; ext i; fin_cases i <;> simp [X₃, l14T] <;> norm_num)
  · exact l14b_mem_mk' _ _ _ (-1/2) (by simp [X₃, d₁]; norm_num) (by simp [X₃, d₁])
  · exact l14b_mem_line _ _ _ (3/4) (by rw [l14b_lineMap]; ext i; fin_cases i <;> simp [Y₃, l14T] <;> norm_num)
  · exact l14b_mem_mk' _ _ _ 1 (by simp [Y₃, d₂]; norm_num) (by simp [Y₃, d₂])

end Brocard
