import CircleSystems.Coaxal
import CircleSystems.Johnson
import CircleSystems.SimsonSteiner

/-!
# Layer 10: definition bridges

Each locally defined notion is tied to the Mathlib notion it stands for.

* `powPt_eq_power`: `powPt P O R` is Mathlib's `Sphere.power` of `P` for the sphere `⟨O, R⟩`
  (definitionally the same expression `dist P O ^ 2 - R ^ 2`); `powPt_eq_zero_iff_mem_sphere`,
  `mul_dist_eq_abs_powPt` (the chord form of the power, via `Sphere.mul_dist_eq_abs_power`).
* `mem_radicalAxis_iff_power`: the radical axis is the set of equal `Sphere.power`;
  `sphere_inter_subset_radicalAxis`: common points of two `Sphere`s lie on it;
  `radicalAxis_eq_affineSubspace`: for distinct centres it is an `AffineSubspace` with direction
  `(ℝ ∙ (O₁ − O₂))ᗮ`.
* `pencilCenter_eq_lineMap`: the pencil centre is `AffineMap.lineMap O₁ O₂ t`.
* `isOrthogonal_iff_angle`: `IsOrthogonal` is a common point of the two `Sphere`s at which the
  unoriented angle `∠ O₁ X O₂` is `π / 2`.
* `reflection_eq_pointReflection`: Mathlib's `reflection` in a line is the point reflection of `P`
  in its foot `orthogonalProjection`.
* `johnson_center_eq_pointReflection`: the Johnson centre `O₁ + O₂ + O₃ − 2H` is the reflection of
  `H` in `M = (O₁ + O₂ + O₃ − H) / 2` (`Equiv.pointReflection`);
  `johnson_center_eq_orthocenter`: for a Mathlib `Affine.Triangle`, the point
  `A + B + C − 2 O` used by the Johnson / Steiner statements is `Affine.Triangle.orthocenter`.
* `cx_eq_repr`, `cy_eq_repr`, `cross_eq_det`, `cross_eq_areaForm`: the coordinates are
  `OrthonormalBasis.repr`, and `cross` is the determinant `Basis.det` / the area form of the
  orientation of `b`.
-/

open Module EuclideanGeometry
open scoped RealInnerProductSpace

namespace CircleSystems

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
theorem powPt_eq_power (P O : V) (R : ℝ) : powPt P O R = (⟨O, R⟩ : Sphere V).power P := rfl

omit [InnerProductSpace ℝ V] in
theorem powPt_eq_zero_iff_mem_sphere {P O : V} {R : ℝ} (hR : 0 ≤ R) :
    powPt P O R = 0 ↔ P ∈ (⟨O, R⟩ : Sphere V) :=
  Sphere.power_eq_zero_iff_mem_sphere (s := ⟨O, R⟩) hR

theorem mul_dist_eq_abs_powPt {P X Y O : V} {R : ℝ} (hP : P ∈ line[ℝ, X, Y])
    (hX : dist X O = R) (hY : dist Y O = R) : dist P X * dist P Y = |powPt P O R| :=
  Sphere.mul_dist_eq_abs_power (s := ⟨O, R⟩) hP (EuclideanGeometry.mem_sphere.2 hX) (EuclideanGeometry.mem_sphere.2 hY)

omit [InnerProductSpace ℝ V] in
theorem mem_radicalAxis_iff_power {P O₁ O₂ : V} {R₁ R₂ : ℝ} :
    P ∈ radicalAxis O₁ R₁ O₂ R₂ ↔ (⟨O₁, R₁⟩ : Sphere V).power P = (⟨O₂, R₂⟩ : Sphere V).power P :=
  Iff.rfl

omit [InnerProductSpace ℝ V] in
theorem sphere_inter_subset_radicalAxis (s₁ s₂ : Sphere V) :
    (s₁ : Set V) ∩ s₂ ⊆ radicalAxis s₁.center s₁.radius s₂.center s₂.radius := by
  rintro X ⟨h₁, h₂⟩
  exact mem_radicalAxis_of_mem_circles (EuclideanGeometry.mem_sphere.1 h₁) (EuclideanGeometry.mem_sphere.1 h₂)

theorem radicalAxis_eq_affineSubspace {O₁ O₂ : V} (R₁ R₂ : ℝ) (h : O₁ ≠ O₂) :
    ∃ L : AffineSubspace ℝ V, (L : Set V) = radicalAxis O₁ R₁ O₂ R₂ ∧
      L.direction = (ℝ ∙ (O₁ - O₂))ᗮ :=
  ⟨_, (radicalAxis_eq_mk' R₁ R₂ h).symm, AffineSubspace.direction_mk' _ _⟩

theorem pencilCenter_eq_lineMap (O₁ O₂ : V) (t : ℝ) :
    pencilCenter O₁ O₂ t = AffineMap.lineMap O₁ O₂ t := by
  rw [AffineMap.lineMap_apply_module, pencilCenter]

theorem isOrthogonal_iff_angle (O₁ O₂ : V) (R₁ R₂ : ℝ) :
    IsOrthogonal O₁ R₁ O₂ R₂ ↔ ∃ X : V, X ∈ (⟨O₁, R₁⟩ : Sphere V) ∧ X ∈ (⟨O₂, R₂⟩ : Sphere V) ∧
      ∠ O₁ X O₂ = Real.pi / 2 := by
  simp only [IsOrthogonal, EuclideanGeometry.mem_sphere, EuclideanGeometry.angle, vsub_eq_sub,
    ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  refine exists_congr fun X => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [← inner_neg_neg, neg_sub, neg_sub]

theorem reflection_eq_pointReflection (X Y P : V) :
    reflection line[ℝ, X, Y] P =
      Equiv.pointReflection (orthogonalProjection line[ℝ, X, Y] P : V) P := by
  rw [reflection_eq, Equiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add, two_smul]
  abel

theorem johnson_center_eq_pointReflection (H O₁ O₂ O₃ : V) :
    O₁ + O₂ + O₃ - (2 : ℝ) • H = Equiv.pointReflection ((1 / 2 : ℝ) • (O₁ + O₂ + O₃ - H)) H := by
  rw [Equiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add]
  module

theorem johnson_center_eq_orthocenter (t : Affine.Triangle ℝ V) :
    t.points 0 + t.points 1 + t.points 2 - (2 : ℝ) • t.circumcenter = t.orthocenter := by
  have hs := t.orthocenter_vsub_circumcenter_eq_sum_vsub
  rw [Fin.sum_univ_three] at hs
  simp only [vsub_eq_sub] at hs
  have hH : t.orthocenter = t.points 0 + t.points 1 + t.points 2 - (2 : ℝ) • t.circumcenter := by
    rw [← sub_eq_zero, ← sub_eq_zero.2 hs, two_smul]
    abel
  exact hH.symm

theorem cx_eq_repr (b : OrthonormalBasis (Fin 2) ℝ V) (v : V) : cx b v = b.repr v 0 :=
  (b.repr_apply_apply v 0).symm

theorem cy_eq_repr (b : OrthonormalBasis (Fin 2) ℝ V) (v : V) : cy b v = b.repr v 1 :=
  (b.repr_apply_apply v 1).symm

theorem cross_eq_det (b : OrthonormalBasis (Fin 2) ℝ V) (u v : V) :
    cross b u v = b.toBasis.det ![u, v] := by
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply, cross, cx, cy, OrthonormalBasis.repr_apply_apply]
  ring

theorem cross_eq_areaForm [Fact (finrank ℝ V = 2)] (b : OrthonormalBasis (Fin 2) ℝ V) (u v : V) :
    cross b u v = b.toBasis.orientation.areaForm u v := by
  rw [Orientation.areaForm_to_volumeForm, Orientation.volumeForm_robust _ b rfl, cross_eq_det]

end CircleSystems
