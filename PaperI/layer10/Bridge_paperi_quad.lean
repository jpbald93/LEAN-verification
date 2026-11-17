import Quadrilaterals.Frame
import Quadrilaterals.Bridges

/-!
# Layer 10: definition bridges

Each locally defined notion is tied to the standard Mathlib notion it stands for.

* `cross_eq_det`, `cross_eq_areaForm`, `abs_cross_eq_abs_areaForm`, `cx_eq_repr`, `cy_eq_repr`:
  the coordinates are `OrthonormalBasis.repr`, and `cross` is the determinant `Basis.det` and the
  area form `Orientation.areaForm` of the orientation of `b` (up to sign for any orientation).
* `triArea_eq_areaForm`, `quadArea_eq_areaForm`: `triArea` is half the absolute area form
  (the shoelace formula), and `quadArea` is the sum of the two shoelace triangle areas;
  `ConvexQuad.quadArea_eq_areaForm`: for a convex quadrilateral it is `|ω(C − A, D − B)| / 2`.
* `convexQuad_iff_sOppSide`: `ConvexQuad A B C D` holds iff `B, D` lie strictly on opposite sides
  (Mathlib's `AffineSubspace.SOppSide`) of the line `AC` and `A, C` strictly on opposite sides
  of the line `BD`.
* `ConvexQuad.quadSign_eq_sign`: for a convex quadrilateral `quadSign` is `Real.sign` of the area
  form `ω(C − A, D − B)`.
* `cospherical_iff_concyclic`, `cospherical_four_iff_exists_sphere`: the cyclic predicate
  (`Cospherical`) is Mathlib's `Concyclic` in the plane, and means the four vertices lie on one
  `EuclideanGeometry.Sphere`.
* `infDist_eq_iff_isTangent`, `isIncircle_iff_isTangent`, `tangential_iff_exists_sphere`: the
  `Metric.infDist` conditions of `IsIncircle` say exactly that the sphere `⟨I, r⟩` is tangent
  (`Sphere.IsTangent`) to the four side lines.
-/

open EuclideanGeometry Module
open scoped RealInnerProductSpace Real

namespace Quadrilaterals

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

theorem cross_eq_areaForm [Fact (finrank ℝ V = 2)] (b : OrthonormalBasis (Fin 2) ℝ V) (u v : V) :
    cross b u v = b.toBasis.orientation.areaForm u v := by
  rw [Orientation.areaForm_to_volumeForm, Orientation.volumeForm_robust _ b rfl, Basis.det_apply,
    Matrix.det_fin_two]
  simp [Basis.toMatrix_apply, cross, cx, cy, OrthonormalBasis.repr_apply_apply]
  ring

theorem abs_cross_eq_abs_areaForm [Fact (finrank ℝ V = 2)] (b : OrthonormalBasis (Fin 2) ℝ V)
    (o : Orientation ℝ V (Fin 2)) (u v : V) : |cross b u v| = |o.areaForm u v| := by
  rw [Orientation.areaForm_to_volumeForm, o.volumeForm_robust' b, Basis.det_apply,
    Matrix.det_fin_two]
  simp only [Basis.toMatrix_apply, cross, cx, cy, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf

theorem triArea_eq_areaForm [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) (A B C : P) :
    triArea A B C = |o.areaForm (B -ᵥ A) (C -ᵥ A)| / 2 := by
  obtain ⟨b⟩ := exists_basis (V := V)
  rw [triArea_eq b, abs_cross_eq_abs_areaForm b o]

theorem quadArea_eq_areaForm [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) (A B C D : P) :
    quadArea A B C D = |o.areaForm (B -ᵥ A) (C -ᵥ A)| / 2 + |o.areaForm (C -ᵥ A) (D -ᵥ A)| / 2 := by
  rw [quadArea, triArea_eq_areaForm o, triArea_eq_areaForm o]

theorem ConvexQuad.quadArea_eq_areaForm [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    {A B C D : P} (h : ConvexQuad A B C D) :
    quadArea A B C D = |o.areaForm (C -ᵥ A) (D -ᵥ B)| / 2 := by
  obtain ⟨b, X, t, u, p1, p2, q1, q2, -, -, hF⟩ := convex_frame h
  obtain ⟨c1, -, -, -, -, -, -, -, c9, -⟩ := hF.crosses
  obtain ⟨ht0, ht1, hu0, hu1, hk, hA1, hA2, hC1, hC2, hB1, hB2, hD1, hD2⟩ := hF
  rw [quadArea, triArea_eq b, triArea_eq b, c1, c9, ← abs_cross_eq_abs_areaForm b o, cross,
    cx_vsub b X, cy_vsub b X, cx_vsub b X, cy_vsub b X, hA1, hA2, hB1, hB2, hC1, hC2, hD1, hD2,
    abs_of_pos (by positivity), abs_of_pos (mul_pos (by linarith) hk), abs_of_pos (by nlinarith)]
  ring

theorem cx_eq_repr (b : OrthonormalBasis (Fin 2) ℝ V) (v : V) : cx b v = b.repr v 0 :=
  (b.repr_apply_apply v 0).symm

theorem cy_eq_repr (b : OrthonormalBasis (Fin 2) ℝ V) (v : V) : cy b v = b.repr v 1 :=
  (b.repr_apply_apply v 1).symm

theorem cross_eq_det (b : OrthonormalBasis (Fin 2) ℝ V) (u v : V) :
    cross b u v = b.toBasis.det ![u, v] := by
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply, cross, cx, cy, OrthonormalBasis.repr_apply_apply]
  ring

theorem ConvexQuad.quadSign_eq_sign [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    {A B C D : P} (h : ConvexQuad A B C D) :
    quadSign o A B C D = Real.sign (o.areaForm (C -ᵥ A) (D -ᵥ B)) := by
  obtain ⟨b, X, t, u, p1, p2, q1, q2, -, -, hF⟩ := convex_frame h
  obtain ⟨ht0, ht1, hu0, hu1, hk, hA1, hA2, hC1, hC2, hB1, hB2, hD1, hD2⟩ := hF
  have hc : cross b (C -ᵥ A) (D -ᵥ B) = p1 * q2 - p2 * q1 := by
    rw [cross, cx_vsub b X, cy_vsub b X, cx_vsub b X, cy_vsub b X, hA1, hA2, hB1, hB2, hC1, hC2,
      hD1, hD2]
    ring
  have hne : o.areaForm (C -ᵥ A) (D -ᵥ B) ≠ 0 := by
    intro h0
    have := abs_cross_eq_abs_areaForm b o (C -ᵥ A) (D -ᵥ B)
    rw [h0, abs_zero, hc, abs_eq_zero] at this
    linarith
  unfold quadSign
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · rw [if_neg (not_lt.2 hneg.le), Real.sign_of_neg hneg]
  · rw [if_pos hpos, Real.sign_of_pos hpos]

theorem convexQuad_iff_sOppSide {A B C D : P} :
    ConvexQuad A B C D ↔ line[ℝ, A, C].SOppSide B D ∧ line[ℝ, B, D].SOppSide A C := by
  constructor
  · rintro ⟨⟨X, hAXC, hBXD⟩, hncol⟩
    have hAC : A ≠ C := hAXC.left_ne_right
    have hXAC : X ∈ line[ℝ, A, C] := hAXC.wbtw.mem_affineSpan
    have hXBD : X ∈ line[ℝ, B, D] := hBXD.wbtw.mem_affineSpan
    have hB : B ∉ line[ℝ, A, C] := fun hB => hncol (by
      have := collinear_insert_of_mem_affineSpan_pair hB
      have e : ({B, A, C} : Set P) = {A, B, C} := Set.insert_comm _ _ _
      rwa [e] at this)
    have hD : D ∉ line[ℝ, A, C] := fun hD =>
      hB (affineSpan_pair_le_of_mem_of_mem hD hXAC hBXD.left_mem_affineSpan)
    have hA : A ∉ line[ℝ, B, D] := fun hA => by
      have hC : C ∈ line[ℝ, B, D] :=
        affineSpan_pair_le_of_mem_of_mem hA hXBD hAXC.right_mem_affineSpan
      apply hncol
      have := collinear_insert_insert_of_mem_affineSpan_pair hA hC
      exact this.subset (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    have hC : C ∉ line[ℝ, B, D] := fun hC =>
      hA (affineSpan_pair_le_of_mem_of_mem hC hXBD hAXC.left_mem_affineSpan)
    exact ⟨hBXD.sOppSide_of_notMem_of_mem hB hXAC, hAXC.sOppSide_of_notMem_of_mem hA hXBD⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨p, hp, hBpD⟩ := h1.exists_sbtw
    obtain ⟨q, hq, hAqC⟩ := h2.exists_sbtw
    have hqAC : q ∈ line[ℝ, A, C] := hAqC.wbtw.mem_affineSpan
    have hpBD : p ∈ line[ℝ, B, D] := hBpD.wbtw.mem_affineSpan
    have hAC : A ≠ C := hAqC.left_ne_right
    have hB := h1.left_notMem
    have hpq : p = q := by
      by_contra hne
      have hcol := collinear_insert_insert_of_mem_affineSpan_pair hpBD hq
      have hBpq : B ∈ line[ℝ, p, q] :=
        hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hne
      exact hB (affineSpan_pair_le_of_mem_of_mem hp hqAC hBpq)
    subst hpq
    refine ⟨⟨p, hAqC, hBpD⟩, fun hcol => hB ?_⟩
    exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAC

theorem cospherical_iff_concyclic [Fact (finrank ℝ V = 2)] (s : Set P) :
    Cospherical s ↔ Concyclic s :=
  ⟨fun h => ⟨h, coplanar_of_fact_finrank_eq_two s⟩, fun h => h.1⟩

theorem cospherical_four_iff_exists_sphere (A B C D : P) :
    Cospherical ({A, B, C, D} : Set P) ↔ ∃ s : Sphere P, A ∈ s ∧ B ∈ s ∧ C ∈ s ∧ D ∈ s := by
  rw [cospherical_iff_exists_sphere]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Sphere.mem_coe]

theorem infDist_eq_iff_isTangent [FiniteDimensional ℝ V] (I X Y : P) (r : ℝ) :
    Metric.infDist I (line[ℝ, X, Y] : Set P) = r ↔ (⟨I, r⟩ : Sphere P).IsTangent line[ℝ, X, Y] :=
  Sphere.infDist_eq_radius_iff_isTangent (s := ⟨I, r⟩)

theorem isIncircle_iff_isTangent [FiniteDimensional ℝ V] (A B C D I : P) (r : ℝ) :
    IsIncircle A B C D I r ↔ 0 < r ∧
      (⟨I, r⟩ : Sphere P).IsTangent line[ℝ, A, B] ∧ (⟨I, r⟩ : Sphere P).IsTangent line[ℝ, B, C] ∧
      (⟨I, r⟩ : Sphere P).IsTangent line[ℝ, C, D] ∧ (⟨I, r⟩ : Sphere P).IsTangent line[ℝ, D, A] ∧
      line[ℝ, A, B].SSameSide I C ∧ line[ℝ, B, C].SSameSide I D ∧
      line[ℝ, C, D].SSameSide I A ∧ line[ℝ, D, A].SSameSide I B := by
  simp only [IsIncircle, infDist_eq_iff_isTangent]

theorem tangential_iff_exists_sphere [FiniteDimensional ℝ V] (A B C D : P) :
    Tangential A B C D ↔ ∃ s : Sphere P, 0 < s.radius ∧
      s.IsTangent line[ℝ, A, B] ∧ s.IsTangent line[ℝ, B, C] ∧
      s.IsTangent line[ℝ, C, D] ∧ s.IsTangent line[ℝ, D, A] ∧
      line[ℝ, A, B].SSameSide s.center C ∧ line[ℝ, B, C].SSameSide s.center D ∧
      line[ℝ, C, D].SSameSide s.center A ∧ line[ℝ, D, A].SSameSide s.center B := by
  constructor
  · rintro ⟨I, r, h⟩
    exact ⟨⟨I, r⟩, (isIncircle_iff_isTangent A B C D I r).1 h⟩
  · rintro ⟨⟨I, r⟩, h⟩
    exact ⟨I, r, (isIncircle_iff_isTangent A B C D I r).2 h⟩

end Quadrilaterals
