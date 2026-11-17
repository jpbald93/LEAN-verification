import Quadrilaterals

/-!
# Layer 15 comparison (J), quadrilaterals: classical_Q1..Q8 vs the `Quadrilaterals` library.
EXTENDED copy (`L15_compare_ext.lean`): area bridge from `area_bridge.lean` spliced in; Q1/Q2 proved.
Classical definitions copied verbatim from PaperIClassical.lean (sha256 prefix 1c595a90ccb3925a),
namespace renamed to `L15Q`.
-/

/-! ## Area bridge (spliced verbatim from `~/l13_quad/scratch/area_bridge.lean`)
Lebesgue measure of the convex hull = `Quadrilaterals.quadArea`. Kept in its own section so its
`open`s do not leak into the comparison below. -/

noncomputable section AreaBridgeSplice

open EuclideanGeometry Module MeasureTheory Set
open scoped RealInnerProductSpace Real

namespace Quadrilaterals.AreaBridge

open Quadrilaterals

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## Convex-geometry helpers -/

/-- A signed half-plane containing `S` contains its convex hull. -/
theorem hull_sub_halfplane (b : OrthonormalBasis (Fin 2) ℝ V) (s : ℝ) {X Y : V} {S : Set V}
    (h : ∀ Z ∈ S, 0 ≤ s * cross b (Y - X) (Z - X)) :
    convexHull ℝ S ⊆ {Z | 0 ≤ s * cross b (Y - X) (Z - X)} := by
  refine convexHull_min h ?_
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have e : a • x + c • y - X = a • (x - X) + c • (y - X) := by
    linear_combination (norm := module) hac • X
  rw [e, cross_add_right, cross_smul_right, cross_smul_right,
    show s * (a * cross b (Y - X) (x - X) + c * cross b (Y - X) (y - X)) =
      a * (s * cross b (Y - X) (x - X)) + c * (s * cross b (Y - X) (y - X)) by ring]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hc hy)

/-- A point weakly inside the three sides of a positively oriented triangle is in its hull. -/
theorem mem_hull_tri (b : OrthonormalBasis (Fin 2) ℝ V) {X Y W Z : V}
    (hk : 0 < cross b (Y - X) (W - X)) (h1 : 0 ≤ cross b (Y - X) (Z - X))
    (h2 : 0 ≤ cross b (W - Y) (Z - Y)) (h3 : 0 ≤ cross b (X - W) (Z - W)) :
    Z ∈ convexHull ℝ ({X, Y, W} : Set V) := by
  set k := cross b (Y - X) (W - X)
  set s := cross b (X - W) (Z - W)
  set t := cross b (Y - X) (Z - X)
  have hsum : cross b (W - Y) (Z - Y) = k - s - t := by
    simp only [k, s, t, cross, cx_sub, cy_sub]; ring
  have hZ : Z = ((k - s - t) / k) • X + (s / k) • Y + (t / k) • W := by
    apply ext_coord b
    · simp only [cx_add, cx_smul]
      field_simp
      simp only [k, s, t, cross, cx_sub, cy_sub]; ring
    · simp only [cy_add, cy_smul]
      field_simp
      simp only [k, s, t, cross, cx_sub, cy_sub]; ring
  have := (convex_convexHull ℝ ({X, Y, W} : Set V)).sum_mem (t := Finset.univ)
    (w := ![(k - s - t) / k, s / k, t / k]) (z := ![X, Y, W])
    (by intro i _; fin_cases i <;> simp <;> [exact div_nonneg (by linarith [hsum ▸ h2]) hk.le;
      exact div_nonneg h3 hk.le; exact div_nonneg h1 hk.le])
    (by simp [Fin.sum_univ_three]; field_simp; ring)
    (by intro i _; fin_cases i <;> apply subset_convexHull <;> simp)
  simpa [Fin.sum_univ_three, ← hZ] using this

/-- `a • u + c • v` with `a, c ≥ 0`, `a + c ≤ 1` lies in the triangle `0, u, v`. -/
theorem smul_add_mem_hull {u v : V} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : a + c ≤ 1) :
    a • u + c • v ∈ convexHull ℝ ({0, u, v} : Set V) := by
  have := (convex_convexHull ℝ ({0, u, v} : Set V)).sum_mem (t := Finset.univ)
    (w := ![1 - a - c, a, c]) (z := ![0, u, v])
    (by intro i _; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_three]; ring)
    (by intro i _; fin_cases i <;> apply subset_convexHull <;> simp)
  simpa [Fin.sum_univ_three] using this

theorem mem_par_iff (u v z : V) :
    z ∈ parallelepiped ![u, v] ↔
      ∃ a c : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ c ∧ c ≤ 1 ∧ z = a • u + c • v := by
  rw [mem_parallelepiped_iff]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨t 0, t 1, h0 0, h1 0, h0 1, h1 1, by simp [Fin.sum_univ_two]⟩
  · rintro ⟨a, c, ha0, ha1, hc0, hc1, rfl⟩
    refine ⟨![a, c], ⟨?_, ?_⟩, by simp [Fin.sum_univ_two]⟩ <;> intro i <;> fin_cases i <;>
      simp [ha0, ha1, hc0, hc1]

/-- The parallelogram on `u, v` is the triangle `0, u, v` together with its point reflection
through the centre `(u + v) / 2`. -/
theorem parallelepiped_eq_union (u v : V) :
    parallelepiped ![u, v] = convexHull ℝ ({0, u, v} : Set V) ∪
      (fun z => (u + v) - z) ⁻¹' convexHull ℝ ({0, u, v} : Set V) := by
  have hsub : convexHull ℝ ({0, u, v} : Set V) ⊆ parallelepiped ![u, v] := by
    refine convexHull_min ?_ (convex_parallelepiped _)
    simp only [insert_subset_iff, singleton_subset_iff, mem_par_iff]
    exact ⟨⟨0, 0, le_rfl, zero_le_one, le_rfl, zero_le_one, by simp⟩,
      ⟨1, 0, zero_le_one, le_rfl, le_rfl, zero_le_one, by simp⟩,
      ⟨0, 1, le_rfl, zero_le_one, zero_le_one, le_rfl, by simp⟩⟩
  ext z
  simp only [mem_union, mem_preimage]
  constructor
  · rw [mem_par_iff]
    rintro ⟨a, c, ha0, ha1, hc0, hc1, rfl⟩
    by_cases hs : a + c ≤ 1
    · exact Or.inl (smul_add_mem_hull ha0 hc0 hs)
    · right
      have := smul_add_mem_hull (u := u) (v := v) (a := 1 - a) (c := 1 - c) (by linarith)
        (by linarith) (by linarith)
      convert this using 1; module
  · rintro (h | h)
    · exact hsub h
    · obtain ⟨a, c, ha0, ha1, hc0, hc1, he⟩ := (mem_par_iff _ _ _).1 (hsub h)
      refine (mem_par_iff _ _ _).2 ⟨1 - a, 1 - c, by linarith, by linarith, by linarith,
        by linarith, ?_⟩
      have : z = (u + v) - (a • u + c • v) := by rw [← he]; abel
      rw [this]; module

/-! ## Measure theory -/

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem isCompact_hull (S : Set V) (hS : S.Finite) : IsCompact (convexHull ℝ S) :=
  hS.isCompact_convexHull ℝ

/-- Volume of the parallelogram spanned by `u, v` is `|u × v|`. -/
theorem volume_parallelogram (b : OrthonormalBasis (Fin 2) ℝ V) (u v : V) :
    volume (parallelepiped ![u, v]) = ENNReal.ofReal |cross b u v| := by
  rw [← b.addHaar_eq_volume, Measure.addHaar_parallelepiped, Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, cross, cx, cy, mul_comm]

/-- Twice the volume of the triangle `0, u, v` is `|u × v|`. -/
theorem two_mul_volume_tri0 (b : OrthonormalBasis (Fin 2) ℝ V) [Fact (finrank ℝ V = 2)]
    (u v : V) : 2 * volume (convexHull ℝ ({0, u, v} : Set V)) = ENNReal.ofReal |cross b u v| := by
  set T := convexHull ℝ ({0, u, v} : Set V) with hT
  by_cases hk : cross b u v = 0
  · -- degenerate: the triangle lies in a proper affine subspace
    have hcol : Collinear ℝ ({0, u, v} : Set V) :=
      collinear_of_cross_eq_zero b (by simpa using hk)
    have hne : affineSpan ℝ ({0, u, v} : Set V) ≠ ⊤ := by
      intro htop
      have h1 := (collinear_iff_finrank_le_one).1 hcol
      rw [← direction_affineSpan, htop, AffineSubspace.direction_top, finrank_top,
        (Fact.out : finrank ℝ V = 2)] at h1
      norm_num at h1
    have h0 : volume T = 0 :=
      measure_mono_null (convexHull_subset_affineSpan _)
        (Measure.addHaar_affineSubspace _ _ hne)
    rw [h0, hk]; simp
  · set S := (fun z => (u + v) - z) ⁻¹' T with hS
    have hTc : IsCompact T := isCompact_hull _ (by simp)
    have hSc : IsClosed S := hTc.isClosed.preimage (by fun_prop)
    have hSvol : volume S = volume T := by
      have : S = Neg.neg ⁻¹' ((fun h => (u + v) + h) ⁻¹' T) := by
        ext z; simp [hS, sub_eq_add_neg]
      rw [this, Measure.measure_preimage_neg, measure_preimage_add]
    have huv : u ≠ v := by rintro rfl; exact hk (cross_self b u)
    -- the two halves meet only on the line through `u` and `v`
    have hpos : ∀ z ∈ T, 0 ≤ cross b u v * cross b (v - u) (z - u) := by
      refine hull_sub_halfplane b _ ?_
      simp only [mem_insert_iff, mem_singleton_iff]
      rintro Z (rfl | rfl | rfl)
      · have : cross b (v - u) (0 - u) = cross b u v := by simp only [cross, cx_sub, cy_sub, cx_zero, cy_zero]; ring
        rw [this]; nlinarith [sq_nonneg (cross b u v)]
      · simp
      · simp [cross_self]
    have hinter : T ∩ S ⊆ (line[ℝ, u, v] : Set V) := by
      rintro z ⟨hz1, hz2⟩
      have p1 := hpos z hz1
      have p2 := hpos _ hz2
      have e : cross b (v - u) ((u + v) - z - u) = -cross b (v - u) (z - u) := by
        simp only [cross, cx_sub, cy_sub, cx_add, cy_add]; ring
      rw [e] at p2
      have : cross b u v * cross b (v - u) (z - u) = 0 := by linarith
      have hz0 : cross b (v - u) (z - u) = 0 := (mul_eq_zero.1 this).resolve_left hk
      exact (mem_line_iff b huv).2 (by simpa using hz0)
    have hline : line[ℝ, u, v] ≠ ⊤ := by
      intro htop
      have h0 : (0 : V) ∈ line[ℝ, u, v] := by rw [htop]; trivial
      have := (mem_line_iff b huv).1 h0
      have e : cross b (v -ᵥ u) (0 -ᵥ u) = cross b u v := by
        simp only [vsub_eq_sub, cross, cx_sub, cy_sub, cx_zero, cy_zero]; ring
      exact hk (e ▸ this)
    have hnull : volume (T ∩ S) = 0 :=
      measure_mono_null hinter (Measure.addHaar_affineSubspace _ _ hline)
    have hu := measure_union_add_inter₀ (μ := volume) T hSc.measurableSet.nullMeasurableSet
    rw [← parallelepiped_eq_union, volume_parallelogram b, hnull, add_zero, hSvol] at hu
    rw [hu, two_mul]

/-- **Triangle area bridge.** The Lebesgue measure of the convex hull of any three points of a
Euclidean plane equals `Quadrilaterals.triArea`. -/
theorem volume_convexHull_triangle [Fact (finrank ℝ V = 2)] (A B C : V) :
    (volume (convexHull ℝ ({A, B, C} : Set V))).toReal = triArea A B C := by
  obtain ⟨b⟩ := exists_basis (V := V)
  have himg : (fun z => A + z) '' convexHull ℝ ({0, B - A, C - A} : Set V) =
      convexHull ℝ ({A, B, C} : Set V) := by
    have := AffineMap.image_convexHull (AffineEquiv.constVAdd ℝ V A).toAffineMap
      ({0, B - A, C - A} : Set V)
    simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, vadd_eq_add] at this
    rw [this]; congr 1; simp [Set.image_insert_eq]
  have hvol : volume (convexHull ℝ ({A, B, C} : Set V)) =
      volume (convexHull ℝ ({0, B - A, C - A} : Set V)) := by
    rw [← himg, image_add_left, measure_preimage_add]
  have h2 := congrArg ENNReal.toReal (two_mul_volume_tri0 b (B - A) (C - A))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at h2
  rw [hvol, triArea_eq b]
  simp only [vsub_eq_sub]
  norm_num at h2
  linarith

/-- **Quadrilateral area bridge.** For a convex quadrilateral (library `ConvexQuad`) the Lebesgue
measure of the convex hull of the four vertices equals `Quadrilaterals.quadArea`. -/
theorem volume_convexHull_quad [Fact (finrank ℝ V = 2)] {A B C D : V}
    (hconv : ConvexQuad A B C D) :
    (volume (convexHull ℝ ({A, B, C, D} : Set V))).toReal = quadArea A B C D := by
  obtain ⟨b, X, t, u, p1, p2, q1, q2, -, -, hF⟩ := convex_frame hconv
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9⟩ := hF.pos
  simp only [vsub_eq_sub] at P1 P2 P3 P4 P5 P6 P7 P8 P9
  set H := convexHull ℝ ({A, B, C, D} : Set V) with hH
  set T1 := convexHull ℝ ({A, B, C} : Set V) with hT1
  set T2 := convexHull ℝ ({A, C, D} : Set V) with hT2
  -- the four side half-planes contain the hull
  have sAB := hull_sub_halfplane b 1 (X := A) (Y := B) (S := {A, B, C, D}) (by
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro Z (rfl | rfl | rfl | rfl) <;> simp only [one_mul, sub_self, cross_zero_right,
      cross_self, le_refl] <;> linarith)
  have sBC := hull_sub_halfplane b 1 (X := B) (Y := C) (S := {A, B, C, D}) (by
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro Z (rfl | rfl | rfl | rfl) <;> simp only [one_mul, sub_self, cross_zero_right,
      cross_self, le_refl] <;> linarith)
  have sCD := hull_sub_halfplane b 1 (X := C) (Y := D) (S := {A, B, C, D}) (by
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro Z (rfl | rfl | rfl | rfl) <;> simp only [one_mul, sub_self, cross_zero_right,
      cross_self, le_refl] <;> linarith)
  have sDA := hull_sub_halfplane b 1 (X := D) (Y := A) (S := {A, B, C, D}) (by
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro Z (rfl | rfl | rfl | rfl) <;> simp only [one_mul, sub_self, cross_zero_right,
      cross_self, le_refl] <;> linarith)
  have flip : ∀ z : V, cross b (A - C) (z - C) = -cross b (C - A) (z - A) := by
    intro z; simp only [cross, cx_sub, cy_sub]; ring
  -- the hull is the union of the two triangles cut off by the diagonal `AC`
  have hunion : H = T1 ∪ T2 := by
    apply le_antisymm
    · intro z hz
      have hab := sAB hz; have hbc := sBC hz; have hcd := sCD hz; have hda := sDA hz
      simp only [mem_ofPred_eq, one_mul] at hab hbc hcd hda
      by_cases hs : 0 ≤ cross b (C - A) (z - A)
      · exact Or.inr (mem_hull_tri b P9 hs hcd hda)
      · push Not at hs
        exact Or.inl (mem_hull_tri b P1 hab hbc (by rw [flip]; linarith))
    · exact union_subset (convexHull_mono (by intro x; simp; tauto))
        (convexHull_mono (by intro x; simp; tauto))
  -- they meet only on the diagonal line `AC`
  have hAC : A ≠ C := by rintro rfl; simp at P1
  have hT1s := hull_sub_halfplane b 1 (X := C) (Y := A) (S := {A, B, C}) (by
    simp only [mem_insert_iff, mem_singleton_iff]
    have : cross b (A - C) (B - C) = cross b (C - B) (A - B) := by
      simp only [cross, cx_sub, cy_sub]; ring
    rintro Z (rfl | rfl | rfl) <;> simp only [one_mul, sub_self, cross_zero_right,
      cross_self, le_refl, this] ; linarith)
  have hT2s := hull_sub_halfplane b 1 (X := A) (Y := C) (S := {A, C, D}) (by
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro Z (rfl | rfl | rfl) <;> simp only [one_mul, sub_self, cross_zero_right,
      cross_self, le_refl] ; linarith)
  have hinter : T1 ∩ T2 ⊆ (line[ℝ, A, C] : Set V) := by
    rintro z ⟨h1, h2⟩
    have k1 := hT1s h1; have k2 := hT2s h2
    simp only [mem_ofPred_eq, one_mul, flip] at k1 k2
    exact (mem_line_iff b hAC).2 (by simp only [vsub_eq_sub]; linarith)
  have hline : line[ℝ, A, C] ≠ ⊤ := by
    intro htop
    have hB : B ∈ line[ℝ, A, C] := by rw [htop]; trivial
    have := (mem_line_iff b hAC).1 hB
    simp only [vsub_eq_sub] at this
    have e : cross b (C - A) (B - A) = -cross b (B - A) (C - A) := by
      simp only [cross]; ring
    rw [e] at this; linarith
  have hnull : volume (T1 ∩ T2) = 0 :=
    measure_mono_null hinter (Measure.addHaar_affineSubspace _ _ hline)
  have hc2 : IsCompact T2 := isCompact_hull _ (by simp)
  have hu := measure_union_add_inter₀ (μ := volume) T1 hc2.isClosed.measurableSet.nullMeasurableSet
  rw [hnull, add_zero] at hu
  rw [hunion, hu, ENNReal.toReal_add (isCompact_hull _ (by simp)).measure_lt_top.ne
    hc2.measure_lt_top.ne, volume_convexHull_triangle, volume_convexHull_triangle, quadArea]

end Quadrilaterals.AreaBridge

end AreaBridgeSplice

open EuclideanGeometry RealInnerProductSpace MeasureTheory

local notation "E2" => EuclideanSpace ℝ (Fin 2)

noncomputable section

namespace L15Q

/-- A (non-degenerate) convex quadrilateral `ABCD`: its diagonals `AC` and `BD` cross at a
point strictly inside both, and the vertices are not all on one line. -/
def ClassicalConvexQuad (A B C D : E2) : Prop :=
  (∃ X : E2, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∧ ¬ Collinear ℝ ({A, B, C} : Set E2)

/-- Area of the convex quadrilateral `ABCD` = Lebesgue measure of its convex hull. -/
def ClassicalQuadArea (A B C D : E2) : ℝ :=
  (volume (convexHull ℝ ({A, B, C, D} : Set E2))).toReal

/-- `O`, `r` are the centre and radius of an inscribed circle of the quadrilateral `ABCD`:
the circle is tangent to the four side lines (distance from `O` to each line is `r`) and its
centre lies inside the quadrilateral. -/
def ClassicalIsIncircle (A B C D O : E2) (r : ℝ) : Prop :=
  0 < r ∧ O ∈ interior (convexHull ℝ ({A, B, C, D} : Set E2)) ∧
    Metric.infDist O (line[ℝ, A, B] : Set E2) = r ∧
    Metric.infDist O (line[ℝ, B, C] : Set E2) = r ∧
    Metric.infDist O (line[ℝ, C, D] : Set E2) = r ∧
    Metric.infDist O (line[ℝ, D, A] : Set E2) = r

/-- The quadrilateral has an inscribed circle. -/
def ClassicalHasIncircle (A B C D : E2) : Prop :=
  ∃ O r, ClassicalIsIncircle A B C D O r

/-- `ABCD` is a parallelogram: `AB` and `DC` are equal as vectors. -/
def ClassicalParallelogram (A B C D : E2) : Prop :=
  B -ᵥ A = C -ᵥ D

/-- Twice the signed (shoelace) area of the quadrilateral `ABCD` in `ℂ`; positive iff the
quadrilateral is oriented counterclockwise. -/
def ClassicalSignedArea2 (A B C D : ℂ) : ℝ :=
  (starRingEnd ℂ A * B).im + (starRingEnd ℂ B * C).im + (starRingEnd ℂ C * D).im +
    (starRingEnd ℂ D * A).im

/-- Centre of the square erected on the side `XY`, on the right of the direction `X → Y`
(i.e. outward for a counterclockwise polygon). -/
def ClassicalOutwardSquareCentre (X Y : ℂ) : ℂ :=
  (X + Y) / 2 - Complex.I * (Y - X) / 2

instance instFactE2 : Fact (Module.finrank ℝ E2 = 2) := ⟨finrank_euclideanSpace_fin⟩

/-! ## Bridges -/

/-- The closed half-plane `{Z | 0 ≤ (Y − X) × (Z − X)}` is convex, so it contains the hull of any
set it contains. -/
theorem hull_sub_halfplane (b : OrthonormalBasis (Fin 2) ℝ E2) {X Y : E2} {S : Set E2}
    (h : ∀ Z ∈ S, 0 ≤ Quadrilaterals.cross b (Y -ᵥ X) (Z -ᵥ X)) :
    convexHull ℝ S ⊆ {Z | 0 ≤ Quadrilaterals.cross b (Y -ᵥ X) (Z -ᵥ X)} := by
  refine convexHull_min h ?_
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_ofPred_eq, vsub_eq_sub] at hx hy ⊢
  have e : a • x + c • y - X = a • (x - X) + c • (y - X) := by
    linear_combination (norm := module) hac • X
  rw [e, Quadrilaterals.cross_add_right, Quadrilaterals.cross_smul_right,
    Quadrilaterals.cross_smul_right]
  positivity

/-- Hull membership plus positive distance to the side line gives the strict same-side
condition of the library. -/
theorem sSameSide_of_hull (b : OrthonormalBasis (Fin 2) ℝ E2) {X Y W O : E2} {S : Set E2}
    {r : ℝ} (hXY : X ≠ Y) (hr : 0 < r) (hO : O ∈ convexHull ℝ S)
    (h : ∀ Z ∈ S, 0 ≤ Quadrilaterals.cross b (Y -ᵥ X) (Z -ᵥ X))
    (hW : 0 < Quadrilaterals.cross b (Y -ᵥ X) (W -ᵥ X))
    (hd : Metric.infDist O (line[ℝ, X, Y] : Set E2) = r) :
    line[ℝ, X, Y].SSameSide O W := by
  have c0 : 0 ≤ Quadrilaterals.cross b (Y -ᵥ X) (O -ᵥ X) := hull_sub_halfplane b h hO
  rw [Quadrilaterals.infDist_line b hXY] at hd
  have hne : Quadrilaterals.cross b (Y -ᵥ X) (O -ᵥ X) ≠ 0 := by
    intro h0; rw [h0, abs_zero, zero_div] at hd; exact hr.ne hd
  exact (Quadrilaterals.sSameSide_line_iff b hXY O W).2 (mul_pos (lt_of_le_of_ne c0 hne.symm) hW)

/-- A classical incircle of a classical convex quadrilateral is a library incircle. -/
theorem isIncircle_of_classical {A B C D O : E2} {r : ℝ} (hconv : ClassicalConvexQuad A B C D)
    (hin : ClassicalIsIncircle A B C D O r) : Quadrilaterals.IsIncircle A B C D O r := by
  obtain ⟨b, X, t, u, p1, p2, q1, q2, -, -, hF⟩ := Quadrilaterals.convex_frame hconv
  obtain ⟨hr, hO, d1, d2, d3, d4⟩ := hin
  have hH := interior_subset hO
  obtain ⟨n1, n2, n3, n4⟩ := hF.ne
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, -⟩ := hF.pos
  have z : ∀ (X : E2) (u : E2), Quadrilaterals.cross b u (X -ᵥ X) = 0 := by
    intro X u; rw [vsub_self, Quadrilaterals.cross_zero_right]
  have s : ∀ u : E2, Quadrilaterals.cross b u u = 0 := Quadrilaterals.cross_self b
  refine ⟨hr, d1, d2, d3, d4, ?_, ?_, ?_, ?_⟩
  · refine sSameSide_of_hull b n1 hr hH ?_ c1 d1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro Z (rfl | rfl | rfl | rfl)
    exacts [(z _ _).ge, (s _).ge, c1.le, c2.le]
  · refine sSameSide_of_hull b n2 hr hH ?_ c3 d2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro Z (rfl | rfl | rfl | rfl)
    exacts [c4.le, (z _ _).ge, (s _).ge, c3.le]
  · refine sSameSide_of_hull b n3 hr hH ?_ c5 d3
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro Z (rfl | rfl | rfl | rfl)
    exacts [c5.le, c6.le, (z _ _).ge, (s _).ge]
  · refine sSameSide_of_hull b n4 hr hH ?_ c7 d4
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro Z (rfl | rfl | rfl | rfl)
    exacts [(s _).ge, c7.le, c8.le, (z _ _).ge]

/-- The bridge in the classical vocabulary (from `area_bridge.lean`). -/
theorem classicalQuadArea_eq (A B C D : E2) (hconv : ClassicalConvexQuad A B C D) :
    ClassicalQuadArea A B C D = Quadrilaterals.quadArea A B C D :=
  Quadrilaterals.AreaBridge.volume_convexHull_quad hconv

/-! ## Q1, Q2: area -/

/-- Q1, the part proved by the library: Bretschneider with the area as the sum of the two
triangles cut off by the diagonal `AC`. -/
theorem cov_Q1_part (A B C D : E2) (hconv : ClassicalConvexQuad A B C D) :
    let a := dist A B; let b := dist B C; let c := dist C D; let d := dist D A
    let s := (a + b + c + d) / 2
    (dist A B * dist A C * Real.sin (∠ B A C) / 2 + dist A C * dist A D * Real.sin (∠ C A D) / 2)
        ^ 2 =
      (s - a) * (s - b) * (s - c) * (s - d) -
        a * b * c * d * Real.cos ((∠ A B C + ∠ C D A) / 2) ^ 2 :=
  Quadrilaterals.l14_bretschneider hconv.1 hconv.2

/-- Q1 reduced to the missing area identification. -/
theorem cov_Q1 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (harea : ClassicalQuadArea A B C D =
      dist A B * dist A C * Real.sin (∠ B A C) / 2 + dist A C * dist A D * Real.sin (∠ C A D) / 2) :
    let a := dist A B; let b := dist B C; let c := dist C D; let d := dist D A
    let s := (a + b + c + d) / 2
    ClassicalQuadArea A B C D ^ 2 =
      (s - a) * (s - b) * (s - c) * (s - d) -
        a * b * c * d * Real.cos ((∠ A B C + ∠ C D A) / 2) ^ 2 := by
  rw [harea]; exact cov_Q1_part A B C D hconv

theorem cov_Q2_part (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set E2)) :
    let a := dist A B; let b := dist B C; let c := dist C D; let d := dist D A
    let s := (a + b + c + d) / 2
    (dist A B * dist A C * Real.sin (∠ B A C) / 2 + dist A C * dist A D * Real.sin (∠ C A D) / 2)
        ^ 2 = (s - a) * (s - b) * (s - c) * (s - d) := by
  intro a b c d s
  have h1 := Quadrilaterals.l14_brahmagupta hconv.1 hconv.2 hcyc
  have h2 := Quadrilaterals.l14_bretschneider hconv.1 hconv.2
  have hx : 0 ≤ (s - a) * (s - b) * (s - c) * (s - d) := by
    have : 0 ≤ a * b * c * d * Real.cos ((∠ A B C + ∠ C D A) / 2) ^ 2 := by
      simp only [a, b, c, d]; positivity
    simp only [a, b, c, d, s] at this ⊢
    nlinarith [sq_nonneg (dist A B * dist A C * Real.sin (∠ B A C) / 2 +
      dist A C * dist A D * Real.sin (∠ C A D) / 2)]
  simp only [a, b, c, d, s] at hx ⊢
  rw [h1, Real.sq_sqrt hx]

theorem cov_Q2 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set E2))
    (harea : ClassicalQuadArea A B C D =
      dist A B * dist A C * Real.sin (∠ B A C) / 2 + dist A C * dist A D * Real.sin (∠ C A D) / 2) :
    let a := dist A B; let b := dist B C; let c := dist C D; let d := dist D A
    let s := (a + b + c + d) / 2
    ClassicalQuadArea A B C D ^ 2 = (s - a) * (s - b) * (s - c) * (s - d) := by
  rw [harea]; exact cov_Q2_part A B C D hconv hcyc

/-! ## Q3a Pitot (covered) -/

theorem cov_Q3a (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hin : ClassicalHasIncircle A B C D) :
    dist A B + dist C D = dist B C + dist D A := by
  obtain ⟨O, r, h⟩ := hin
  exact Quadrilaterals.pitot hconv ⟨O, r, isIncircle_of_classical hconv h⟩

/-! ## Q3b converse of Pitot: the library gives the incircle with same-side conditions -/

theorem cov_Q3b_part (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (h : dist A B + dist C D = dist B C + dist D A) :
    ∃ (O : E2) (r : ℝ), 0 < r ∧
      Metric.infDist O (line[ℝ, A, B] : Set E2) = r ∧
      Metric.infDist O (line[ℝ, B, C] : Set E2) = r ∧
      Metric.infDist O (line[ℝ, C, D] : Set E2) = r ∧
      Metric.infDist O (line[ℝ, D, A] : Set E2) = r ∧
      line[ℝ, A, B].SSameSide O C ∧ line[ℝ, B, C].SSameSide O D ∧
      line[ℝ, C, D].SSameSide O A ∧ line[ℝ, D, A].SSameSide O B :=
  Quadrilaterals.l14_pitot_converse hconv.1 hconv.2 h


/-! ## Q3b: closing the gap (NEW PROOF): the incentre lies in the interior of the hull -/

open Quadrilaterals in
/-- A point weakly inside the three sides of a positively oriented triangle is in its hull. -/
theorem mem_hull_tri (b : OrthonormalBasis (Fin 2) ℝ E2) {X Y W Z : E2}
    (hk : 0 < cross b (Y -ᵥ X) (W -ᵥ X)) (h1 : 0 ≤ cross b (Y -ᵥ X) (Z -ᵥ X))
    (h2 : 0 ≤ cross b (W -ᵥ Y) (Z -ᵥ Y)) (h3 : 0 ≤ cross b (X -ᵥ W) (Z -ᵥ W)) :
    Z ∈ convexHull ℝ ({X, Y, W} : Set E2) := by
  set k := cross b (Y -ᵥ X) (W -ᵥ X)
  set s := cross b (X -ᵥ W) (Z -ᵥ W)
  set t := cross b (Y -ᵥ X) (Z -ᵥ X)
  have hsum : cross b (W -ᵥ Y) (Z -ᵥ Y) = k - s - t := by
    simp only [k, s, t, cross, vsub_eq_sub, cx_sub, cy_sub]; ring
  have hw : (fun i : Fin 3 => ![(k - s - t) / k, s / k, t / k] i) = ![(k - s - t) / k, s / k, t / k] :=
    rfl
  have hZ : Z = ((k - s - t) / k) • X + (s / k) • Y + (t / k) • W := by
    apply ext_coord b
    · simp only [cx_add, cx_smul]
      field_simp
      simp only [k, s, t, cross, vsub_eq_sub, cx_sub, cy_sub]; ring
    · simp only [cy_add, cy_smul]
      field_simp
      simp only [k, s, t, cross, vsub_eq_sub, cx_sub, cy_sub]; ring
  have := (convex_convexHull ℝ ({X, Y, W} : Set E2)).sum_mem (t := Finset.univ)
    (w := ![(k - s - t) / k, s / k, t / k]) (z := ![X, Y, W])
    (by intro i _; fin_cases i <;> simp <;> [exact div_nonneg (by linarith [hsum ▸ h2]) hk.le;
      exact div_nonneg h3 hk.le; exact div_nonneg h1 hk.le])
    (by simp [Fin.sum_univ_three]; field_simp; ring)
    (by intro i _; fin_cases i <;> apply subset_convexHull <;> simp)
  simpa [Fin.sum_univ_three, ← hZ] using this

open Quadrilaterals in
theorem cov_Q3b (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (h : dist A B + dist C D = dist B C + dist D A) :
    ClassicalHasIncircle A B C D := by
  obtain ⟨O, r, hr, d1, d2, d3, d4, s1, s2, s3, s4⟩ := cov_Q3b_part A B C D hconv h
  refine ⟨O, r, hr, ?_, d1, d2, d3, d4⟩
  obtain ⟨b, X, t, u, p1, p2, q1, q2, -, -, hF⟩ := convex_frame hconv
  obtain ⟨i1, i2, i3, i4⟩ := IsFrame.incircle b hF ⟨hr, d1, d2, d3, d4, s1, s2, s3, s4⟩
  obtain ⟨n1, n2, n3, n4⟩ := hF.ne
  obtain ⟨c1, -, -, -, -, -, -, -, c9⟩ := hF.pos
  let U : Set E2 := {Z | 0 < cross b (B -ᵥ A) (Z -ᵥ A)} ∩ {Z | 0 < cross b (C -ᵥ B) (Z -ᵥ B)} ∩
    {Z | 0 < cross b (D -ᵥ C) (Z -ᵥ C)} ∩ {Z | 0 < cross b (A -ᵥ D) (Z -ᵥ D)}
  have hcont : ∀ (P Q : E2), Continuous fun Z : E2 => cross b (Q -ᵥ P) (Z -ᵥ P) := by
    intro P Q; unfold cross cx cy; fun_prop
  have hU : IsOpen U :=
    (((isOpen_lt continuous_const (hcont _ _)).inter (isOpen_lt continuous_const (hcont _ _))).inter
      (isOpen_lt continuous_const (hcont _ _))).inter (isOpen_lt continuous_const (hcont _ _))
  have hOU : O ∈ U := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp only [Set.mem_ofPred_eq, i1, i2, i3, i4] <;>
      exact mul_pos hr (dist_pos.2 ‹_›)
  have hsub : U ⊆ convexHull ℝ ({A, B, C, D} : Set E2) := by
    rintro Z ⟨⟨⟨z1, z2⟩, z3⟩, z4⟩
    simp only [Set.mem_ofPred_eq] at z1 z2 z3 z4
    by_cases hz : 0 ≤ cross b (C -ᵥ A) (Z -ᵥ A)
    · refine convexHull_mono (by intro x; simp; tauto) (mem_hull_tri b c9 hz z3.le z4.le)
    · push Not at hz
      refine convexHull_mono (by intro x; simp; tauto) (mem_hull_tri b c1 z1.le z2.le ?_)
      have : cross b (A -ᵥ C) (Z -ᵥ C) = -cross b (C -ᵥ A) (Z -ᵥ A) := by
        simp only [cross, vsub_eq_sub, cx_sub, cy_sub]; ring
      linarith
  exact interior_maximal hsub hU hOU

/-- The full classical Pitot equivalence. -/
theorem cov_Q3 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D) :
    ClassicalHasIncircle A B C D ↔ dist A B + dist C D = dist B C + dist D A :=
  ⟨cov_Q3a A B C D hconv, cov_Q3b A B C D hconv⟩

/-! ## Q4 Euler: library needs `finrank = 2`; general proof (NEW PROOF) -/

theorem cov_Q4_part (A B C D : E2) :
    dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2 =
      dist A C ^ 2 + dist B D ^ 2 + 4 * dist (midpoint ℝ A C) (midpoint ℝ B D) ^ 2 :=
  Quadrilaterals.l14_euler_quadrilateral A B C D

theorem cov_Q4 {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C D : P) :
    dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2 =
      dist A C ^ 2 + dist B D ^ 2 + 4 * dist (midpoint ℝ A C) (midpoint ℝ B D) ^ 2 := by
  have hm : midpoint ℝ A C -ᵥ midpoint ℝ B D = (⅟2 : ℝ) • ((A -ᵥ B) + (C -ᵥ D)) := by
    rw [midpoint_vsub_midpoint, midpoint_eq_smul_add]
  rw [dist_eq_norm_vsub V (midpoint ℝ A C), hm]
  simp only [dist_eq_norm_vsub V]
  have e1 : A -ᵥ B = -(B -ᵥ A) := (neg_vsub_eq_vsub_rev B A).symm
  have e2 : B -ᵥ C = (B -ᵥ A) - (C -ᵥ A) := (vsub_sub_vsub_cancel_right B C A).symm
  have e3 : C -ᵥ D = (C -ᵥ A) - (D -ᵥ A) := (vsub_sub_vsub_cancel_right C D A).symm
  have e4 : A -ᵥ C = -(C -ᵥ A) := (neg_vsub_eq_vsub_rev C A).symm
  have e5 : B -ᵥ D = (B -ᵥ A) - (D -ᵥ A) := (vsub_sub_vsub_cancel_right B D A).symm
  have e6 : D -ᵥ A = D -ᵥ A := rfl
  rw [e1, e2, e3, e4, e5]
  generalize B -ᵥ A = u
  generalize C -ᵥ A = v
  generalize D -ᵥ A = w
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right,
    invOf_eq_inv]
  rw [real_inner_comm u v, real_inner_comm u w, real_inner_comm v w]
  ring

/-! ## Q5 Ptolemy II (covered) -/

theorem cov_Q5 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set E2)) :
    dist A C / dist B D =
      (dist A B * dist A D + dist C B * dist C D) /
        (dist B A * dist B C + dist D A * dist D C) :=
  Quadrilaterals.ptolemy_second hconv hcyc

/-! ## Q6 van Aubel (covered) -/

instance instFactC : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩

/-- Shoelace sum = area form of the diagonals. -/
theorem signedArea2_eq (A B C D : ℂ) :
    ClassicalSignedArea2 A B C D = Complex.orientation.areaForm (C -ᵥ A) (D -ᵥ B) := by
  rw [Complex.areaForm, ClassicalSignedArea2]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, vsub_eq_sub, Complex.sub_re,
    Complex.sub_im]
  ring

theorem squareCenter_eq (A B C D X Y : ℂ) (hccw : 0 < ClassicalSignedArea2 A B C D) :
    Quadrilaterals.squareCenter Complex.orientation A B C D X Y =
      ClassicalOutwardSquareCentre X Y := by
  have hs : Quadrilaterals.quadSign Complex.orientation A B C D = 1 := by
    rw [Quadrilaterals.quadSign, if_pos (by rwa [← signedArea2_eq])]
  rw [Quadrilaterals.squareCenter, hs, ClassicalOutwardSquareCentre, Complex.rotation,
    Real.Angle.coe_toCircle, Real.Angle.cos_coe, Real.Angle.sin_coe]
  simp only [one_mul, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two,
    vsub_eq_sub, vadd_eq_add, midpoint_eq_smul_add, Complex.real_smul, invOf_eq_inv]
  push_cast
  ring

theorem cov_Q6 (A B C D : ℂ) (hccw : 0 < ClassicalSignedArea2 A B C D) :
    let P := ClassicalOutwardSquareCentre A B
    let Q := ClassicalOutwardSquareCentre B C
    let R := ClassicalOutwardSquareCentre C D
    let S := ClassicalOutwardSquareCentre D A
    dist P R = dist Q S ∧ ⟪R - P, S - Q⟫ = 0 := by
  have h := Quadrilaterals.van_aubel Complex.orientation A B C D
  simp only [squareCenter_eq A B C D _ _ hccw, vsub_eq_sub] at h
  exact h

/-! ## Q7 Newton (covered) -/

theorem cov_Q7 (A B C D O : E2) (r : ℝ) (hconv : ClassicalConvexQuad A B C D)
    (hin : ClassicalIsIncircle A B C D O r) (hnp : ¬ ClassicalParallelogram A B C D) :
    O ∈ line[ℝ, midpoint ℝ A C, midpoint ℝ B D] := by
  have hcol := Quadrilaterals.newton_line hconv (isIncircle_of_classical hconv hin)
  have hne : midpoint ℝ A C ≠ midpoint ℝ B D := by
    intro h
    rw [midpoint_eq_midpoint_iff_vsub_eq_vsub] at h
    apply hnp
    rw [ClassicalParallelogram]
    rw [← neg_vsub_eq_vsub_rev A B, h, neg_vsub_eq_vsub_rev]
  exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hne

/-! ## Q8 Fuss (covered) -/

theorem cov_Q8 (A B C D I : E2) (r : ℝ) (Ω : Sphere E2)
    (hconv : ClassicalConvexQuad A B C D)
    (hA : A ∈ Ω) (hB : B ∈ Ω) (hC : C ∈ Ω) (hD : D ∈ Ω)
    (hin : ClassicalIsIncircle A B C D I r) :
    let R := Ω.radius; let d := dist Ω.center I
    1 / (R - d) ^ 2 + 1 / (R + d) ^ 2 = 1 / r ^ 2 :=
  Quadrilaterals.fuss hconv (mem_sphere.1 hA) (mem_sphere.1 hB) (mem_sphere.1 hC)
    (mem_sphere.1 hD) (isIncircle_of_classical hconv hin)


/-! ## Verbatim classical statements (copied from PaperIClassical.lean, proved from `cov_`) -/

-- Q1 (was NARROWER): now proved via `classicalQuadArea_eq` (area bridge).
theorem classical_Q1 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D) :
    let a := dist A B; let b := dist B C; let c := dist C D; let d := dist D A
    let s := (a + b + c + d) / 2
    ClassicalQuadArea A B C D ^ 2 =
      (s - a) * (s - b) * (s - c) * (s - d) -
        a * b * c * d * Real.cos ((∠ A B C + ∠ C D A) / 2) ^ 2 := by
  intro a b c d s
  rw [classicalQuadArea_eq A B C D hconv]
  exact Quadrilaterals.bretschneider hconv

-- Q2 (was NARROWER): now proved via `classicalQuadArea_eq` (area bridge).
theorem classical_Q2 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set E2)) :
    let a := dist A B; let b := dist B C; let c := dist C D; let d := dist D A
    let s := (a + b + c + d) / 2
    ClassicalQuadArea A B C D ^ 2 = (s - a) * (s - b) * (s - c) * (s - d) := by
  intro a b c d s
  rw [classicalQuadArea_eq A B C D hconv]
  have h1 := Quadrilaterals.brahmagupta hconv hcyc
  have h2 := Quadrilaterals.bretschneider hconv
  have hx : 0 ≤ (s - a) * (s - b) * (s - c) * (s - d) := by
    have : 0 ≤ a * b * c * d * Real.cos ((∠ A B C + ∠ C D A) / 2) ^ 2 := by
      simp only [a, b, c, d]; positivity
    simp only [a, b, c, d, s, Quadrilaterals.semiperimeter] at this h2 ⊢
    nlinarith [sq_nonneg (Quadrilaterals.quadArea A B C D)]
  simp only [a, b, c, d, s, Quadrilaterals.semiperimeter] at hx h1 ⊢
  rw [h1, Real.sq_sqrt hx]

theorem classical_Q3a (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hin : ClassicalHasIncircle A B C D) :
    dist A B + dist C D = dist B C + dist D A := by
  exact cov_Q3a A B C D hconv hin

theorem classical_Q3b (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (h : dist A B + dist C D = dist B C + dist D A) :
    ClassicalHasIncircle A B C D := by
  exact cov_Q3b A B C D hconv h

theorem classical_Q4 {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C D : P) :
    dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2 =
      dist A C ^ 2 + dist B D ^ 2 + 4 * dist (midpoint ℝ A C) (midpoint ℝ B D) ^ 2 := by
  exact cov_Q4 A B C D

theorem classical_Q5 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set E2)) :
    dist A C / dist B D =
      (dist A B * dist A D + dist C B * dist C D) /
        (dist B A * dist B C + dist D A * dist D C) := by
  exact cov_Q5 A B C D hconv hcyc

theorem classical_Q6 (A B C D : ℂ) (hccw : 0 < ClassicalSignedArea2 A B C D) :
    let P := ClassicalOutwardSquareCentre A B
    let Q := ClassicalOutwardSquareCentre B C
    let R := ClassicalOutwardSquareCentre C D
    let S := ClassicalOutwardSquareCentre D A
    dist P R = dist Q S ∧ ⟪R - P, S - Q⟫ = 0 := by
  exact cov_Q6 A B C D hccw

theorem classical_Q7 (A B C D O : E2) (r : ℝ) (hconv : ClassicalConvexQuad A B C D)
    (hin : ClassicalIsIncircle A B C D O r) (hnp : ¬ ClassicalParallelogram A B C D) :
    O ∈ line[ℝ, midpoint ℝ A C, midpoint ℝ B D] := by
  exact cov_Q7 A B C D O r hconv hin hnp

theorem classical_Q8 (A B C D I : E2) (r : ℝ) (Ω : Sphere E2)
    (hconv : ClassicalConvexQuad A B C D)
    (hA : A ∈ Ω) (hB : B ∈ Ω) (hC : C ∈ Ω) (hD : D ∈ Ω)
    (hin : ClassicalIsIncircle A B C D I r) :
    let R := Ω.radius; let d := dist Ω.center I
    1 / (R - d) ^ 2 + 1 / (R + d) ^ 2 = 1 / r ^ 2 := by
  exact cov_Q8 A B C D I r Ω hconv hA hB hC hD hin

end L15Q

#print axioms L15Q.cov_Q1_part
#print axioms L15Q.cov_Q1
#print axioms L15Q.cov_Q2_part
#print axioms L15Q.cov_Q2
#print axioms L15Q.cov_Q3a
#print axioms L15Q.cov_Q3b_part
#print axioms L15Q.cov_Q3b
#print axioms L15Q.cov_Q3
#print axioms L15Q.cov_Q4_part
#print axioms L15Q.cov_Q4
#print axioms L15Q.cov_Q5
#print axioms L15Q.cov_Q6
#print axioms L15Q.cov_Q7
#print axioms L15Q.cov_Q8
#print axioms Quadrilaterals.AreaBridge.volume_convexHull_triangle
#print axioms Quadrilaterals.AreaBridge.volume_convexHull_quad
#print axioms L15Q.classicalQuadArea_eq
#print axioms L15Q.classical_Q1
#print axioms L15Q.classical_Q2
#print axioms L15Q.classical_Q3a
#print axioms L15Q.classical_Q3b
#print axioms L15Q.classical_Q4
#print axioms L15Q.classical_Q5
#print axioms L15Q.classical_Q6
#print axioms L15Q.classical_Q7
#print axioms L15Q.classical_Q8
