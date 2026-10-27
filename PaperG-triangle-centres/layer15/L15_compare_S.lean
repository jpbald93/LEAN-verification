import Brocard

open EuclideanGeometry

noncomputable section

namespace L15CmpS

local notation "Pt" => EuclideanSpace ℝ (Fin 2)

/-! ## Basic definitions -/

/-- The triangle `ABC` as a Mathlib `Affine.Triangle`. -/
def ClassicalTri (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Affine.Triangle ℝ Pt :=
  ⟨![A, B, C], h⟩

/-- The point with (unnormalised) barycentric coordinates `wA : wB : wC` with respect to
`A, B, C` (meaningful when `wA + wB + wC ≠ 0`). -/
def ClassicalBary (A B C : Pt) (wA wB wC : ℝ) : Pt :=
  Finset.univ.affineCombination ℝ ![A, B, C] (fun i => ![wA, wB, wC] i / (wA + wB + wC))

/-- Semiperimeter. -/
def ClassicalSemiperimeter (A B C : Pt) : ℝ := (dist B C + dist C A + dist A B) / 2

/-- Area `Δ = ½·AB·AC·sin A`. -/
def ClassicalArea (A B C : Pt) : ℝ := (1 / 2) * dist A B * dist A C * Real.sin (∠ B A C)

/-- Centroid `G`. (Stated for any three points; also used for pedal triangles.) -/
def ClassicalCentroid (A B C : Pt) : Pt := Finset.univ.centroid ℝ ![A, B, C]

/-- Excentre opposite `A`: barycentrics `-a : b : c` (textbook formula). -/
def ClassicalExcenterA (A B C : Pt) : Pt :=
  ClassicalBary A B C (-dist B C) (dist C A) (dist A B)

/-- Point of contact of the excircle opposite `A` with line `BC`: the foot of the
perpendicular from the excentre to `BC`. -/
def ClassicalExContactA (A B C : Pt) : Pt :=
  (orthogonalProjection line[ℝ, B, C] (ClassicalExcenterA A B C) : Pt)

/-- Exradius `r_a`: distance from the excentre opposite `A` to line `BC`. -/
def ClassicalExradiusA (A B C : Pt) : ℝ :=
  dist (ClassicalExcenterA A B C) (ClassicalExContactA A B C)

/-- Point of contact of the incircle with line `BC`: foot of the perpendicular from the
(Mathlib) incentre to `BC`. -/
def ClassicalInContactA (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Pt :=
  (orthogonalProjection line[ℝ, B, C] (ClassicalTri A B C h).incenter : Pt)

/-- Incircle contact points on `CA` and `AB` (feet of perpendiculars from the same incentre). -/
def ClassicalInContactB (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Pt :=
  (orthogonalProjection line[ℝ, C, A] (ClassicalTri A B C h).incenter : Pt)

def ClassicalInContactC (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Pt :=
  (orthogonalProjection line[ℝ, A, B] (ClassicalTri A B C h).incenter : Pt)

/-- A point (other than `A`, in a non-degenerate triangle) on the internal bisector of angle
`BAC`: `A + AB/|AB| + AC/|AC|`. -/
def ClassicalBisectorPoint (A B C : Pt) : Pt :=
  ((dist A B)⁻¹ • (B -ᵥ A) + (dist A C)⁻¹ • (C -ᵥ A)) +ᵥ A

/-- Reflection of the line `AP` in the internal bisector at `A`
(the isogonal line of `AP` at vertex `A`). -/
def ClassicalIsogonalLine (A B C P : Pt) : AffineSubspace ℝ Pt :=
  line[ℝ, A, reflection line[ℝ, A, ClassicalBisectorPoint A B C] P]

/-- Symmedian through `A`: reflection of the median `A M_a` in the internal bisector at `A`. -/
def ClassicalSymmedian (A B C : Pt) : AffineSubspace ℝ Pt :=
  ClassicalIsogonalLine A B C (midpoint ℝ B C)

/-- `P` and `Q` are isogonal conjugates: for each vertex, the reflection of the line
vertex–`P` in the bisector at that vertex passes through `Q`. -/
def ClassicalIsogonalConj (A B C P Q : Pt) : Prop :=
  Q ∈ ClassicalIsogonalLine A B C P ∧ Q ∈ ClassicalIsogonalLine B C A P ∧
    Q ∈ ClassicalIsogonalLine C A B P

/-- Pedal triangle vertex on line `BC` of a point `P`. -/
def ClassicalFoot (B C P : Pt) : Pt := (orthogonalProjection line[ℝ, B, C] P : Pt)

/-- Centroid of the pedal triangle of `P`. -/
def ClassicalPedalCentroid (A B C P : Pt) : Pt :=
  ClassicalCentroid (ClassicalFoot B C P) (ClassicalFoot C A P) (ClassicalFoot A B P)

/-- Anticomplementary-triangle vertex opposite `A`: reflection of `A` in the midpoint of `BC`
(i.e. `B + C - A`); the triangle of these has `ABC` as medial triangle. -/
def ClassicalAnticompl (A B C : Pt) : Pt := AffineEquiv.pointReflection ℝ (midpoint ℝ B C) A


open Brocard

instance factFinrankPt : Fact (Module.finrank ℝ Pt = 2) := ⟨finrank_euclideanSpace_fin⟩


open scoped RealInnerProductSpace

lemma refl_vec (X Y Z P : Pt) (hXY : X ≠ Y) (hXZ : X ≠ Z) (y z : ℝ)
    (hP : P -ᵥ X = y • (Y -ᵥ X) + z • (Z -ᵥ X)) :
    reflection line[ℝ, X, ClassicalBisectorPoint X Y Z] P -ᵥ X =
      (z * dist X Z / dist X Y) • (Y -ᵥ X) + (y * dist X Y / dist X Z) • (Z -ᵥ X) := by
  have hc : 0 < dist X Y := dist_pos.2 hXY
  have hb : 0 < dist X Z := dist_pos.2 hXZ
  have hpu : ⟪Y -ᵥ X, Y -ᵥ X⟫ = dist X Y ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm_vsub' Pt]
  have hqv : ⟪Z -ᵥ X, Z -ᵥ X⟫ = dist X Z ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm_vsub' Pt]
  have hBis : ClassicalBisectorPoint X Y Z -ᵥ X =
      (dist X Y)⁻¹ • (Y -ᵥ X) + (dist X Z)⁻¹ • (Z -ᵥ X) := by
    rw [ClassicalBisectorPoint, vadd_vsub]
  set s : ℝ := (y * dist X Y + z * dist X Z) / 2 with hs
  have hF : AffineMap.lineMap X (ClassicalBisectorPoint X Y Z) s -ᵥ X =
      (s * (dist X Y)⁻¹) • (Y -ᵥ X) + (s * (dist X Z)⁻¹) • (Z -ᵥ X) := by
    rw [AffineMap.lineMap_vsub_left, hBis]; module
  have hproj : (orthogonalProjection line[ℝ, X, ClassicalBisectorPoint X Y Z] P : Pt) =
      AffineMap.lineMap X (ClassicalBisectorPoint X Y Z) s := by
    rw [coe_orthogonalProjection_eq_iff_mem]
    refine ⟨AffineMap.lineMap_mem_affineSpan_pair _ _ _, ?_⟩
    rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right]
    have e1 : X -ᵥ ClassicalBisectorPoint X Y Z =
        (-(dist X Y)⁻¹) • (Y -ᵥ X) + (-(dist X Z)⁻¹) • (Z -ᵥ X) := by
      rw [← neg_vsub_eq_vsub_rev, hBis]; module
    have e2 : P -ᵥ AffineMap.lineMap X (ClassicalBisectorPoint X Y Z) s =
        (y - s * (dist X Y)⁻¹) • (Y -ᵥ X) + (z - s * (dist X Z)⁻¹) • (Z -ᵥ X) := by
      rw [← vsub_sub_vsub_cancel_right P _ X, hP, hF]; module
    rw [e1, e2, Brocard.inner_comb, hpu, hqv]
    unfold Brocard.gram
    rw [hs]
    field_simp
    ring
  rw [EuclideanGeometry.reflection_apply', hproj, vadd_vsub_assoc,
    ← vsub_sub_vsub_cancel_right _ P X, hF, hP]
  match_scalars <;> field_simp <;> ring

lemma range3 (A B C : Pt) : Set.range ![A, B, C] = {A, B, C} := by
  rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]

lemma span_top (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    affineSpan ℝ (Set.range ![A, B, C]) = ⊤ := by
  rw [h.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_fin,
    finrank_euclideanSpace_fin]

def basis3 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : AffineBasis (Fin 3) ℝ Pt :=
  ⟨![A, B, C], h, span_top A B C h⟩

lemma interior_eq (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    interior (convexHull ℝ {A, B, C}) = {x | ∀ i, 0 < (basis3 A B C h).coord i x} := by
  rw [← (basis3 A B C h).interior_convexHull, ← range3]
  rfl

lemma coords_of_interior (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (X : Pt)
    (hX : X ∈ interior (convexHull ℝ {A, B, C})) :
    ∃ y z : ℝ, 0 < y ∧ 0 < z ∧ 0 < 1 - y - z ∧
      X -ᵥ A = y • (B -ᵥ A) + z • (C -ᵥ A) := by
  rw [interior_eq A B C h] at hX
  set b := basis3 A B C h
  have hsum : ∑ i, b.coord i X = 1 := b.sum_coord_apply_eq_one X
  have hX' := b.affineCombination_coord_eq_self X
  have hv : Finset.univ.affineCombination ℝ (ClassicalTri A B C h).points
      (fun i => b.coord i X) -ᵥ A =
      b.coord 1 X • (B -ᵥ A) + b.coord 2 X • (C -ᵥ A) :=
    Brocard.affineCombination_vsub (ClassicalTri A B C h) _ hsum
  refine ⟨b.coord 1 X, b.coord 2 X, hX 1, hX 2, ?_, ?_⟩
  · rw [Fin.sum_univ_three] at hsum
    have := hX 0
    linarith
  · rw [← hv]
    exact congrArg (· -ᵥ A) hX'.symm

lemma interior_of_weights (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (w : Fin 3 → ℝ)
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) :
    Finset.univ.affineCombination ℝ ![A, B, C] w ∈ interior (convexHull ℝ {A, B, C}) := by
  rw [interior_eq A B C h]
  intro i
  have := (basis3 A B C h).coord_apply_combination_of_mem (Finset.mem_univ i) hw
  rw [show (⇑(basis3 A B C h) : Fin 3 → Pt) = ![A, B, C] from rfl] at this
  rw [this]
  exact hpos i


lemma bary_vsub (A B C Q : Pt) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination ℝ ![A, B, C] w -ᵥ Q =
      w 0 • (A -ᵥ Q) + w 1 • (B -ᵥ Q) + w 2 • (C -ᵥ Q) := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw Q, vadd_vsub,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp

lemma symm_mem (X Y Z P : Pt) (hXY : X ≠ Y) (hXZ : X ≠ Z) (S : ℝ) (hS : 0 < S)
    (hP : P -ᵥ X = (dist X Z ^ 2 / S) • (Y -ᵥ X) + (dist X Y ^ 2 / S) • (Z -ᵥ X)) :
    P ∈ ClassicalSymmedian X Y Z := by
  have hc : 0 < dist X Y := dist_pos.2 hXY
  have hb : 0 < dist X Z := dist_pos.2 hXZ
  have hM : midpoint ℝ Y Z -ᵥ X = (1 / 2 : ℝ) • (Y -ᵥ X) + (1 / 2 : ℝ) • (Z -ᵥ X) := by
    rw [midpoint_vsub, invOf_eq_inv]; module
  have hR := refl_vec X Y Z _ hXY hXZ _ _ hM
  unfold ClassicalSymmedian ClassicalIsogonalLine
  rw [← vsub_vadd P X, vadd_left_mem_affineSpan_pair]
  refine ⟨2 * dist X Y * dist X Z / S, ?_⟩
  rw [hR, hP]
  match_scalars <;> field_simp

lemma symm_dir (X Y Z P : Pt) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hP : P ∈ ClassicalSymmedian X Y Z) :
    ∃ r : ℝ, P -ᵥ X = (r * (1 / 2 * dist X Z / dist X Y)) • (Y -ᵥ X) +
      (r * (1 / 2 * dist X Y / dist X Z)) • (Z -ᵥ X) := by
  have hM : midpoint ℝ Y Z -ᵥ X = (1 / 2 : ℝ) • (Y -ᵥ X) + (1 / 2 : ℝ) • (Z -ᵥ X) := by
    rw [midpoint_vsub, invOf_eq_inv]; module
  have hR := refl_vec X Y Z _ hXY hXZ _ _ hM
  unfold ClassicalSymmedian ClassicalIsogonalLine at hP
  rw [← vsub_vadd P X, vadd_left_mem_affineSpan_pair] at hP
  obtain ⟨r, hr⟩ := hP
  refine ⟨r, ?_⟩
  rw [← hr, hR]
  module

lemma ne01 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : A ≠ B :=
  fun e => absurd (h.injective (a₁ := 0) (a₂ := 1) (by simpa using e)) (by decide)
lemma ne02 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : A ≠ C :=
  fun e => absurd (h.injective (a₁ := 0) (a₂ := 2) (by simpa using e)) (by decide)
lemma ne12 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : B ≠ C :=
  fun e => absurd (h.injective (a₁ := 1) (a₂ := 2) (by simpa using e)) (by decide)

lemma K_vsub (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    let S := dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2
    let K := ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2)
    K -ᵥ A = (dist C A ^ 2 / S) • (B -ᵥ A) + (dist A B ^ 2 / S) • (C -ᵥ A) ∧
    K -ᵥ B = (dist A B ^ 2 / S) • (C -ᵥ B) + (dist B C ^ 2 / S) • (A -ᵥ B) ∧
    K -ᵥ C = (dist B C ^ 2 / S) • (A -ᵥ C) + (dist C A ^ 2 / S) • (B -ᵥ C) := by
  intro S K
  have ha := dist_pos.2 (ne12 A B C h)
  have hb := dist_pos.2 (ne02 A B C h).symm
  have hc := dist_pos.2 (ne01 A B C h)
  have hS : 0 < S := by positivity
  have hw : ∑ i, (fun i => ![dist B C ^ 2, dist C A ^ 2, dist A B ^ 2] i / S) i = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [← add_div, ← add_div]; exact div_self hS.ne'
  refine ⟨?_, ?_, ?_⟩ <;> rw [show K = Finset.univ.affineCombination ℝ ![A, B, C]
    (fun i => ![dist B C ^ 2, dist C A ^ 2, dist A B ^ 2] i / S) from rfl, bary_vsub _ _ _ _ _ hw]
    <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, vsub_self, smul_zero] <;> abel

theorem cov_S1a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ K : Pt, K ∈ ClassicalSymmedian A B C ∧ K ∈ ClassicalSymmedian B C A ∧
      K ∈ ClassicalSymmedian C A B ∧ K ∈ interior (convexHull ℝ {A, B, C}) := by
  have ha := dist_pos.2 (ne12 A B C h)
  have hb := dist_pos.2 (ne02 A B C h).symm
  have hc := dist_pos.2 (ne01 A B C h)
  have hS : 0 < dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2 := by positivity
  obtain ⟨hKA, hKB, hKC⟩ := K_vsub A B C h
  refine ⟨ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2), ?_, ?_, ?_, ?_⟩
  · refine symm_mem A B C _ (ne01 A B C h) (ne02 A B C h) _ hS ?_
    rw [hKA, dist_comm A C]
  · refine symm_mem B C A _ (ne12 A B C h) (ne01 A B C h).symm _ hS ?_
    rw [hKB, dist_comm B A]
  · refine symm_mem C A B _ (ne02 A B C h).symm (ne12 A B C h).symm _ hS ?_
    rw [hKC, dist_comm C B]
  · refine interior_of_weights A B C h _ ?_ ?_
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
    · intro i; fin_cases i <;> simp <;> positivity

theorem cov_S1b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (K : Pt)
    (hA : K ∈ ClassicalSymmedian A B C) (hB : K ∈ ClassicalSymmedian B C A)
    (hC : K ∈ ClassicalSymmedian C A B) :
    K = ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2) := by
  have ha := dist_pos.2 (ne12 A B C h)
  have hb := dist_pos.2 (ne02 A B C h).symm
  have hc := dist_pos.2 (ne01 A B C h)
  have hpu : inner ℝ (B -ᵥ A) (B -ᵥ A) = dist A B ^ 2 := Brocard.inner_uu (ClassicalTri A B C h)
  have hqv : inner ℝ (C -ᵥ A) (C -ᵥ A) = dist C A ^ 2 := Brocard.inner_vv (ClassicalTri A B C h)
  have hruv : inner ℝ (B -ᵥ A) (C -ᵥ A) = (dist C A ^ 2 + dist A B ^ 2 - dist B C ^ 2) / 2 :=
    Brocard.inner_uv (ClassicalTri A B C h)
  have hD := Brocard.gram_det_pos (ClassicalTri A B C h)
  change 0 < inner ℝ (B -ᵥ A) (B -ᵥ A) * inner ℝ (C -ᵥ A) (C -ᵥ A) -
    inner ℝ (B -ᵥ A) (C -ᵥ A) ^ 2 at hD
  rw [hpu, hqv, hruv] at hD
  obtain ⟨r, hr⟩ := symm_dir A B C K (ne01 A B C h) (ne02 A B C h) hA
  obtain ⟨s, hs⟩ := symm_dir B C A K (ne12 A B C h) (ne01 A B C h).symm hB
  have hs' : K -ᵥ A = (1 - s * (1 / 2 * dist B A / dist B C) - s * (1 / 2 * dist B C / dist B A)) •
      (B -ᵥ A) + (s * (1 / 2 * dist B A / dist B C)) • (C -ᵥ A) := by
    rw [← vsub_add_vsub_cancel K B A, hs, ← vsub_sub_vsub_cancel_right C B A,
      ← neg_vsub_eq_vsub_rev B A]
    module
  obtain ⟨e1, e2⟩ := Brocard.coords_eq hpu hqv hruv hD (hr.symm.trans hs')
  rw [dist_comm B A, dist_comm A C] at *
  have hr2 : r * (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) = 2 * dist C A * dist A B := by
    field_simp at e1 e2
    nlinarith
  apply vsub_left_cancel (p := A)
  rw [hr, (K_vsub A B C h).1]
  have hS : 0 < dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2 := by positivity
  congr 1 <;> congr 1 <;> field_simp <;> nlinarith


lemma tri_facts (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    inner ℝ (B -ᵥ A) (B -ᵥ A) = dist A B ^ 2 ∧ inner ℝ (C -ᵥ A) (C -ᵥ A) = dist C A ^ 2 ∧
    inner ℝ (B -ᵥ A) (C -ᵥ A) = (dist C A ^ 2 + dist A B ^ 2 - dist B C ^ 2) / 2 ∧
    0 < dist A B ^ 2 * dist C A ^ 2 - ((dist C A ^ 2 + dist A B ^ 2 - dist B C ^ 2) / 2) ^ 2 ∧
    0 < dist B C ^ 2 ∧ 0 < dist C A ^ 2 ∧ 0 < dist A B ^ 2 := by
  have hpu : inner ℝ (B -ᵥ A) (B -ᵥ A) = dist A B ^ 2 := Brocard.inner_uu (ClassicalTri A B C h)
  have hqv : inner ℝ (C -ᵥ A) (C -ᵥ A) = dist C A ^ 2 := Brocard.inner_vv (ClassicalTri A B C h)
  have hruv : inner ℝ (B -ᵥ A) (C -ᵥ A) = (dist C A ^ 2 + dist A B ^ 2 - dist B C ^ 2) / 2 :=
    Brocard.inner_uv (ClassicalTri A B C h)
  have hD := Brocard.gram_det_pos (ClassicalTri A B C h)
  change 0 < inner ℝ (B -ᵥ A) (B -ᵥ A) * inner ℝ (C -ᵥ A) (C -ᵥ A) -
    inner ℝ (B -ᵥ A) (C -ᵥ A) ^ 2 at hD
  rw [hpu, hqv, hruv] at hD
  have ha := dist_pos.2 (ne12 A B C h)
  have hb := dist_pos.2 (ne02 A B C h).symm
  have hc := dist_pos.2 (ne01 A B C h)
  exact ⟨hpu, hqv, hruv, hD, by positivity, by positivity, by positivity⟩

/-- NEW PROOF: uniqueness of the first Brocard point among interior points. -/
lemma brocard1_unique (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A) :
    Ω = (ClassicalTri A B C h).brocardPoint₁ := by
  obtain ⟨y, z, hy, hz, hx, hΩc⟩ := coords_of_interior A B C h Ω hΩ.1
  obtain ⟨hpu, hqv, hruv, hD, ha, hb, hc⟩ := tri_facts A B C h
  have hA : A -ᵥ A = (0 : ℝ) • (B -ᵥ A) + (0 : ℝ) • (C -ᵥ A) := by simp
  have hB : B -ᵥ A = (1 : ℝ) • (B -ᵥ A) + (0 : ℝ) • (C -ᵥ A) := by simp
  have hC : C -ᵥ A = (0 : ℝ) • (B -ᵥ A) + (1 : ℝ) • (C -ᵥ A) := by simp
  have hBr : (ClassicalTri A B C h).brocardPoint₁ -ᵥ A =
      (dist B C ^ 2 * dist C A ^ 2 / (dist B C ^ 2 * dist C A ^ 2 + dist C A ^ 2 * dist A B ^ 2 +
        dist A B ^ 2 * dist B C ^ 2)) • (B -ᵥ A) +
      (dist C A ^ 2 * dist A B ^ 2 / (dist B C ^ 2 * dist C A ^ 2 + dist C A ^ 2 * dist A B ^ 2 +
        dist A B ^ 2 * dist B C ^ 2)) • (C -ᵥ A) :=
    Brocard.brocardPoint₁_coords (ClassicalTri A B C h) rfl rfl rfl
  have e1 := congrArg Real.cot hΩ.2.1
  have e2 := congrArg Real.cot hΩ.2.2
  rw [Brocard.cot_angle_coords (d := z) hpu hqv hruv hΩc hA hB (by
        rw [show (y - 0) * (0 - 0) - (1 - 0) * (z - 0) = -z by ring, abs_neg, abs_of_pos hz]),
    Brocard.cot_angle_coords (d := 1 - y - z) hpu hqv hruv hΩc hB hC (by
        rw [show (y - 1) * (1 - 0) - (0 - 1) * (z - 0) = -(1 - y - z) by ring, abs_neg,
          abs_of_pos hx])] at e1
  rw [Brocard.cot_angle_coords (d := 1 - y - z) hpu hqv hruv hΩc hB hC (by
        rw [show (y - 1) * (1 - 0) - (0 - 1) * (z - 0) = -(1 - y - z) by ring, abs_neg,
          abs_of_pos hx]),
    Brocard.cot_angle_coords (d := y) hpu hqv hruv hΩc hC hA (by
        rw [show (y - 0) * (0 - 1) - (0 - 0) * (z - 1) = -y by ring, abs_neg,
          abs_of_pos hy])] at e2
  apply vsub_left_cancel (p := A)
  rw [hΩc, hBr]
  have hs := Real.sqrt_pos.2 hD
  generalize √(dist A B ^ 2 * dist C A ^ 2 -
    ((dist C A ^ 2 + dist A B ^ 2 - dist B C ^ 2) / 2) ^ 2) = s at *
  generalize dist B C ^ 2 = a2 at *
  generalize dist C A ^ 2 = b2 at *
  generalize dist A B ^ 2 = c2 at *
  unfold Brocard.gram at e1 e2
  rw [div_eq_div_iff (by positivity) (by positivity)] at e1 e2
  set x := 1 - y - z with hxdef
  set g1 := (y - 0) * (1 - 0) * c2 + ((y - 0) * (0 - 0) + (z - 0) * (1 - 0)) *
    ((b2 + c2 - a2) / 2) + (z - 0) * (0 - 0) * b2 with hg1
  set g2 := (y - 1) * (0 - 1) * c2 + ((y - 1) * (1 - 0) + (z - 0) * (0 - 1)) *
    ((b2 + c2 - a2) / 2) + (z - 0) * (1 - 0) * b2 with hg2
  set g3 := (y - 0) * (0 - 0) * c2 + ((y - 0) * (0 - 1) + (z - 1) * (0 - 0)) *
    ((b2 + c2 - a2) / 2) + (z - 1) * (0 - 1) * b2 with hg3
  have f1 : (g1 * x - g2 * z) * s = 0 := by linear_combination e1
  have f2 : (g2 * y - g3 * x) * s = 0 := by linear_combination e2
  have f1' := (mul_eq_zero.1 f1).resolve_right hs.ne'
  have f2' := (mul_eq_zero.1 f2).resolve_right hs.ne'
  have hsum : g1 + g2 + g3 = (a2 + b2 + c2) / 2 := by rw [hg1, hg2, hg3]; ring
  clear_value g1 g2 g3 x
  have k2 : g2 = x * ((a2 + b2 + c2) / 2) := by
    rw [← hsum]; linear_combination (-1 : ℝ) * f1' + f2' - g2 * hxdef
  have k1 : g1 = z * ((a2 + b2 + c2) / 2) := by
    have : (g1 - z * ((a2 + b2 + c2) / 2)) * x = 0 := by
      linear_combination f1' + z * k2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hx.ne')
  rw [hg1] at k1
  rw [hg2, hxdef] at k2
  have hU : 0 < a2 * b2 + b2 * c2 + c2 * a2 := by positivity
  congr 1 <;> congr 1 <;> rw [eq_div_iff hU.ne']
  · linear_combination (a2 + b2) * k1 + a2 * k2
  · linear_combination (-b2) * k1 + c2 * k2

/-- NEW PROOF: uniqueness of the second Brocard point among interior points. -/
lemma brocard2_unique (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω B A = ∠ Ω C B ∧ ∠ Ω C B = ∠ Ω A C) :
    Ω = (ClassicalTri A B C h).brocardPoint₂ := by
  obtain ⟨y, z, hy, hz, hx, hΩc⟩ := coords_of_interior A B C h Ω hΩ.1
  obtain ⟨hpu, hqv, hruv, hD, ha, hb, hc⟩ := tri_facts A B C h
  have hA : A -ᵥ A = (0 : ℝ) • (B -ᵥ A) + (0 : ℝ) • (C -ᵥ A) := by simp
  have hB : B -ᵥ A = (1 : ℝ) • (B -ᵥ A) + (0 : ℝ) • (C -ᵥ A) := by simp
  have hC : C -ᵥ A = (0 : ℝ) • (B -ᵥ A) + (1 : ℝ) • (C -ᵥ A) := by simp
  have hBr : (ClassicalTri A B C h).brocardPoint₂ -ᵥ A =
      (dist C A ^ 2 * dist A B ^ 2 / (dist B C ^ 2 * dist C A ^ 2 + dist C A ^ 2 * dist A B ^ 2 +
        dist A B ^ 2 * dist B C ^ 2)) • (B -ᵥ A) +
      (dist A B ^ 2 * dist B C ^ 2 / (dist B C ^ 2 * dist C A ^ 2 + dist C A ^ 2 * dist A B ^ 2 +
        dist A B ^ 2 * dist B C ^ 2)) • (C -ᵥ A) :=
    Brocard.brocardPoint₂_coords (ClassicalTri A B C h) rfl rfl rfl
  have e1 := congrArg Real.cot hΩ.2.1
  have e2 := congrArg Real.cot hΩ.2.2
  rw [Brocard.cot_angle_coords (d := z) hpu hqv hruv hΩc hB hA (by
        rw [show (y - 1) * (0 - 0) - (0 - 1) * (z - 0) = z by ring, abs_of_pos hz]),
    Brocard.cot_angle_coords (d := 1 - y - z) hpu hqv hruv hΩc hC hB (by
        rw [show (y - 0) * (0 - 1) - (1 - 0) * (z - 1) = 1 - y - z by ring, abs_of_pos hx])] at e1
  rw [Brocard.cot_angle_coords (d := 1 - y - z) hpu hqv hruv hΩc hC hB (by
        rw [show (y - 0) * (0 - 1) - (1 - 0) * (z - 1) = 1 - y - z by ring, abs_of_pos hx]),
    Brocard.cot_angle_coords (d := y) hpu hqv hruv hΩc hA hC (by
        rw [show (y - 0) * (1 - 0) - (0 - 0) * (z - 0) = y by ring, abs_of_pos hy])] at e2
  apply vsub_left_cancel (p := A)
  rw [hΩc, hBr]
  have hs := Real.sqrt_pos.2 hD
  generalize √(dist A B ^ 2 * dist C A ^ 2 -
    ((dist C A ^ 2 + dist A B ^ 2 - dist B C ^ 2) / 2) ^ 2) = s at *
  generalize dist B C ^ 2 = a2 at *
  generalize dist C A ^ 2 = b2 at *
  generalize dist A B ^ 2 = c2 at *
  unfold Brocard.gram at e1 e2
  rw [div_eq_div_iff (by positivity) (by positivity)] at e1 e2
  set x := 1 - y - z with hxdef
  set g1 := (y - 1) * (0 - 1) * c2 + ((y - 1) * (0 - 0) + (z - 0) * (0 - 1)) *
    ((b2 + c2 - a2) / 2) + (z - 0) * (0 - 0) * b2 with hg1
  set g2 := (y - 0) * (1 - 0) * c2 + ((y - 0) * (0 - 1) + (z - 1) * (1 - 0)) *
    ((b2 + c2 - a2) / 2) + (z - 1) * (0 - 1) * b2 with hg2
  set g3 := (y - 0) * (0 - 0) * c2 + ((y - 0) * (1 - 0) + (z - 0) * (0 - 0)) *
    ((b2 + c2 - a2) / 2) + (z - 0) * (1 - 0) * b2 with hg3
  have f1 : (g1 * x - g2 * z) * s = 0 := by linear_combination e1
  have f2 : (g2 * y - g3 * x) * s = 0 := by linear_combination e2
  have f1' := (mul_eq_zero.1 f1).resolve_right hs.ne'
  have f2' := (mul_eq_zero.1 f2).resolve_right hs.ne'
  have hsum : g1 + g2 + g3 = (a2 + b2 + c2) / 2 := by rw [hg1, hg2, hg3]; ring
  clear_value g1 g2 g3 x
  have k2 : g2 = x * ((a2 + b2 + c2) / 2) := by
    rw [← hsum]; linear_combination (-1 : ℝ) * f1' + f2' - g2 * hxdef
  have k1 : g1 = z * ((a2 + b2 + c2) / 2) := by
    have : (g1 - z * ((a2 + b2 + c2) / 2)) * x = 0 := by
      linear_combination f1' + z * k2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hx.ne')
  rw [hg1] at k1
  rw [hg2, hxdef] at k2
  have hU : 0 < a2 * b2 + b2 * c2 + c2 * a2 := by positivity
  congr 1 <;> congr 1 <;> rw [eq_div_iff hU.ne']
  · linear_combination c2 * k1 + (b2 + c2) * k2
  · linear_combination (-(a2 + c2)) * k1 - c2 * k2


lemma brocard1_interior (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    (ClassicalTri A B C h).brocardPoint₁ ∈ interior (convexHull ℝ {A, B, C}) := by
  obtain ⟨-, -, -, -, ha, hb, hc⟩ := tri_facts A B C h
  refine interior_of_weights A B C h _ ?_ ?_
  · change ∑ i, (fun i => ![1 / dist C A ^ 2, 1 / dist A B ^ 2, 1 / dist B C ^ 2] i /
      (1 / dist B C ^ 2 + 1 / dist C A ^ 2 + 1 / dist A B ^ 2)) i = 1
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp; ring
  · intro i
    change 0 < ![1 / dist C A ^ 2, 1 / dist A B ^ 2, 1 / dist B C ^ 2] i /
      (1 / dist B C ^ 2 + 1 / dist C A ^ 2 + 1 / dist A B ^ 2)
    fin_cases i <;> simp <;> positivity

lemma brocard2_interior (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    (ClassicalTri A B C h).brocardPoint₂ ∈ interior (convexHull ℝ {A, B, C}) := by
  obtain ⟨-, -, -, -, ha, hb, hc⟩ := tri_facts A B C h
  refine interior_of_weights A B C h _ ?_ ?_
  · change ∑ i, (fun i => ![1 / dist A B ^ 2, 1 / dist B C ^ 2, 1 / dist C A ^ 2] i /
      (1 / dist B C ^ 2 + 1 / dist C A ^ 2 + 1 / dist A B ^ 2)) i = 1
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp; ring
  · intro i
    change 0 < ![1 / dist A B ^ 2, 1 / dist B C ^ 2, 1 / dist C A ^ 2] i /
      (1 / dist B C ^ 2 + 1 / dist C A ^ 2 + 1 / dist A B ^ 2)
    fin_cases i <;> simp <;> positivity

lemma brocard1_spec (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    let Ω := (ClassicalTri A B C h).brocardPoint₁
    Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A :=
  ⟨brocard1_interior A B C h, l14_brocardPoint₁_angles (ClassicalTri A B C h)⟩

lemma brocard2_spec (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    let Ω' := (ClassicalTri A B C h).brocardPoint₂
    Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C :=
  ⟨brocard2_interior A B C h, l14_brocardPoint₂_angles (ClassicalTri A B C h)⟩

theorem cov_S3a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃! Ω : Pt, Ω ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A := by
  refine ⟨(ClassicalTri A B C h).brocardPoint₁, brocard1_spec A B C h, ?_⟩
  intro Ω hΩ
  exact brocard1_unique A B C h Ω hΩ

theorem cov_S3b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃! Ω' : Pt, Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C := by
  refine ⟨(ClassicalTri A B C h).brocardPoint₂, brocard2_spec A B C h, ?_⟩
  intro Ω hΩ
  exact brocard2_unique A B C h Ω hΩ

theorem cov_S3c (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω Ω' : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A)
    (hΩ' : Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C) :
    ∠ Ω A B = ∠ Ω' B A := by
  rw [brocard1_unique A B C h Ω hΩ, brocard2_unique A B C h Ω' hΩ']
  exact (Brocard.brocardPoint₁_angles (ClassicalTri A B C h)).1.trans
    (Brocard.brocardPoints_isogonal (ClassicalTri A B C h)).2.1

theorem cov_S3d (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A) :
    Real.cot (∠ Ω A B) = Real.cot (∠ B A C) + Real.cot (∠ C B A) + Real.cot (∠ A C B) ∧
      Real.cot (∠ B A C) + Real.cot (∠ C B A) + Real.cot (∠ A C B) =
        (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (4 * ClassicalArea A B C) := by
  rw [brocard1_unique A B C h Ω hΩ]
  have e1 : Real.cot (∠ (ClassicalTri A B C h).brocardPoint₁ A B) =
      Real.cot (∠ B A C) + Real.cot (∠ A B C) + Real.cot (∠ A C B) :=
    Brocard.cot_brocardAngle_eq_sum_cot (ClassicalTri A B C h)
  have e2 : Real.cot (∠ (ClassicalTri A B C h).brocardPoint₁ A B) =
      (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (4 * ClassicalArea A B C) :=
    Brocard.cot_brocardAngle_eq_div_area (ClassicalTri A B C h)
  rw [angle_comm C B A]
  exact ⟨e1, e1.symm.trans e2⟩

theorem cov_S3e (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A) :
    0 < ∠ Ω A B ∧ ∠ Ω A B ≤ Real.pi / 6 := by
  rw [brocard1_unique A B C h Ω hΩ]
  exact l14_brocardAngle_pos_le (ClassicalTri A B C h)

lemma isog_vertex (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    (ClassicalTri A B C h).brocardPoint₂ ∈
      ClassicalIsogonalLine A B C (ClassicalTri A B C h).brocardPoint₁ := by
  obtain ⟨-, -, -, -, ha, hb, hc⟩ := tri_facts A B C h
  have h1 : (ClassicalTri A B C h).brocardPoint₁ -ᵥ A =
      (dist B C ^ 2 * dist C A ^ 2 / (dist B C ^ 2 * dist C A ^ 2 + dist C A ^ 2 * dist A B ^ 2 +
        dist A B ^ 2 * dist B C ^ 2)) • (B -ᵥ A) +
      (dist C A ^ 2 * dist A B ^ 2 / (dist B C ^ 2 * dist C A ^ 2 + dist C A ^ 2 * dist A B ^ 2 +
        dist A B ^ 2 * dist B C ^ 2)) • (C -ᵥ A) :=
    Brocard.brocardPoint₁_coords (ClassicalTri A B C h) rfl rfl rfl
  have h2 : (ClassicalTri A B C h).brocardPoint₂ -ᵥ A =
      (dist C A ^ 2 * dist A B ^ 2 / (dist B C ^ 2 * dist C A ^ 2 + dist C A ^ 2 * dist A B ^ 2 +
        dist A B ^ 2 * dist B C ^ 2)) • (B -ᵥ A) +
      (dist A B ^ 2 * dist B C ^ 2 / (dist B C ^ 2 * dist C A ^ 2 + dist C A ^ 2 * dist A B ^ 2 +
        dist A B ^ 2 * dist B C ^ 2)) • (C -ᵥ A) :=
    Brocard.brocardPoint₂_coords (ClassicalTri A B C h) rfl rfl rfl
  have hR := refl_vec A B C _ (ne01 A B C h) (ne02 A B C h) _ _ h1
  unfold ClassicalIsogonalLine
  rw [← vsub_vadd (ClassicalTri A B C h).brocardPoint₂ A, vadd_left_mem_affineSpan_pair]
  have hb' : 0 < dist C A := dist_pos.2 (ne02 A B C h).symm
  have hc' : 0 < dist A B := dist_pos.2 (ne01 A B C h)
  refine ⟨dist A B / dist C A, ?_⟩
  rw [hR, h2, dist_comm A C]
  match_scalars <;> field_simp

lemma hull_rot (A B C : Pt) : ({B, C, A} : Set Pt) = {A, B, C} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

lemma indep_rot (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    AffineIndependent ℝ ![B, C, A] := by
  rw [affineIndependent_iff_not_collinear_set] at h ⊢
  rwa [hull_rot]

theorem cov_S4 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω Ω' : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A)
    (hΩ' : Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C) :
    ClassicalIsogonalConj A B C Ω Ω' ∧
      dist Ω (ClassicalTri A B C h).circumcenter = dist Ω' (ClassicalTri A B C h).circumcenter := by
  have h' := indep_rot A B C h
  have h'' := indep_rot B C A h'
  have e1 := brocard1_unique A B C h Ω hΩ
  have e2 := brocard2_unique A B C h Ω' hΩ'
  have f1 : Ω = (ClassicalTri B C A h').brocardPoint₁ :=
    brocard1_unique B C A h' Ω ⟨by rw [hull_rot]; exact hΩ.1, hΩ.2.2, (hΩ.2.1.trans hΩ.2.2).symm⟩
  have f2 : Ω' = (ClassicalTri B C A h').brocardPoint₂ :=
    brocard2_unique B C A h' Ω' ⟨by rw [hull_rot]; exact hΩ'.1, hΩ'.2.2, (hΩ'.2.1.trans hΩ'.2.2).symm⟩
  have g1 : Ω = (ClassicalTri C A B h'').brocardPoint₁ :=
    brocard1_unique C A B h'' Ω ⟨by rw [hull_rot, hull_rot]; exact hΩ.1,
      (hΩ.2.1.trans hΩ.2.2).symm, hΩ.2.1⟩
  have g2 : Ω' = (ClassicalTri C A B h'').brocardPoint₂ :=
    brocard2_unique C A B h'' Ω' ⟨by rw [hull_rot, hull_rot]; exact hΩ'.1,
      (hΩ'.2.1.trans hΩ'.2.2).symm, hΩ'.2.1⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [e1, e2]; exact isog_vertex A B C h
  · rw [f1, f2]; exact isog_vertex B C A h'
  · rw [g1, g2]; exact isog_vertex C A B h''
  · rw [e1, e2, dist_comm, dist_comm (ClassicalTri A B C h).brocardPoint₂]
    exact Brocard.dist_circumcenter_brocardPoint (ClassicalTri A B C h)

theorem cov_S5 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω Ω' : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A)
    (hΩ' : Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C) :
    let O := (ClassicalTri A B C h).circumcenter
    let K := ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2)
    dist Ω (midpoint ℝ O K) = dist O K / 2 ∧ dist Ω' (midpoint ℝ O K) = dist O K / 2 := by
  intro O K
  rw [brocard1_unique A B C h Ω hΩ, brocard2_unique A B C h Ω' hΩ']
  have hc := Brocard.brocardCircle (ClassicalTri A B C h)
  exact ⟨hc _ (by simp), hc _ (by simp)⟩

lemma meet_unique (X Y K : Pt) (L : AffineSubspace ℝ Pt) (D : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (hX : X ∈ L) (hY : Y ∈ L) (hXK : X ∈ AffineSubspace.mk' K D) (hYK : Y ∈ AffineSubspace.mk' K D)
    (hLD : ∀ w, w ∈ L.direction → w ∈ D → w = 0) : X = Y := by
  have h1 := AffineSubspace.vsub_mem_direction hX hY
  have h2 := AffineSubspace.vsub_mem_direction hXK hYK
  rw [AffineSubspace.direction_mk'] at h2
  exact vsub_eq_zero_iff_eq.1 (hLD _ h1 h2)

lemma lines_transverse (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (P₁ P₂ Q₁ Q₂ : Pt)
    {x1 y1 x2 y2 : ℝ} (hp : P₂ -ᵥ P₁ = x1 • (B -ᵥ A) + y1 • (C -ᵥ A))
    (hq : Q₂ -ᵥ Q₁ = x2 • (B -ᵥ A) + y2 • (C -ᵥ A)) (hdet : x1 * y2 - x2 * y1 ≠ 0) :
    ∀ w, w ∈ (line[ℝ, P₁, P₂]).direction → w ∈ (line[ℝ, Q₁, Q₂]).direction → w = 0 := by
  obtain ⟨hpu, hqv, hruv, hD, -, -, -⟩ := tri_facts A B C h
  intro w h1 h2
  rw [direction_affineSpan, mem_vectorSpan_pair_rev] at h1 h2
  obtain ⟨r, rfl⟩ := h1
  obtain ⟨s, hs⟩ := h2
  rw [hp] at hs ⊢
  rw [hq] at hs
  have e : (s * x2) • (B -ᵥ A) + (s * y2) • (C -ᵥ A) = (r * x1) • (B -ᵥ A) + (r * y1) • (C -ᵥ A) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul] at hs; exact hs
  obtain ⟨e1, e2⟩ := Brocard.coords_eq hpu hqv hruv hD e
  have : r * (x1 * y2 - x2 * y1) = 0 := by linear_combination y2 * e1.symm - x2 * e2.symm
  rw [(mul_eq_zero.1 this).resolve_right hdet]
  simp

theorem cov_S6 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C])
    (P₁ P₂ P₃ P₄ P₅ P₆ : Pt) :
    let K := ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2)
    P₁ ∈ line[ℝ, A, B] → P₁ ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction →
    P₂ ∈ line[ℝ, A, C] → P₂ ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction →
    P₃ ∈ line[ℝ, B, C] → P₃ ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction →
    P₄ ∈ line[ℝ, B, A] → P₄ ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction →
    P₅ ∈ line[ℝ, C, A] → P₅ ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction →
    P₆ ∈ line[ℝ, C, B] → P₆ ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction →
    ∃ ρ : ℝ, ∀ P ∈ ({P₁, P₂, P₃, P₄, P₅, P₆} : Set Pt),
      dist P (midpoint ℝ (ClassicalTri A B C h).circumcenter K) = ρ := by
  intro K h₁ h₁' h₂ h₂' h₃ h₃' h₄ h₄' h₅ h₅' h₆ h₆'
  set t := ClassicalTri A B C h
  have hm := Brocard.lemoinePoints_mem t
  have hcirc := Brocard.lemoineCircle t
  change (_ ∈ line[ℝ, C, A] ∧ _ ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction) ∧
    (_ ∈ line[ℝ, A, B] ∧ _ ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction) ∧
    (_ ∈ line[ℝ, B, C] ∧ _ ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction) ∧
    (_ ∈ line[ℝ, A, B] ∧ _ ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction) ∧
    (_ ∈ line[ℝ, B, C] ∧ _ ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction) ∧
    (_ ∈ line[ℝ, C, A] ∧ _ ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction) at hm
  obtain ⟨⟨m0, m0'⟩, ⟨m1, m1'⟩, ⟨m2, m2'⟩, ⟨m3, m3'⟩, ⟨m4, m4'⟩, ⟨m5, m5'⟩⟩ := hm
  have vAB : B -ᵥ A = (1 : ℝ) • (B -ᵥ A) + (0 : ℝ) • (C -ᵥ A) := by simp
  have vCA : A -ᵥ C = (0 : ℝ) • (B -ᵥ A) + (-1 : ℝ) • (C -ᵥ A) := by
    rw [← neg_vsub_eq_vsub_rev]; simp
  have vBC : C -ᵥ B = (-1 : ℝ) • (B -ᵥ A) + (1 : ℝ) • (C -ᵥ A) := by
    rw [← vsub_sub_vsub_cancel_right C B A]; module
  have vAC : C -ᵥ A = (0 : ℝ) • (B -ᵥ A) + (1 : ℝ) • (C -ᵥ A) := by simp
  have vBA : A -ᵥ B = (-1 : ℝ) • (B -ᵥ A) + (0 : ℝ) • (C -ᵥ A) := by
    rw [← neg_vsub_eq_vsub_rev]; module
  have vCB : B -ᵥ C = (1 : ℝ) • (B -ᵥ A) + (-1 : ℝ) • (C -ᵥ A) := by
    rw [← vsub_sub_vsub_cancel_right B C A]; module
  have lAC : line[ℝ, A, C] = line[ℝ, C, A] := by rw [Set.pair_comm]
  have lBA : line[ℝ, B, A] = line[ℝ, A, B] := by rw [Set.pair_comm]
  have lCB : line[ℝ, C, B] = line[ℝ, B, C] := by rw [Set.pair_comm]
  have e1 : P₁ = t.lemoinePoints 1 :=
    meet_unique _ _ K _ _ h₁ m1 h₁' m1' (lines_transverse A B C h _ _ _ _ vAB vBC (by norm_num))
  have e2 : P₂ = t.lemoinePoints 0 :=
    meet_unique _ _ K _ _ (lAC ▸ h₂) m0 h₂' m0' (lines_transverse A B C h _ _ _ _ vCA vBC (by norm_num))
  have e3 : P₃ = t.lemoinePoints 2 :=
    meet_unique _ _ K _ _ h₃ m2 h₃' m2' (lines_transverse A B C h _ _ _ _ vBC vCA (by norm_num))
  have e4 : P₄ = t.lemoinePoints 3 :=
    meet_unique _ _ K _ _ (lBA ▸ h₄) m3 h₄' m3' (lines_transverse A B C h _ _ _ _ vAB vCA (by norm_num))
  have e5 : P₅ = t.lemoinePoints 5 :=
    meet_unique _ _ K _ _ h₅ m5 h₅' m5' (lines_transverse A B C h _ _ _ _ vCA vAB (by norm_num))
  have e6 : P₆ = t.lemoinePoints 4 :=
    meet_unique _ _ K _ _ (lCB ▸ h₆) m4 h₆' m4' (lines_transverse A B C h _ _ _ _ vBC vAB (by norm_num))
  refine ⟨dist (t.lemoinePoints 0) (midpoint ℝ t.circumcenter t.symmedianPoint), ?_⟩
  intro P hP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e1]; exact hcirc 1
  · rw [e2]; exact hcirc 0
  · rw [e3]; exact hcirc 2
  · rw [e4]; exact hcirc 3
  · rw [e5]; exact hcirc 5
  · rw [e6]; exact hcirc 4


theorem cov_S2a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ClassicalPedalCentroid A B C (ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2)
      (dist A B ^ 2)) = ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2) := by
  exact l14_symmedianPoint_eq_centroid_pedal (ClassicalTri A B C h)

theorem cov_S2b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (P : Pt)
    (hP : ClassicalPedalCentroid A B C P = P) :
    P = ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2) := by
  exact l14_eq_symmedianPoint_of_eq_centroid_pedal (ClassicalTri A B C h) P hP

theorem cov_S7 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (u v : Pt)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : inner ℝ u v = 0)
    -- EXTRA HYPOTHESIS: neither line is parallel to (or equal to) a side line, i.e. each meets
    -- each side line in exactly one point. Without this, in a right triangle a line through
    -- H = the right-angle vertex can coincide with a side line, the "segment" is not
    -- determined, and the statement (read with arbitrary intersection points) is false.
    (hu₁ : u ∉ (line[ℝ, B, C]).direction) (hu₂ : u ∉ (line[ℝ, C, A]).direction)
    (hu₃ : u ∉ (line[ℝ, A, B]).direction)
    (hv₁ : v ∉ (line[ℝ, B, C]).direction) (hv₂ : v ∉ (line[ℝ, C, A]).direction)
    (hv₃ : v ∉ (line[ℝ, A, B]).direction)
    (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Pt) :
    let H := (ClassicalTri A B C h).orthocenter
    let ℓ₁ := AffineSubspace.mk' H (Submodule.span ℝ {u})
    let ℓ₂ := AffineSubspace.mk' H (Submodule.span ℝ {v})
    X₁ ∈ ℓ₁ → X₁ ∈ line[ℝ, B, C] → X₂ ∈ ℓ₂ → X₂ ∈ line[ℝ, B, C] →
    Y₁ ∈ ℓ₁ → Y₁ ∈ line[ℝ, C, A] → Y₂ ∈ ℓ₂ → Y₂ ∈ line[ℝ, C, A] →
    Z₁ ∈ ℓ₁ → Z₁ ∈ line[ℝ, A, B] → Z₂ ∈ ℓ₂ → Z₂ ∈ line[ℝ, A, B] →
    Collinear ℝ {midpoint ℝ X₁ X₂, midpoint ℝ Y₁ Y₂, midpoint ℝ Z₁ Z₂} := by
  intro H ℓ₁ ℓ₂ hX₁ hX₁' hX₂ hX₂' hY₁ hY₁' hY₂ hY₂' hZ₁ hZ₁' hZ₂ hZ₂'
  exact l14_drozFarny (ClassicalTri A B C h) u v huv hu₁ hu₂ hu₃ hv₁ hv₂ hv₃
    hX₁' hX₁ hX₂' hX₂ hY₁' hY₁ hY₂' hY₂ hZ₁' hZ₁ hZ₂' hZ₂

#print axioms cov_S1a
#print axioms cov_S1b
#print axioms cov_S2a
#print axioms cov_S2b
#print axioms cov_S3a
#print axioms cov_S3b
#print axioms cov_S3c
#print axioms cov_S3d
#print axioms cov_S3e
#print axioms cov_S4
#print axioms cov_S5
#print axioms cov_S6
#print axioms cov_S7

end L15CmpS
