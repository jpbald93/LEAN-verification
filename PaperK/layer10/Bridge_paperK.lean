import PaperK.LieCore
import PaperK.TwoD
import PaperK.ThreeD

/-!
# Paper K, Layer 10: definition bridges

One lemma (or a short cluster) per locally-defined notion, tying it to the standard Mathlib
notion it stands for.

Conventions used throughout.
* Euclidean points are `EuclideanSpace ℝ (Fin 2)` (resp. `Fin 3`), written `!₂[x, y]`.
  `ℝ × ℝ` (used by `PaperK.pt` and Prop 3.1) carries the sup metric in Mathlib, so all metric
  bridges go through `!₂[(pt X).1, (pt X).2]`; the affine statements (collinearity) stay in `ℝ × ℝ`.
* An affine cycle `X` with `v = X 3 = 1` (resp. `X 4 = 1` in ℝ³) and `B X X = 0` is the oriented
  circle of centre `(X 1, X 2)` and signed radius `X 0`; its Mathlib sphere is
  `⟨!₂[X 1, X 2], X 0⟩` when `X 0 ≥ 0`, and `⟨!₂[X 1, X 2], -X 0⟩` for the opposite orientation.
* Sign convention: `B` is the NEGATIVE of the usual Lie product `(·|·)` on the centre/radius part,
  so `2 · B X Y = dist(c, c')² − (r − r')²` (Lie product `(X|Y) = −B`), and for a point cycle
  `B = +½ · Sphere.power`, while the equal-power constant is `−B(P,P)/P₃²`.  Every lemma below states that sign explicitly.
-/

open EuclideanGeometry

namespace PaperK

/-! ## Coordinates -/

/-- Squared Euclidean distance of two planar points, in coordinates. -/
theorem bridge_dist_sq (a b c d : ℝ) :
    dist (!₂[a, b]) (!₂[c, d]) ^ 2 = (a - c) ^ 2 + (b - d) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

lemma eq_iff_sq_eq {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) : x = r ↔ x ^ 2 = r ^ 2 :=
  (pow_left_inj₀ hx hr two_ne_zero).symm

/-! ## `G`, `B`: the Gram matrix is the matrix of `B` as a Mathlib bilinear map -/

/-- `B` is the bilinear map `Matrix.toLinearMap₂' ℝ G` of the Gram matrix `G`. -/
theorem bridge_B_toLinearMap₂ (X Y : Fin 5 → ℝ) : B X Y = Matrix.toLinearMap₂' ℝ G X Y := by
  rw [Matrix.toLinearMap₂'_apply', B_eq_dot_G]

/-! ## `cofactor` vs `Matrix.det` -/

/-- Pairing the cofactor vector with `v` is the determinant of `M` with `v` prepended as a row
(Laplace expansion along row 0, `Matrix.det_succ_row_zero`). -/
theorem bridge_cofactor_det (M : Matrix (Fin 4) (Fin 5) ℝ) (v : Fin 5 → ℝ) :
    v ⬝ᵥ cofactor M = (Matrix.of (Fin.cons v fun j => M j) : Matrix (Fin 5) (Fin 5) ℝ).det := by
  rw [Matrix.det_succ_row_zero]
  simp only [dotProduct, cofactor]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Matrix.of (Fin.cons v fun j => M j) : Matrix (Fin 5) (Fin 5) ℝ).submatrix Fin.succ
      k.succAbove = M.submatrix id k.succAbove := by
    ext a b; simp
  rw [this]; simp; ring

/-! ## `pt` vs the concrete centre -/

/-- `pt X = (c / v)`.  This is `rfl`: the two sides are literally the definition of `pt`. -/
theorem bridge_pt (X : Fin 5 → ℝ) : pt X = (X 1 / X 3, X 2 / X 3) := rfl

/-- For a normalised cycle (`v = 1`), `pt X` is its centre `(X 1, X 2)`. -/
theorem bridge_pt_normalised (X : Fin 5 → ℝ) (h : X 3 = 1) : pt X = (X 1, X 2) := by
  simp [pt, h]

/-! ## `B` vs Euclidean distance, `Sphere.IsExtTangent`, `Sphere.IsIntTangent`, `Sphere.power` -/

/-- **Sign stated.** For normalised affine cycles, `2·B X Y = dist(c_X, c_Y)² − (r_X − r_Y)²`. -/
theorem bridge_B_dist (X Y : Fin 5 → ℝ) (hX : B X X = 0) (hY : B Y Y = 0)
    (hX3 : X 3 = 1) (hY3 : Y 3 = 1) :
    2 * B X Y = dist (!₂[X 1, X 2]) (!₂[Y 1, Y 2]) ^ 2 - (X 0 - Y 0) ^ 2 := by
  have h := tangency_identity X Y hX hY
  rw [hX3, hY3] at h
  rw [bridge_dist_sq]
  linear_combination -h

/-- `B X Y = 0` ⇔ the oriented tangency equation `dist(c_X, c_Y)² = (r_X − r_Y)²`. -/
theorem bridge_B_eq_zero_iff_dist (X Y : Fin 5 → ℝ) (hX : B X X = 0) (hY : B Y Y = 0)
    (hX3 : X 3 = 1) (hY3 : Y 3 = 1) :
    B X Y = 0 ↔ dist (!₂[X 1, X 2]) (!₂[Y 1, Y 2]) ^ 2 = (X 0 - Y 0) ^ 2 := by
  have h := bridge_B_dist X Y hX hY hX3 hY3
  constructor <;> intro h' <;> linarith

/-- Opposite orientations (`r_X ≥ 0 ≥ r_Y`): `B X Y = 0` ⇔ Mathlib external tangency of
`⟨c_X, r_X⟩` and `⟨c_Y, −r_Y⟩`. -/
theorem bridge_B_isExtTangent (X Y : Fin 5 → ℝ) (hX : B X X = 0) (hY : B Y Y = 0)
    (hX3 : X 3 = 1) (hY3 : Y 3 = 1) (hr : 0 ≤ X 0) (hr' : Y 0 ≤ 0) :
    B X Y = 0 ↔ (⟨!₂[X 1, X 2], X 0⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).IsExtTangent
      ⟨!₂[Y 1, Y 2], -Y 0⟩ := by
  rw [Sphere.isExtTangent_iff_dist_center, bridge_B_eq_zero_iff_dist X Y hX hY hX3 hY3]
  constructor
  · intro h
    refine ⟨?_, hr, by linarith⟩
    rw [eq_iff_sq_eq dist_nonneg (by linarith), h]; ring
  · rintro ⟨h, -, -⟩
    simp only at h
    rw [h]; ring

/-- Equal orientations (`0 ≤ r_X ≤ r_Y`): `B X Y = 0` ⇔ Mathlib internal tangency of
`⟨c_X, r_X⟩` inside `⟨c_Y, r_Y⟩`. -/
theorem bridge_B_isIntTangent (X Y : Fin 5 → ℝ) (hX : B X X = 0) (hY : B Y Y = 0)
    (hX3 : X 3 = 1) (hY3 : Y 3 = 1) (hr : 0 ≤ X 0) (hrr : X 0 ≤ Y 0) :
    B X Y = 0 ↔ (⟨!₂[X 1, X 2], X 0⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).IsIntTangent
      ⟨!₂[Y 1, Y 2], Y 0⟩ := by
  rw [Sphere.isIntTangent_iff_dist_center, bridge_B_eq_zero_iff_dist X Y hX hY hX3 hY3]
  constructor
  · intro h
    refine ⟨?_, hr, by linarith⟩
    rw [eq_iff_sq_eq dist_nonneg (by linarith), h]; ring
  · rintro ⟨h, -, -⟩
    simp only at h
    rw [h]; ring

/-- **Sign stated.** Radius-0 case: for a point cycle `X` (`r_X = 0`) and a cycle `Y`,
`B X Y = ½ · Sphere.power ⟨c_Y, r_Y⟩ c_X`. -/
theorem bridge_B_power (X Y : Fin 5 → ℝ) (hX : B X X = 0) (hY : B Y Y = 0)
    (hX3 : X 3 = 1) (hY3 : Y 3 = 1) (hX0 : X 0 = 0) :
    B X Y = (1 / 2) * (⟨!₂[Y 1, Y 2], Y 0⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power
      (!₂[X 1, X 2]) := by
  have h := bridge_B_dist X Y hX hY hX3 hY3
  rw [hX0] at h
  unfold Sphere.power
  simp only
  linear_combination (1 / 2 : ℝ) * h

/-! ## `power` (Laguerre power) vs `Sphere.power` -/

/-- The Laguerre power of `(p, ρ)` w.r.t. `Y` is the Mathlib power of `p` w.r.t. the sphere of
centre `c_Y` and radius `ρ − r_Y` (the tangential-distance sphere).  Holds for every `Y`. -/
theorem bridge_power_sphere (p : ℝ × ℝ) (ρ : ℝ) (Y : Fin 5 → ℝ) :
    power p ρ Y = (⟨!₂[Y 1, Y 2], ρ - Y 0⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power
      (!₂[p.1, p.2]) := by
  unfold power Sphere.power
  simp only
  rw [bridge_dist_sq]

/-- **Sign stated.** The equal-power constant of `power_eq_of_B_eq_zero` as a Mathlib power:
for each normalised cycle `Y ⊥_B P`,
`Sphere.power ⟨c_Y, ρ − r_Y⟩ P_X = −B(P,P)/P₃²` with `ρ = P 0 / P 3`. -/
theorem bridge_power_eq_const_sphere (P Y : Fin 5 → ℝ) (hP3 : P 3 ≠ 0) (hv : Y 3 = 1)
    (hnull : B Y Y = 0) (h : B P Y = 0) :
    (⟨!₂[Y 1, Y 2], P 0 / P 3 - Y 0⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power
      (!₂[P 1 / P 3, P 2 / P 3]) = -B P P / (P 3) ^ 2 := by
  have e := bridge_power_sphere (pt P) (P 0 / P 3) Y
  rw [power_eq_of_B_eq_zero P Y hP3 hv hnull h] at e
  exact e.symm

/-- Radius-0 specialisation (`P 0 = 0`, i.e. `ρ = 0`): the Mathlib power of `P_X` w.r.t. each
cycle's own sphere `⟨c_Y, r_Y⟩` is the constant `−B(P,P)/P₃²`. -/
theorem bridge_power_eq_const_sphere_rho0 (P Y : Fin 5 → ℝ) (hP3 : P 3 ≠ 0) (hP0 : P 0 = 0)
    (hv : Y 3 = 1) (hnull : B Y Y = 0) (h : B P Y = 0) :
    (⟨!₂[Y 1, Y 2], Y 0⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power
      (!₂[P 1 / P 3, P 2 / P 3]) = -B P P / (P 3) ^ 2 := by
  rw [← bridge_power_eq_const_sphere P Y hP3 hv hnull h]
  unfold Sphere.power
  simp only
  rw [hP0]; ring

/-! ## Coordinate determinant vs `Collinear` (in `ℝ × ℝ`, where Prop 3.1 lives) -/

/-- Three points of `ℝ × ℝ` are `Collinear` iff the coordinate determinant vanishes. -/
theorem bridge_collinear_iff_det (p q s : ℝ × ℝ) :
    Collinear ℝ ({p, q, s} : Set (ℝ × ℝ)) ↔
      (q.1 - p.1) * (s.2 - p.2) - (s.1 - p.1) * (q.2 - p.2) = 0 := by
  constructor
  · rw [collinear_iff_of_mem (Set.mem_insert p _)]
    rintro ⟨v, hv⟩
    obtain ⟨a, ha⟩ := hv q (by simp)
    obtain ⟨b, hb⟩ := hv s (by simp)
    rw [ha, hb]
    simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · intro h
    by_cases hq : q = p
    · subst hq
      rw [Set.insert_eq_of_mem (Set.mem_insert _ _)]
      exact collinear_pair ℝ q s
    rw [collinear_iff_of_mem (Set.mem_insert p _)]
    refine ⟨q - p, ?_⟩
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · by_cases h1 : q.1 - p.1 = 0
      · have h2 : q.2 - p.2 ≠ 0 := by
          intro h2; apply hq; ext <;> linarith
        have hs1 : (x.1 - p.1) * (q.2 - p.2) = 0 := by rw [h1] at h; linarith
        have hs1' : x.1 - p.1 = 0 := (mul_eq_zero.mp hs1).resolve_right h2
        refine ⟨(x.2 - p.2) / (q.2 - p.2), ?_⟩
        ext
        · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
          rw [h1]; linarith
        · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
          field_simp; ring
      · refine ⟨(x.1 - p.1) / (q.1 - p.1), ?_⟩
        ext
        · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
          field_simp; ring
        · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
          field_simp
          linear_combination h

end PaperK

namespace PaperK2

/-! ## Paper K2 (`TwoD`): `B`, `circ`, `pw`, `pconst`, `Equi`, `D3`, `Tangent` -/

/-- `PaperK2.B` and `PaperK.B` are the same form.  This is `rfl`: the two definitions have
literally the same body. -/
theorem bridge_B_eq (X Y : Fin 5 → ℝ) : B X Y = PaperK.B X Y := rfl

/-- `circ r a b` lies on the null cone (it is a genuine Lie cycle). -/
theorem bridge_circ_null (r a b : ℝ) : B (circ r a b) (circ r a b) = 0 := by
  simp [B, circ]; ring

/-- Centre and radius of `circ r a b`: its affine point is `(a, b)` and its radius slot is `r`. -/
theorem bridge_circ_centre_radius (r a b : ℝ) :
    PaperK.pt (circ r a b) = (a, b) ∧ circ r a b 0 = r ∧ circ r a b 3 = 1 := by
  simp [PaperK.pt, circ]

/-- **Sign stated.** `2·B(circ r a b, circ r' a' b') = dist((a,b),(a',b'))² − (r − r')²`. -/
theorem bridge_B_circ_dist (r a b r' a' b' : ℝ) :
    2 * B (circ r a b) (circ r' a' b') = dist (!₂[a, b]) (!₂[a', b']) ^ 2 - (r - r') ^ 2 := by
  rw [PaperK.bridge_dist_sq]
  simp [B, circ]; ring

/-- Point membership: `(x,y)` lies on the Mathlib sphere `⟨(a,b), r⟩` (`r ≥ 0`) iff the point
cycle `circ 0 x y` is `B`-orthogonal to `circ r a b`. -/
theorem bridge_circ_mem_sphere (x y r a b : ℝ) (hr : 0 ≤ r) :
    (!₂[x, y] : EuclideanSpace ℝ (Fin 2)) ∈ (⟨!₂[a, b], r⟩ : Sphere (EuclideanSpace ℝ (Fin 2)))
      ↔ B (circ 0 x y) (circ r a b) = 0 := by
  rw [EuclideanGeometry.mem_sphere]
  simp only
  rw [PaperK.eq_iff_sq_eq dist_nonneg hr]
  have e := bridge_B_circ_dist 0 x y r a b
  have e0 : ((0 : ℝ) - r) ^ 2 = r ^ 2 := by ring
  rw [e0] at e
  constructor <;> intro h <;> linarith

/-- **Sign stated.** `B(circ 0 x y, circ r a b) = ½ · Sphere.power ⟨(a,b), r⟩ (x,y)`. -/
theorem bridge_circ_power (x y r a b : ℝ) :
    B (circ 0 x y) (circ r a b)
      = (1 / 2) * (⟨!₂[a, b], r⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power (!₂[x, y]) := by
  have e := bridge_B_circ_dist 0 x y r a b
  unfold Sphere.power
  simp only
  linear_combination (1 / 2 : ℝ) * e

/-- `B`-orthogonality of oppositely oriented circles ⇔ Mathlib external tangency. -/
theorem bridge_circ_isExtTangent (r a b r' a' b' : ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r') :
    B (circ r a b) (circ (-r') a' b') = 0 ↔
      (⟨!₂[a, b], r⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).IsExtTangent ⟨!₂[a', b'], r'⟩ := by
  rw [Sphere.isExtTangent_iff_dist_center]
  simp only
  have e := bridge_B_circ_dist r a b (-r') a' b'
  constructor
  · intro h
    refine ⟨?_, hr, hr'⟩
    rw [PaperK.eq_iff_sq_eq dist_nonneg (by linarith)]
    rw [h] at e; linear_combination -e
  · rintro ⟨h, -, -⟩
    rw [h] at e
    linarith

/-- `B`-orthogonality of equally oriented circles with `0 ≤ r ≤ r'` ⇔ Mathlib internal
tangency of `⟨(a,b), r⟩` inside `⟨(a',b'), r'⟩`. -/
theorem bridge_circ_isIntTangent (r a b r' a' b' : ℝ) (hr : 0 ≤ r) (hrr : r ≤ r') :
    B (circ r a b) (circ r' a' b') = 0 ↔
      (⟨!₂[a, b], r⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).IsIntTangent ⟨!₂[a', b'], r'⟩ := by
  rw [Sphere.isIntTangent_iff_dist_center]
  simp only
  have e := bridge_B_circ_dist r a b r' a' b'
  constructor
  · intro h
    refine ⟨?_, hr, by linarith⟩
    rw [PaperK.eq_iff_sq_eq dist_nonneg (by linarith)]
    rw [h] at e; linear_combination -e
  · rintro ⟨h, -, -⟩
    rw [h] at e
    linarith

/-- `pw` is the Mathlib power of `P_X` w.r.t. the sphere of centre `(a,b)` and radius `ρ − r`,
`ρ = P 0 / P 3`.  Holds for every `P`. -/
theorem bridge_pw_sphere (P : Fin 5 → ℝ) (r a b : ℝ) :
    pw P r a b = (⟨!₂[a, b], P 0 / P 3 - r⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power
      (!₂[P 1 / P 3, P 2 / P 3]) := by
  unfold pw Sphere.power
  simp only
  rw [PaperK.bridge_dist_sq]

/-- **Sign stated.** The constant `pconst P` is `−B(P,P)/P₃²` (our `B = −(·|·)`). -/
theorem bridge_pconst_neg_B (P : Fin 5 → ℝ) (hP : P 3 ≠ 0) : pconst P = -B P P / (P 3) ^ 2 := by
  unfold pconst B
  field_simp
  ring

/-- `power_eq_const` in Mathlib terms: for each circle `B`-orthogonal to `P`,
`Sphere.power ⟨(a,b), ρ − r⟩ P_X = −B(P,P)/P₃²`. -/
theorem bridge_power_eq_const_sphere (P : Fin 5 → ℝ) (hP : P 3 ≠ 0) (r a b : ℝ)
    (h : B P (circ r a b) = 0) :
    (⟨!₂[a, b], P 0 / P 3 - r⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power
      (!₂[P 1 / P 3, P 2 / P 3]) = -B P P / (P 3) ^ 2 := by
  rw [← bridge_pw_sphere, power_eq_const P hP r a b h, bridge_pconst_neg_B P hP]

/-- Radius-0 specialisation (`P 0 = 0`): the Mathlib power of `P_X` w.r.t. each circle's own
sphere `⟨(a,b), r⟩` equals `−B(P,P)/P₃²`, hence is the same for every orthogonal circle. -/
theorem bridge_power_eq_const_sphere_rho0 (P : Fin 5 → ℝ) (hP : P 3 ≠ 0) (hP0 : P 0 = 0)
    (r a b : ℝ) (h : B P (circ r a b) = 0) :
    (⟨!₂[a, b], r⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power
      (!₂[P 1 / P 3, P 2 / P 3]) = -B P P / (P 3) ^ 2 := by
  rw [← bridge_power_eq_const_sphere P hP r a b h]
  unfold Sphere.power
  simp only
  rw [hP0]; ring

/-- `Equi` is Euclidean equidistance (`dist`) from the three points `(a i, b i)`. -/
theorem bridge_Equi_dist (x y : ℝ) (a b : Fin 3 → ℝ) :
    Equi x y a b ↔
      dist (!₂[x, y]) (!₂[a 0, b 0]) = dist (!₂[x, y]) (!₂[a 1, b 1]) ∧
      dist (!₂[x, y]) (!₂[a 0, b 0]) = dist (!₂[x, y]) (!₂[a 2, b 2]) := by
  rw [PaperK.eq_iff_sq_eq dist_nonneg dist_nonneg, PaperK.eq_iff_sq_eq dist_nonneg dist_nonneg,
    PaperK.bridge_dist_sq, PaperK.bridge_dist_sq, PaperK.bridge_dist_sq]
  rfl

/-- `D3 a b = 0` ⇔ the three centres are `Collinear` (so `D3 ≠ 0` is non-collinearity). -/
theorem bridge_D3_collinear (a b : Fin 3 → ℝ) :
    D3 a b = 0 ↔ Collinear ℝ ({(a 0, b 0), (a 1, b 1), (a 2, b 2)} : Set (ℝ × ℝ)) := by
  rw [PaperK.bridge_collinear_iff_det]
  rfl

/-- `Tangent` is the oriented tangency equation `dist² = (ρ − r)²`, i.e. `B`-orthogonality of
the two `circ` cycles. -/
theorem bridge_Tangent (x y ρ a b r : ℝ) :
    (Tangent x y ρ a b r ↔ dist (!₂[x, y]) (!₂[a, b]) ^ 2 = (ρ - r) ^ 2) ∧
    (Tangent x y ρ a b r ↔ B (circ ρ x y) (circ r a b) = 0) := by
  have e := bridge_B_circ_dist ρ x y r a b
  rw [PaperK.bridge_dist_sq] at e
  refine ⟨by rw [PaperK.bridge_dist_sq]; rfl, ?_⟩
  unfold Tangent
  constructor <;> intro h <;> linarith

end PaperK2

namespace PaperK3

/-! ## Paper K3 (`ThreeD`): `B`, `sph` vs Mathlib spheres in `EuclideanSpace ℝ (Fin 3)` -/

/-- Squared Euclidean distance in ℝ³, in coordinates. -/
theorem bridge_dist_sq3 (a b c d e f : ℝ) :
    dist (!₂[a, b, c]) (!₂[d, e, f]) ^ 2 = (a - d) ^ 2 + (b - e) ^ 2 + (c - f) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three, Real.dist_eq, sq_abs]

/-- **Sign stated.** `2·B(sph, sph') = dist(c, c')² − (r − r')²`. -/
theorem bridge_B_sph_dist (r a b c r' a' b' c' : ℝ) :
    2 * B (sph r a b c) (sph r' a' b' c')
      = dist (!₂[a, b, c]) (!₂[a', b', c']) ^ 2 - (r - r') ^ 2 := by
  rw [bridge_dist_sq3]
  simp [B, sph]; ring

/-- Point membership in the Mathlib sphere `⟨(a,b,c), r⟩` (`r ≥ 0`) ⇔ `B`-orthogonality of the
point cycle `sph 0 x y z` to `sph r a b c`. -/
theorem bridge_sph_mem_sphere (x y z r a b c : ℝ) (hr : 0 ≤ r) :
    (!₂[x, y, z] : EuclideanSpace ℝ (Fin 3))
        ∈ (⟨!₂[a, b, c], r⟩ : Sphere (EuclideanSpace ℝ (Fin 3)))
      ↔ B (sph 0 x y z) (sph r a b c) = 0 := by
  rw [EuclideanGeometry.mem_sphere]
  simp only
  rw [PaperK.eq_iff_sq_eq dist_nonneg hr]
  have e := bridge_B_sph_dist 0 x y z r a b c
  have e0 : ((0 : ℝ) - r) ^ 2 = r ^ 2 := by ring
  rw [e0] at e
  constructor <;> intro h <;> linarith

/-- **Sign stated.** `B(sph 0 x y z, sph r a b c) = ½ · Sphere.power ⟨(a,b,c), r⟩ (x,y,z)`. -/
theorem bridge_sph_power (x y z r a b c : ℝ) :
    B (sph 0 x y z) (sph r a b c)
      = (1 / 2) * (⟨!₂[a, b, c], r⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).power
          (!₂[x, y, z]) := by
  have e := bridge_B_sph_dist 0 x y z r a b c
  unfold Sphere.power
  simp only
  linear_combination (1 / 2 : ℝ) * e

/-- Oppositely oriented spheres: `B`-orthogonality ⇔ Mathlib external tangency. -/
theorem bridge_sph_isExtTangent (r a b c r' a' b' c' : ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r') :
    B (sph r a b c) (sph (-r') a' b' c') = 0 ↔
      (⟨!₂[a, b, c], r⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).IsExtTangent
        ⟨!₂[a', b', c'], r'⟩ := by
  rw [Sphere.isExtTangent_iff_dist_center]
  simp only
  have e := bridge_B_sph_dist r a b c (-r') a' b' c'
  constructor
  · intro h
    refine ⟨?_, hr, hr'⟩
    rw [PaperK.eq_iff_sq_eq dist_nonneg (by linarith)]
    rw [h] at e; linear_combination -e
  · rintro ⟨h, -, -⟩
    rw [h] at e
    linarith

/-- Equally oriented spheres with `0 ≤ r ≤ r'`: `B`-orthogonality ⇔ Mathlib internal tangency.
(This is the bridge for `tetra_tangent_B`'s enclosing sphere.) -/
theorem bridge_sph_isIntTangent (r a b c r' a' b' c' : ℝ) (hr : 0 ≤ r) (hrr : r ≤ r') :
    B (sph r a b c) (sph r' a' b' c') = 0 ↔
      (⟨!₂[a, b, c], r⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).IsIntTangent
        ⟨!₂[a', b', c'], r'⟩ := by
  rw [Sphere.isIntTangent_iff_dist_center]
  simp only
  have e := bridge_B_sph_dist r a b c r' a' b' c'
  constructor
  · intro h
    refine ⟨?_, hr, by linarith⟩
    rw [PaperK.eq_iff_sq_eq dist_nonneg (by linarith)]
    rw [h] at e; linear_combination -e
  · rintro ⟨h, -, -⟩
    rw [h] at e
    linarith

/-- **Sign stated.** The ℝ³ `equal_power` constant in Mathlib terms: for each affine sphere
`X i ⊥_B P`, `Sphere.power ⟨c_i, ρ − r_i⟩ P_X = −B(P,P)/P₄²` with `ρ = P 0 / P 4`. -/
theorem bridge_equal_power_sphere {ι : Type*} (X : ι → Fin 6 → ℝ)
    (hX4 : ∀ i, X i 4 = 1)
    (hX5 : ∀ i, X i 5 = ((X i 0)^2 - ((X i 1)^2 + (X i 2)^2 + (X i 3)^2)) / 2)
    (P : Fin 6 → ℝ) (hP : ∀ i, B P (X i) = 0) (hP4 : P 4 ≠ 0) (i : ι) :
    (⟨!₂[X i 1, X i 2, X i 3], P 0 / P 4 - X i 0⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).power
      (!₂[P 1 / P 4, P 2 / P 4, P 3 / P 4]) = -B P P / (P 4) ^ 2 := by
  have e := equal_power X hX4 hX5 P hP hP4 i
  unfold Sphere.power
  simp only
  rw [bridge_dist_sq3, e]
  unfold B
  field_simp
  ring

end PaperK3
