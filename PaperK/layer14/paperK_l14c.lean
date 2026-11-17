import Mathlib

/-!
# Paper K, L14c: Mathlib-vocabulary restatements of the five ℝ³ claims of `PaperK3`

No import of the Paper K library. Local definitions are thin abbreviations over Mathlib:
* `G3`, `lieB3` : the Gram matrix and `lieB3 = Matrix.toLinearMap₂' ℝ G3`; `lieB3_apply` shows
  its value is `X0Y0 − X1Y1 − X2Y2 − X3Y3 − X4Y5 − X5Y4`, the body of `PaperK3.B`.
* `η`, `minkowski`, `lorentzQ` : the Minkowski form on `Fin 4 → ℝ`, as
  `Matrix.toLinearMap₂' ℝ (diagonal η)` and as `QuadraticMap.weightedSumSquares ℝ η`.
* `sph r c` : the null vector of the oriented sphere with centre `c : EuclideanSpace ℝ (Fin 3)`
  and signed radius `r` (same coordinates as `PaperK3.sph r (c 0) (c 1) (c 2)`).
* `pX P` : the affine centre `(P1, P2, P3)/P4 ∈ EuclideanSpace ℝ (Fin 3)`;
  `cen X` : the un-normalised centre `(X1, X2, X3)`.
* `tv` : the four tetrahedron vertices `(1,1,1), (1,−1,−1), (−1,1,−1), (−1,−1,1)`.
-/

open EuclideanGeometry Matrix

namespace PaperKL14c

noncomputable section

/-! ## Vocabulary -/

def G3 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, -1, 0]

/-- The Lie form on `ℝ⁶` as the Mathlib bilinear map of the Gram matrix `G3`. -/
def lieB3 (X Y : Fin 6 → ℝ) : ℝ := Matrix.toLinearMap₂' ℝ G3 X Y

theorem lieB3_apply (X Y : Fin 6 → ℝ) :
    lieB3 X Y = X 0 * Y 0 - X 1 * Y 1 - X 2 * Y 2 - X 3 * Y 3 - X 4 * Y 5 - X 5 * Y 4 := by
  simp [lieB3, Matrix.toLinearMap₂'_apply', G3, mulVec, dotProduct, Fin.sum_univ_six]; ring

/-- Minkowski signature `(+,−,−,−)`. -/
def η : Fin 4 → ℝ := ![1, -1, -1, -1]

/-- Minkowski bilinear form on `ℝ⁴`, via `Matrix.toLinearMap₂'`. -/
def minkowski : LinearMap.BilinForm ℝ (Fin 4 → ℝ) := Matrix.toLinearMap₂' ℝ (diagonal η)

/-- Lorentz quadratic form on `ℝ⁴`, via `QuadraticMap.weightedSumSquares`. -/
def lorentzQ : QuadraticForm ℝ (Fin 4 → ℝ) := QuadraticMap.weightedSumSquares ℝ η

theorem lorentzQ_apply (v : Fin 4 → ℝ) :
    lorentzQ v = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by
  simp [lorentzQ, QuadraticMap.weightedSumSquares_apply, η, Fin.sum_univ_four]; ring

theorem lorentzQ_eq_minkowski (v : Fin 4 → ℝ) : lorentzQ v = minkowski v v := by
  rw [lorentzQ_apply]
  simp [minkowski, Matrix.toLinearMap₂'_apply', mulVec_diagonal, dotProduct, Fin.sum_univ_four, η]
  ring

/-- The first four coordinates `(r, c)` of a vector of `ℝ⁶`. -/
def lor (X : Fin 6 → ℝ) : Fin 4 → ℝ := ![X 0, X 1, X 2, X 3]

/-- Oriented sphere with centre `c` and signed radius `r`, as a null vector. -/
def sph (r : ℝ) (c : EuclideanSpace ℝ (Fin 3)) : Fin 6 → ℝ :=
  ![r, c 0, c 1, c 2, 1, (r ^ 2 - (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2)) / 2]

/-- Affine centre `P_X` of a vector with `P 4 ≠ 0`. -/
def pX (P : Fin 6 → ℝ) : EuclideanSpace ℝ (Fin 3) := !₂[P 1 / P 4, P 2 / P 4, P 3 / P 4]

/-- Un-normalised centre part `(X1, X2, X3)`. -/
def cen (X : Fin 6 → ℝ) : EuclideanSpace ℝ (Fin 3) := !₂[X 1, X 2, X 3]

theorem dist_sq3 (p q : EuclideanSpace ℝ (Fin 3)) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three, Real.dist_eq, sq_abs]

/-- Sign bridge: `2·B(sph r c, sph r' c') = dist(c,c')² − (r − r')²`. -/
theorem two_lieB3_sph (r r' : ℝ) (c c' : EuclideanSpace ℝ (Fin 3)) :
    2 * lieB3 (sph r c) (sph r' c') = dist c c' ^ 2 - (r - r') ^ 2 := by
  rw [dist_sq3, lieB3_apply]; simp [sph]; ring

/-- `B`-orthogonality of equally oriented spheres (`0 ≤ r' ≤ r`) is Mathlib internal tangency. -/
theorem isIntTangent_of_lieB3 {r r' : ℝ} {c c' : EuclideanSpace ℝ (Fin 3)}
    (h : lieB3 (sph r c) (sph r' c') = 0) (h0 : 0 ≤ r') (hle : r' ≤ r) :
    (⟨c', r'⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).IsIntTangent ⟨c, r⟩ := by
  rw [Sphere.isIntTangent_iff_dist_center]
  refine ⟨?_, h0, by linarith⟩
  have e := two_lieB3_sph r r' c c'
  rw [h] at e
  have hsq : dist c' c ^ 2 = (r - r') ^ 2 := by rw [dist_comm]; linarith
  exact (pow_left_inj₀ dist_nonneg (by linarith) two_ne_zero).1 hsq

/-- `B`-orthogonality of oppositely oriented spheres (`r ≤ 0 ≤ r'`) is Mathlib external tangency
of the sphere of (unsigned) radius `−r` with the sphere of radius `r'`. -/
theorem isExtTangent_of_lieB3 {r r' : ℝ} {c c' : EuclideanSpace ℝ (Fin 3)}
    (h : lieB3 (sph r c) (sph r' c') = 0) (hr : r ≤ 0) (hr' : 0 ≤ r') :
    (⟨c, -r⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).IsExtTangent ⟨c', r'⟩ := by
  rw [Sphere.isExtTangent_iff_dist_center]
  refine ⟨?_, by linarith, hr'⟩
  have e := two_lieB3_sph r r' c c'
  rw [h] at e
  have hsq : dist c c' ^ 2 = (-r + r') ^ 2 := by linarith
  exact (pow_left_inj₀ dist_nonneg (by linarith) two_ne_zero).1 hsq

/-! ## 1. Null cone (`PaperK3.B_self_zero_iff`) -/

theorem B_self_zero_iff (X : Fin 6 → ℝ) :
    lieB3 X X = 0 ↔ lorentzQ (lor X) = 2 * X 4 * X 5 := by
  rw [lieB3_apply, lorentzQ_apply]
  simp [lor]
  constructor <;> intro h <;> linear_combination h

/-! ## 2. Tangency identity (`PaperK3.tangency_identity`) -/

theorem tangency_identity (X Y : Fin 6 → ℝ) (hX : lieB3 X X = 0) (hY : lieB3 Y Y = 0) :
    -2 * X 4 * Y 4 * lieB3 X Y
      = (X 0 * Y 4 - Y 0 * X 4) ^ 2 - dist (Y 4 • cen X) (X 4 • cen Y) ^ 2 := by
  rw [dist_sq3]
  simp [cen]
  rw [lieB3_apply] at *
  linear_combination (-(Y 4) ^ 2) * hX - (X 4) ^ 2 * hY

/-- Normalised form (`X4 = Y4 = 1`): `−2·B X Y = (r_X − r_Y)² − dist(c_X, c_Y)²`. -/
theorem tangency_identity_normalised (X Y : Fin 6 → ℝ) (hX : lieB3 X X = 0)
    (hY : lieB3 Y Y = 0) (hX4 : X 4 = 1) (hY4 : Y 4 = 1) :
    -2 * lieB3 X Y = (X 0 - Y 0) ^ 2 - dist (cen X) (cen Y) ^ 2 := by
  have e := tangency_identity X Y hX hY
  rw [hX4, hY4] at e
  simpa using e

/-! ## 3. Equal power (`PaperK3.equal_power`), via `Sphere.power` -/

/-- One normalised sphere `Y`: the Laguerre power of `P_X` equals `Sphere.power` of `P_X` w.r.t.
the sphere of centre `c_Y` and radius `ρ − r_Y` (`ρ = P0/P4`), and equals `−B(P,P)/P4²`. -/
theorem power_eq_const (P Y : Fin 6 → ℝ) (hP4 : P 4 ≠ 0) (hY4 : Y 4 = 1)
    (hY5 : Y 5 = (Y 0 ^ 2 - (Y 1 ^ 2 + Y 2 ^ 2 + Y 3 ^ 2)) / 2) (h : lieB3 P Y = 0) :
    (⟨cen Y, P 0 / P 4 - Y 0⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).power (pX P)
      = -lieB3 P P / P 4 ^ 2 := by
  unfold Sphere.power
  simp only
  rw [dist_sq3]
  simp [pX, cen]
  rw [lieB3_apply] at *
  rw [hY4, hY5] at h
  field_simp
  linear_combination (2 * P 4) * h

theorem equal_power {ι : Type*} (X : ι → Fin 6 → ℝ)
    (hX4 : ∀ i, X i 4 = 1)
    (hX5 : ∀ i, X i 5 = ((X i 0) ^ 2 - ((X i 1) ^ 2 + (X i 2) ^ 2 + (X i 3) ^ 2)) / 2)
    (P : Fin 6 → ℝ) (hP : ∀ i, lieB3 P (X i) = 0) (hP4 : P 4 ≠ 0) (i j : ι) :
    (⟨cen (X i), P 0 / P 4 - X i 0⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).power (pX P)
      = (⟨cen (X j), P 0 / P 4 - X j 0⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).power (pX P) := by
  rw [power_eq_const P _ hP4 (hX4 i) (hX5 i) (hP i), power_eq_const P _ hP4 (hX4 j) (hX5 j) (hP j)]

/-- The common value `−B(P,P)/P4²` is the source's `‖P_X‖² − ρ² + 2·P5/P4`. -/
theorem power_const_eq_source (P : Fin 6 → ℝ) (hP4 : P 4 ≠ 0) :
    -lieB3 P P / P 4 ^ 2
      = (P 1 / P 4) ^ 2 + (P 2 / P 4) ^ 2 + (P 3 / P 4) ^ 2 - (P 0 / P 4) ^ 2 + 2 * (P 5 / P 4) := by
  rw [lieB3_apply]
  field_simp
  ring

/-! ## 4. Tetrahedron: `B`-orthogonality as Mathlib tangency (`PaperK3.tetra_tangent_B`) -/

def tv : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[1, 1, 1], !₂[1, -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

theorem one_lt_sqrt3 : 1 < Real.sqrt 3 := by
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem tetra_lieB3 (i : Fin 4) :
    lieB3 (sph (Real.sqrt 3 + 1) 0) (sph 1 (tv i)) = 0 ∧
    lieB3 (sph (1 - Real.sqrt 3) 0) (sph 1 (tv i)) = 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [lieB3_apply, lieB3_apply]
  fin_cases i <;> simp [sph, tv] <;> constructor <;> linear_combination (-1/2) * h3

/-- The enclosing sphere `⟨0, √3+1⟩` is internally tangent to (contains) each unit sphere, and the
inscribed sphere `⟨0, √3−1⟩` (the signed radius `1−√3`, negated) is externally tangent to each. -/
theorem tetra_tangent_B (i : Fin 4) :
    lieB3 (sph (Real.sqrt 3 + 1) 0) (sph 1 (tv i)) = 0 ∧
    lieB3 (sph (1 - Real.sqrt 3) 0) (sph 1 (tv i)) = 0 ∧
    (⟨tv i, 1⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).IsIntTangent ⟨0, Real.sqrt 3 + 1⟩ ∧
    (⟨0, -(1 - Real.sqrt 3)⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).IsExtTangent ⟨tv i, 1⟩ := by
  obtain ⟨h1, h2⟩ := tetra_lieB3 i
  have hs := one_lt_sqrt3
  exact ⟨h1, h2, isIntTangent_of_lieB3 h1 zero_le_one (by linarith),
    isExtTangent_of_lieB3 h2 (by linarith) zero_le_one⟩

/-! ## 5. `PaperK3.tetra_thm36` (an E1 fact, not Theorem 3.6) -/

theorem tetra_PX_origin (P : Fin 6 → ℝ) (h : ∀ i, lieB3 P (sph 1 (tv i)) = 0) : pX P = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [lieB3_apply, sph, tv] at h0 h1 h2 h3
  have a1 : P 1 = 0 := by linarith
  have a2 : P 2 = 0 := by linarith
  have a3 : P 3 = 0 := by linarith
  ext k; fin_cases k <;> simp [pX, a1, a2, a3]

/-- The Apollonius pair of the four tetrahedron spheres: an oriented sphere `(x; ρ)` is
`B`-orthogonal (`dist² = (ρ − 1)²`) to all four unit spheres iff `x = 0` and `ρ = 1 ± √3`. -/
theorem tetra_apollonius (x : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) :
    (∀ i, lieB3 (sph ρ x) (sph 1 (tv i)) = 0) ↔
      (x = 0 ∧ (ρ = 1 + Real.sqrt 3 ∨ ρ = 1 - Real.sqrt 3)) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hB : ∀ i, lieB3 (sph ρ x) (sph 1 (tv i)) = 0 ↔ dist x (tv i) ^ 2 = (ρ - 1) ^ 2 := by
    intro i
    have e := two_lieB3_sph ρ 1 x (tv i)
    constructor <;> intro h
    · rw [h] at e; linarith
    · linarith
  simp only [hB, dist_sq3, Fin.forall_fin_succ]
  simp [tv]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    have hx : x 0 = 0 := by linear_combination (-1/8) * (h0 + h1 - h2 - h3)
    have hy : x 1 = 0 := by linear_combination (-1/8) * (h0 - h1 + h2 - h3)
    have hz : x 2 = 0 := by linear_combination (-1/8) * (h0 - h1 - h2 + h3)
    rw [hx, hy, hz] at h0
    refine ⟨?_, ?_⟩
    · ext k; fin_cases k <;> simp [hx, hy, hz]
    · have : (ρ - 1 - Real.sqrt 3) * (ρ - 1 + Real.sqrt 3) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
  · rintro ⟨rfl, h⟩
    simp
    rcases h with h | h <;> subst h <;> nlinarith

/-- Restatement of `PaperK3.tetra_thm36`: for `P` `B`-orthogonal to the four unit spheres and to an
arbitrary fifth sphere, with `P4 ≠ 0`: `P_X = 0`, both Apollonius spheres of radii `√3 ± 1` centred at
`P_X` are `B`-orthogonal to (and Mathlib-tangent to) all four, and `P_X` has the same
`Sphere.power` (`= 2`) w.r.t. each unit sphere. -/
theorem tetra_thm36 (r : ℝ) (c : EuclideanSpace ℝ (Fin 3)) (P : Fin 6 → ℝ)
    (h : ∀ i, lieB3 P (sph 1 (tv i)) = 0) (_h5 : lieB3 P (sph r c) = 0) (_hP4 : P 4 ≠ 0) :
    pX P = 0 ∧
    ∀ i : Fin 4,
      lieB3 (sph (Real.sqrt 3 + 1) (pX P)) (sph 1 (tv i)) = 0 ∧
      lieB3 (sph (1 - Real.sqrt 3) (pX P)) (sph 1 (tv i)) = 0 ∧
      (⟨tv i, 1⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).IsIntTangent ⟨pX P, Real.sqrt 3 + 1⟩ ∧
      (⟨pX P, -(1 - Real.sqrt 3)⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).IsExtTangent ⟨tv i, 1⟩ ∧
      (⟨tv i, 1⟩ : Sphere (EuclideanSpace ℝ (Fin 3))).power (pX P) = 2 := by
  have hpx := tetra_PX_origin P h
  refine ⟨hpx, fun i => ?_⟩
  rw [hpx]
  refine ⟨(tetra_tangent_B i).1, (tetra_tangent_B i).2.1, (tetra_tangent_B i).2.2.1,
    (tetra_tangent_B i).2.2.2, ?_⟩
  unfold Sphere.power
  simp only
  rw [dist_sq3]
  fin_cases i <;> simp [tv] <;> norm_num

end

end PaperKL14c
