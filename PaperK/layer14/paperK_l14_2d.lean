import Mathlib

/-!
# Paper K, L14a: Mathlib-vocabulary restatements of eight planar/3D claims + the sign audit

No import of the Paper K library. The only local definitions are thin abbreviations built
from Mathlib primitives:
* `G`, `lieB` : the Gram matrix (a `Matrix` literal) and `lieB = Matrix.toLinearMap₂' ℝ G`;
  `lieB_apply` shows its value is `r r' − c·c' − v w' − w v'`, the body of `PaperK.B`.
* `G3`, `lieB3` : the same on `Fin 6 → ℝ` (the body of `PaperK3.B`).
* `circ r c` / `sph r c` : the null vector `(r, c, 1, (r² − ‖c‖²)/2)` of an oriented circle
  (sphere) with centre `c : EuclideanSpace ℝ (Fin 2)` (`Fin 3`) and signed radius `r`.
-/

open EuclideanGeometry Matrix

namespace PaperKL14

noncomputable section

/-! ## Local Mathlib-built vocabulary -/

def G : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
     0, -1, 0, 0, 0;
     0, 0, -1, 0, 0;
     0, 0, 0, 0, -1;
     0, 0, 0, -1, 0]

/-- The Lie form as the Mathlib bilinear map of the Gram matrix `G`. -/
def lieB (X Y : Fin 5 → ℝ) : ℝ := Matrix.toLinearMap₂' ℝ G X Y

theorem lieB_apply (X Y : Fin 5 → ℝ) :
    lieB X Y = X 0 * Y 0 - X 1 * Y 1 - X 2 * Y 2 - X 3 * Y 4 - X 4 * Y 3 := by
  simp [lieB, Matrix.toLinearMap₂'_apply', G, mulVec, dotProduct, Fin.sum_univ_five]; ring

def G3 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, -1, 0]

def lieB3 (X Y : Fin 6 → ℝ) : ℝ := Matrix.toLinearMap₂' ℝ G3 X Y

theorem lieB3_apply (X Y : Fin 6 → ℝ) :
    lieB3 X Y = X 0 * Y 0 - X 1 * Y 1 - X 2 * Y 2 - X 3 * Y 3 - X 4 * Y 5 - X 5 * Y 4 := by
  simp [lieB3, Matrix.toLinearMap₂'_apply', G3, mulVec, dotProduct, Fin.sum_univ_six]; ring

/-- Oriented circle with centre `c` and signed radius `r`, as a null vector. -/
def circ (r : ℝ) (c : EuclideanSpace ℝ (Fin 2)) : Fin 5 → ℝ :=
  ![r, c 0, c 1, 1, (r ^ 2 - c 0 ^ 2 - c 1 ^ 2) / 2]

/-- Oriented sphere with centre `c` and signed radius `r`, as a null vector. -/
def sph (r : ℝ) (c : EuclideanSpace ℝ (Fin 3)) : Fin 6 → ℝ :=
  ![r, c 0, c 1, c 2, 1, (r ^ 2 - (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2)) / 2]

theorem dist_sq2 (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-! ## 1. Null cone (`PaperK.B_self_eq_zero_iff`) -/

theorem B_self_eq_zero_iff (X : EuclideanSpace ℝ (Fin 5)) :
    lieB X X = 0 ↔ X 0 ^ 2 - X 1 ^ 2 - X 2 ^ 2 = 2 * X 3 * X 4 := by
  rw [lieB_apply]
  constructor <;> intro h <;> linear_combination h

/-- The affine chart `P ↦ (P 1, P 2)/P 3`, landing in Euclidean 2-space. -/
def pX (P : Fin 5 → ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[P 1 / P 3, P 2 / P 3]

/-! ## 2. Collinearity (`PaperK.prop31`) -/

theorem prop31 (X : Fin 4 → Fin 5 → ℝ) (i : Fin 4) (A A' P : Fin 5 → ℝ)
    (hspan : ∀ Y, (∀ j, j ≠ i → lieB Y (X j) = 0) → Y ∈ Submodule.span ℝ {A, A'})
    (hP : ∀ j, lieB P (X j) = 0)
    (hA : A 3 ≠ 0) (hA' : A' 3 ≠ 0) (hP3 : P 3 ≠ 0) :
    P ∈ Submodule.span ℝ {A, A'} ∧
      Collinear ℝ ({pX P, pX A, pX A'} : Set (EuclideanSpace ℝ (Fin 2))) := by
  have hmem : P ∈ Submodule.span ℝ {A, A'} := hspan P (fun j _ => hP j)
  refine ⟨hmem, ?_⟩
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
  subst hαβ
  have hP3' : α * A 3 + β * A' 3 ≠ 0 := by simpa using hP3
  apply collinear_insert_of_mem_affineSpan_pair
  have : pX (α • A + β • A') =
      AffineMap.lineMap (pX A) (pX A') (β * A' 3 / (α * A 3 + β * A' 3)) := by
    rw [AffineMap.lineMap_apply_module]
    ext k; fin_cases k <;> simp [pX] <;> field_simp <;> ring
  rw [this]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-! ## 3. Explicit power (`PaperK.explicit_power`), `ℝ × ℝ` coordinates -/

/-- `det [u₁ u₂ u₃ u₄]` of four column vectors, via `Matrix.det`. -/
def det4 (u₁ u₂ u₃ u₄ : Fin 4 → ℝ) : ℝ :=
  (Matrix.of fun i => ![u₁ i, u₂ i, u₃ i, u₄ i]).det

/-- Leibniz expansion of `det4` (used only to verify the row relation by `ring`). -/
theorem det4_eq (u1 u2 u3 u4 : Fin 4 → ℝ) :
    det4 u1 u2 u3 u4 = 0 + u1 0*u2 1*u3 2*u4 3 - u1 0*u2 1*u4 2*u3 3 - u1 0*u3 1*u2 2*u4 3 + u1 0*u3 1*u4 2*u2 3 + u1 0*u4 1*u2 2*u3 3 - u1 0*u4 1*u3 2*u2 3 - u2 0*u1 1*u3 2*u4 3 + u2 0*u1 1*u4 2*u3 3 + u2 0*u3 1*u1 2*u4 3 - u2 0*u3 1*u4 2*u1 3 - u2 0*u4 1*u1 2*u3 3 + u2 0*u4 1*u3 2*u1 3 + u3 0*u1 1*u2 2*u4 3 - u3 0*u1 1*u4 2*u2 3 - u3 0*u2 1*u1 2*u4 3 + u3 0*u2 1*u4 2*u1 3 + u3 0*u4 1*u1 2*u2 3 - u3 0*u4 1*u2 2*u1 3 - u4 0*u1 1*u2 2*u3 3 + u4 0*u1 1*u3 2*u2 3 + u4 0*u2 1*u1 2*u3 3 - u4 0*u2 1*u3 2*u1 3 - u4 0*u3 1*u1 2*u2 3 + u4 0*u3 1*u2 2*u1 3 := by
  rw [det4, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Laplace expansion of the `5 × 5` determinant with a repeated row, as a polynomial identity. -/
theorem row_relation (u1 u2 u3 u4 : Fin 4 → ℝ) (i : Fin 4) :
    u1 i * det4 u2 u3 u4 1 - u2 i * det4 u1 u3 u4 1 + u3 i * det4 u1 u2 u4 1
      - u4 i * det4 u1 u2 u3 1 + det4 u1 u2 u3 u4 = 0 := by
  simp only [det4_eq, Pi.one_apply]
  fin_cases i <;> simp <;> ring

/-- Circles `i` have centre `c i : ℝ × ℝ` and signed radius `r i`; `s i = ‖c i‖² − r i²`.
With `D = det[r a b 1] ≠ 0`, the point `p = (−det[r b s 1], det[r a s 1])/(2D)` and the radius
`ρ = −det[a b s 1]/(2D)` give every circle the same Laguerre power
`(p₁ − c₁)² + (p₂ − c₂)² − (ρ − r)²`, namely `‖p‖² − ρ² + det[r a b s]/D`. -/
theorem explicit_power (r : Fin 4 → ℝ) (c : Fin 4 → ℝ × ℝ)
    (hD : det4 r (fun i => (c i).1) (fun i => (c i).2) 1 ≠ 0) (i : Fin 4) :
    let a := fun i => (c i).1
    let b := fun i => (c i).2
    let s := fun i => a i ^ 2 + b i ^ 2 - r i ^ 2
    let D := det4 r a b 1
    let p : ℝ × ℝ := (-det4 r b s 1 / (2 * D), det4 r a s 1 / (2 * D))
    let ρ := -det4 a b s 1 / (2 * D)
    (p.1 - (c i).1) ^ 2 + (p.2 - (c i).2) ^ 2 - (ρ - r i) ^ 2
      = p.1 ^ 2 + p.2 ^ 2 - ρ ^ 2 + det4 r a b s / D := by
  intro a b s D p ρ
  have hrow : r i * det4 a b s 1 - a i * det4 r b s 1 + b i * det4 r a s 1
      - s i * det4 r a b 1 + det4 r a b s = 0 := by
    exact row_relation r a b s i
  have key : (p.1 - (c i).1) ^ 2 + (p.2 - (c i).2) ^ 2 - (ρ - r i) ^ 2 - (p.1 ^ 2 + p.2 ^ 2 - ρ ^ 2)
      = s i - (2 * p.1 * a i + 2 * p.2 * b i - 2 * ρ * r i) := by
    simp only [s, a, b]; ring
  have hlin : s i - (2 * p.1 * a i + 2 * p.2 * b i - 2 * ρ * r i) = det4 r a b s / D := by
    simp only [p, ρ]
    have hD' : D ≠ 0 := hD
    field_simp
    linear_combination (-1 : ℝ) * hrow
  linarith

/-! ## 4. Equal Laguerre power (`PaperK.equal_power`), via `Sphere.power` -/

/-- One cycle: the Laguerre power is `Sphere.power` of `P_X` w.r.t. the sphere of centre `c_Y`
and radius `ρ − r_Y` (`ρ = P 0/P 3`), and it equals the constant `−B(P,P)/P₃²`. -/
theorem power_eq_const (P Y : Fin 5 → ℝ) (hP3 : P 3 ≠ 0) (hv : Y 3 = 1)
    (hnull : lieB Y Y = 0) (h : lieB P Y = 0) :
    (⟨!₂[Y 1, Y 2], P 0 / P 3 - Y 0⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power (pX P)
      = -lieB P P / P 3 ^ 2 := by
  unfold Sphere.power
  simp only
  rw [dist_sq2]
  simp only [pX, PiLp.toLp_apply]
  simp
  rw [lieB_apply] at *
  rw [hv] at hnull h
  field_simp
  linear_combination (-(P 3) ^ 2) * hnull + (2 * P 3) * h

theorem equal_power {ι : Type*} (X : ι → Fin 5 → ℝ) (P : Fin 5 → ℝ) (hP3 : P 3 ≠ 0)
    (hv : ∀ i, X i 3 = 1) (hnull : ∀ i, lieB (X i) (X i) = 0) (h : ∀ i, lieB P (X i) = 0)
    (i j : ι) :
    (⟨!₂[X i 1, X i 2], P 0 / P 3 - X i 0⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power (pX P)
      = (⟨!₂[X j 1, X j 2], P 0 / P 3 - X j 0⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power
          (pX P) := by
  rw [power_eq_const P _ hP3 (hv i) (hnull i) (h i),
    power_eq_const P _ hP3 (hv j) (hnull j) (h j)]

/-! ## Helper: orthogonality to `circ r c` in coordinates -/

theorem circ_pw (P : Fin 5 → ℝ) (hP3 : P 3 ≠ 0) (r : ℝ) (c : EuclideanSpace ℝ (Fin 2))
    (h : lieB P (circ r c) = 0) :
    dist (pX P) c ^ 2 - (P 0 / P 3 - r) ^ 2
      = (P 1 / P 3) ^ 2 + (P 2 / P 3) ^ 2 - (P 0 / P 3) ^ 2 + 2 * (P 4 / P 3) := by
  rw [lieB_apply] at h
  simp [circ] at h
  rw [dist_sq2]
  simp [pX]
  field_simp
  linear_combination (2 * P 3) * h

/-! ## 5. Equal radii: `P_X` is the circumcentre (`PaperK2.PX_circumcentre`) -/

theorem PX_circumcentre (P : Fin 5 → ℝ) (hP3 : P 3 ≠ 0)
    (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) (r₀ : ℝ)
    (h : ∀ i, lieB P (circ r₀ (s.points i)) = 0) :
    pX P = s.circumcenter := by
  have hspan : affineSpan ℝ (Set.range s.points) = ⊤ :=
    (s.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by simp)
  refine s.eq_circumcenter_of_dist_eq (r := dist (s.points 0) (pX P)) (by rw [hspan]; trivial) ?_
  intro i
  have e := circ_pw P hP3 r₀ _ (h i)
  have e0 := circ_pw P hP3 r₀ _ (h 0)
  rw [dist_comm, dist_comm (s.points 0)]
  have hsq : dist (pX P) (s.points i) ^ 2 = dist (pX P) (s.points 0) ^ 2 := by linarith
  exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 hsq

/-! ## 6. Equilateral triple (`PaperK2.equilateral_PX`) -/

theorem equilateral_PX (P : Fin 5 → ℝ) (hP3 : P 3 ≠ 0) (r : ℝ) (c : EuclideanSpace ℝ (Fin 2))
    (h1 : lieB P (circ 1 !₂[0, 0]) = 0) (h2 : lieB P (circ 1 !₂[2, 0]) = 0)
    (h3 : lieB P (circ 1 !₂[1, Real.sqrt 3]) = 0) (_h4 : lieB P (circ r c) = 0) :
    pX P = !₂[1, Real.sqrt 3 / 3] := by
  have e1 := circ_pw P hP3 _ _ h1
  have e2 := circ_pw P hP3 _ _ h2
  have e3 := circ_pw P hP3 _ _ h3
  rw [dist_sq2] at e1 e2 e3
  simp [pX] at e1 e2 e3
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  set x := P 1 / P 3
  set y := P 2 / P 3
  have hx : x = 1 := by nlinarith
  have hy : y = Real.sqrt 3 / 3 := by
    clear_value x y
    subst hx
    have : 2 * Real.sqrt 3 * y = 2 := by nlinarith
    field_simp
    nlinarith
  ext k; fin_cases k <;> simp [pX] <;> [exact hx; exact hy]

/-! ## 7. Square of four unit circles (`PaperK2.square_PX` + `square_apollonius`) -/

/-- Centres `(1,1), (−1,1), (−1,−1), (1,−1)`. -/
def sqc : Fin 4 → EuclideanSpace ℝ (Fin 2) := ![!₂[1, 1], !₂[-1, 1], !₂[-1, -1], !₂[1, -1]]

theorem square_PX (P : Fin 5 → ℝ) (_hP3 : P 3 ≠ 0)
    (h : ∀ i, lieB P (circ 1 (sqc i)) = 0) : pX P = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [lieB_apply, circ, sqc] at h0 h1 h2 h3
  have a1 : P 1 = 0 := by linarith
  have a2 : P 2 = 0 := by linarith
  ext k; fin_cases k <;> simp [pX, a1, a2]

/-- For every 3-subset (omit `k`), an oriented circle `(x; ρ)` is tangent (`dist² = (ρ − 1)²`)
to the three remaining unit circles iff `x = 0` and `ρ = 1 ± √2`. -/
theorem square_apollonius (k : Fin 4) (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    (∀ i, i ≠ k → dist x (sqc i) ^ 2 = (ρ - 1) ^ 2) ↔
      (x = 0 ∧ (ρ = 1 + Real.sqrt 2 ∨ ρ = 1 - Real.sqrt 2)) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have rho_iff : (ρ - 1) ^ 2 = 2 ↔ (ρ = 1 + Real.sqrt 2 ∨ ρ = 1 - Real.sqrt 2) := by
    constructor
    · intro h
      have : (ρ - 1 - Real.sqrt 2) * (ρ - 1 + Real.sqrt 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> subst h <;> nlinarith
  have hx0 : x = 0 ↔ x 0 = 0 ∧ x 1 = 0 :=
    ⟨fun h => by simp [h], fun ⟨h0, h1⟩ => by ext i; fin_cases i <;> simp [h0, h1]⟩
  rw [← rho_iff, hx0]
  simp only [dist_sq2]
  fin_cases k <;> simp [sqc, Fin.forall_fin_succ] <;>
  · constructor
    · intro h
      obtain ⟨h1, h2, h3⟩ := h
      have hx : x 0 = 0 := by nlinarith
      have hy : x 1 = 0 := by nlinarith
      rw [hx, hy] at h1 h2 h3
      exact ⟨⟨hx, hy⟩, by nlinarith⟩
    · rintro ⟨⟨hx, hy⟩, h⟩
      rw [hx, hy]
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-! ## 8. Regular tetrahedron in `EuclideanSpace ℝ (Fin 3)` (`PaperK3.tetra_PX_origin`) -/

def tv : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[1, 1, 1], !₂[1, -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

theorem tetra_PX_origin (r : ℝ) (c : EuclideanSpace ℝ (Fin 3)) (P : Fin 6 → ℝ)
    (h : ∀ i, lieB3 P (sph 1 (tv i)) = 0) (_h5 : lieB3 P (sph r c) = 0) (_hP4 : P 4 ≠ 0) :
    (!₂[P 1 / P 4, P 2 / P 4, P 3 / P 4] : EuclideanSpace ℝ (Fin 3)) = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [lieB3_apply, sph, tv] at h0 h1 h2 h3
  have a1 : P 1 = 0 := by linarith
  have a2 : P 2 = 0 := by linarith
  have a3 : P 3 = 0 := by linarith
  ext k; fin_cases k <;> simp [a1, a2, a3]

/-! ## Sign audit -/

/-- **Audit (a), general.** For normalised null vectors (`v = 1`), the bilinear form satisfies
`2·B X Y = dist(c_X, c_Y)² − (r_X − r_Y)²`. -/
theorem audit_two_B_dist (X Y : Fin 5 → ℝ) (hX : lieB X X = 0) (hY : lieB Y Y = 0)
    (hX3 : X 3 = 1) (hY3 : Y 3 = 1) :
    2 * lieB X Y = dist (!₂[X 1, X 2] : EuclideanSpace ℝ (Fin 2)) !₂[Y 1, Y 2] ^ 2
      - (X 0 - Y 0) ^ 2 := by
  rw [dist_sq2]
  simp
  rw [lieB_apply] at hX hY ⊢
  rw [hX3, hY3]
  rw [hX3] at hX
  rw [hY3] at hY
  linear_combination hX + hY

/-- **Audit (a), `circ` form.** -/
theorem audit_two_B_dist_circ (r r' : ℝ) (c c' : EuclideanSpace ℝ (Fin 2)) :
    2 * lieB (circ r c) (circ r' c') = dist c c' ^ 2 - (r - r') ^ 2 := by
  rw [dist_sq2, lieB_apply]; simp [circ]; ring

/-- **Audit (b).** Radius-0 cycle: `B X Y = ½ · Sphere.power ⟨c_Y, r_Y⟩ c_X`. -/
theorem audit_B_half_power (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (c : EuclideanSpace ℝ (Fin 2)) :
    lieB (circ 0 x) (circ r c) = (1 / 2) * (⟨c, r⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power x := by
  have e := audit_two_B_dist_circ 0 r x c
  unfold Sphere.power
  simp only
  linear_combination (1 / 2 : ℝ) * e

/-- **Audit (c).** The equal-power constant: radius-0 `P` (`P 0 = 0`) orthogonal to `circ r c`
gives `Sphere.power ⟨c, r⟩ P_X = −B(P,P)/P₃²`. -/
theorem audit_power_const_rho0 (P : Fin 5 → ℝ) (hP3 : P 3 ≠ 0) (hP0 : P 0 = 0) (r : ℝ)
    (c : EuclideanSpace ℝ (Fin 2)) (h : lieB P (circ r c) = 0) :
    (⟨c, r⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).power (pX P) = -lieB P P / P 3 ^ 2 := by
  have e := circ_pw P hP3 r c h
  unfold Sphere.power
  simp only
  rw [hP0] at e
  rw [lieB_apply, hP0]
  field_simp at e ⊢
  linear_combination e

/-- The "source form" of reading (ii), transcribed literally. -/
def sourceForm (X Y : Fin 5 → ℝ) : ℝ :=
  X 0 * Y 0 - (X 1 * Y 1 + X 2 * Y 2) - X 3 * Y 4 - X 4 * Y 3

/-- **Audit (d).** The bilinear form IS the literal source form (factor `+1`). -/
theorem audit_B_eq_source (X Y : Fin 5 → ℝ) : lieB X Y = sourceForm X Y := by
  rw [lieB_apply, sourceForm]; ring

/-- **Audit (e).** Reading (ii) `B = −(source form)` is refuted: at `X = Y = (1,1,1,1,1)`, `B = −3` but `−(source) = 3`. -/
theorem audit_reading_ii_false : ¬ ∀ X Y : Fin 5 → ℝ, lieB X Y = -sourceForm X Y := by
  intro H
  have := H (fun _ => 1) (fun _ => 1)
  rw [lieB_apply, sourceForm] at this
  norm_num at this

/-- **Audit (f), numeric witness of (a).** Unit circle at `0`, radius-2 circle at `(3,4)`:
`2·B = 25 − 1 = 24`. -/
theorem audit_witness :
    2 * lieB (circ 1 !₂[0, 0]) (circ 2 !₂[3, 4]) = 24 ∧
    dist (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) !₂[3, 4] ^ 2 - (1 - 2) ^ 2 = 24 := by
  constructor
  · rw [lieB_apply]; simp [circ]; norm_num
  · rw [dist_sq2]; simp; norm_num

end

end PaperKL14
