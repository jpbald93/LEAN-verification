import Mathlib

/-!
# Paper K, L14b: Mathlib-vocabulary restatements, part 2 (planar + linear-algebra rows)

No import of the Paper K library. Local definitions are thin wrappers over Mathlib primitives:
* `G`, `lieB` : the Gram matrix literal and `lieB = Matrix.toLinearMap₂' ℝ G` (`lieB_apply` gives the
  body of `PaperK.B` / `PaperK2.B`).
* `cen X = !₂[X 1, X 2]`, `pX P = !₂[P 1 / P 3, P 2 / P 3]` in `EuclideanSpace ℝ (Fin 2)`;
  `sph X = ⟨pX X, X 0 / X 3⟩ : EuclideanGeometry.Sphere _` (centre / signed radius of a cycle).
* `circ r c` : the null vector `(r, c 0, c 1, 1, (r² − ‖c‖²)/2)` of the oriented circle `(c; r)`.
* `cofactor M` : signed `4 × 4` minors via `Matrix.det` / `Matrix.submatrix`.
* `det4`, `D3`, `ccx`, `ccy` : the same polynomials as in the source files.
-/

open EuclideanGeometry Matrix Module

namespace PaperKL14b

noncomputable section

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## Vocabulary -/

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

/-- Unnormalised centre slots of a cycle. -/
def cen (X : Fin 5 → ℝ) : E2 := !₂[X 1, X 2]

/-- The affine chart `P ↦ (P 1, P 2)/P 3`. -/
def pX (P : Fin 5 → ℝ) : E2 := !₂[P 1 / P 3, P 2 / P 3]

/-- The oriented circle of a cycle: centre `pX X`, signed radius `X 0 / X 3`. -/
def sph (X : Fin 5 → ℝ) : Sphere E2 := ⟨pX X, X 0 / X 3⟩

/-- Oriented circle with centre `c` and signed radius `r`, as a null vector. -/
def circ (r : ℝ) (c : E2) : Fin 5 → ℝ :=
  ![r, c 0, c 1, 1, (r ^ 2 - c 0 ^ 2 - c 1 ^ 2) / 2]

theorem dist_sq2 (p q : E2) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-! ## Row 1. `PaperK.tangency_identity` -/

/-- **Row 1.** For null `X, Y`, `−2 X₃ Y₃ B(X,Y) = (r_X Y₃ − r_Y X₃)² − dist(Y₃ c_X, X₃ c_Y)²`.
No nonvanishing hypothesis, exactly as in the source. -/
theorem tangency_identity (X Y : Fin 5 → ℝ) (hX : lieB X X = 0) (hY : lieB Y Y = 0) :
    -2 * X 3 * Y 3 * lieB X Y
      = (X 0 * Y 3 - Y 0 * X 3) ^ 2 - dist (Y 3 • cen X) (X 3 • cen Y) ^ 2 := by
  rw [dist_sq2]
  simp [cen]
  rw [lieB_apply] at *
  linear_combination -(Y 3) ^ 2 * hX - (X 3) ^ 2 * hY

/-- **Row 1, normalised.** With `X 3, Y 3 ≠ 0`:
`−2 B(X,Y)/(X₃Y₃) = (r_X − r_Y)² − dist(c_X, c_Y)²` for the circles `sph X`, `sph Y`. -/
theorem tangency_identity_sph (X Y : Fin 5 → ℝ) (hX : lieB X X = 0) (hY : lieB Y Y = 0)
    (hX3 : X 3 ≠ 0) (hY3 : Y 3 ≠ 0) :
    -2 * lieB X Y / (X 3 * Y 3)
      = ((sph X).radius - (sph Y).radius) ^ 2 - dist (sph X).center (sph Y).center ^ 2 := by
  have h := tangency_identity X Y hX hY
  rw [dist_sq2] at h ⊢
  simp [cen] at h
  simp only [sph, pX]
  simp
  rw [div_eq_iff (mul_ne_zero hX3 hY3)]
  field_simp
  linear_combination h

/-! ## Row 2. `PaperK.B_eq_zero_iff_tangent` (+ `tangency_of_B_eq_zero`) -/

/-- **Row 2 helper.** `B = 0` on the null cone forces the scaled tangency equation. -/
theorem tangency_of_B_eq_zero (X Y : Fin 5 → ℝ) (hX : lieB X X = 0) (hY : lieB Y Y = 0)
    (h : lieB X Y = 0) :
    (X 0 * Y 3 - Y 0 * X 3) ^ 2 = dist (Y 3 • cen X) (X 3 • cen Y) ^ 2 := by
  have := tangency_identity X Y hX hY
  rw [h] at this
  linarith

/-- **Row 2.** With `X 3, Y 3 ≠ 0` on the null cone, `B X Y = 0` iff the two oriented circles have
centres at distance `|r_X − r_Y|`. -/
theorem B_eq_zero_iff_tangent (X Y : Fin 5 → ℝ) (hX : lieB X X = 0) (hY : lieB Y Y = 0)
    (hX3 : X 3 ≠ 0) (hY3 : Y 3 ≠ 0) :
    lieB X Y = 0 ↔
      dist (sph X).center (sph Y).center = |(sph X).radius - (sph Y).radius| := by
  have h := tangency_identity_sph X Y hX hY hX3 hY3
  have hne : X 3 * Y 3 ≠ 0 := mul_ne_zero hX3 hY3
  rw [← sq_eq_sq₀ dist_nonneg (abs_nonneg _), sq_abs]
  constructor
  · intro h0
    rw [h0] at h
    simp at h
    linarith
  · intro h1
    have : -2 * lieB X Y / (X 3 * Y 3) = 0 := by rw [h, h1]; ring
    rcases div_eq_zero_iff.1 this with h2 | h2
    · linarith
    · exact absurd h2 hne

/-- **Row 2, Mathlib tangency (same orientation).** For non-negative radii, `B X Y = 0` iff one
circle is internally tangent to the other (`Sphere.IsIntTangent`). -/
theorem B_eq_zero_iff_isIntTangent (X Y : Fin 5 → ℝ) (hX : lieB X X = 0) (hY : lieB Y Y = 0)
    (hX3 : X 3 ≠ 0) (hY3 : Y 3 ≠ 0) (hr : 0 ≤ (sph X).radius) (hr' : 0 ≤ (sph Y).radius) :
    lieB X Y = 0 ↔ (sph X).IsIntTangent (sph Y) ∨ (sph Y).IsIntTangent (sph X) := by
  rw [B_eq_zero_iff_tangent X Y hX hY hX3 hY3, Sphere.isIntTangent_iff_dist_center,
    Sphere.isIntTangent_iff_dist_center, dist_comm (sph Y).center, eq_comm,
    abs_eq dist_nonneg]
  constructor
  · rintro (h | h)
    · right; exact ⟨by linarith, hr', hr⟩
    · left; exact ⟨by linarith, hr, hr'⟩
  · rintro (⟨h, -, -⟩ | ⟨h, -, -⟩)
    · right; linarith
    · left; linarith

/-- **Row 2, Mathlib tangency (opposite orientation).** If `r_X ≥ 0 ≥ r_Y`, `B X Y = 0` iff
`sph X` is externally tangent (`Sphere.IsExtTangent`) to the circle of centre `c_Y`, radius `−r_Y`. -/
theorem B_eq_zero_iff_isExtTangent (X Y : Fin 5 → ℝ) (hX : lieB X X = 0) (hY : lieB Y Y = 0)
    (hX3 : X 3 ≠ 0) (hY3 : Y 3 ≠ 0) (hr : 0 ≤ (sph X).radius) (hr' : (sph Y).radius ≤ 0) :
    lieB X Y = 0 ↔
      (sph X).IsExtTangent (⟨(sph Y).center, -(sph Y).radius⟩ : Sphere E2) := by
  rw [B_eq_zero_iff_tangent X Y hX hY hX3 hY3, Sphere.isExtTangent_iff_dist_center,
    abs_of_nonneg (by linarith)]
  constructor
  · intro h; exact ⟨by rw [h]; ring, hr, by linarith⟩
  · rintro ⟨h, -, -⟩; rw [h]; ring

/-! ## Row 3. `PaperK.mulVec_cofactor` -/

/-- Signed `4 × 4` minors of a `4 × 5` matrix (generalised cross product). -/
def cofactor (M : Matrix (Fin 4) (Fin 5) ℝ) : Fin 5 → ℝ :=
  fun k => (-1 : ℝ) ^ (k : ℕ) * (M.submatrix id (Fin.succAbove k)).det

/-- **Row 3 (Laplace).** The `5 × 5` determinant of `M` with the row `y` stacked on top is
`y ⬝ᵥ cofactor M` (`Matrix.det_succ_row_zero`). -/
theorem det_cons_eq_dotProduct (M : Matrix (Fin 4) (Fin 5) ℝ) (y : Fin 5 → ℝ) :
    (Matrix.of (Fin.cons y fun j => M j) : Matrix (Fin 5) (Fin 5) ℝ).det = y ⬝ᵥ cofactor M := by
  rw [Matrix.det_succ_row_zero]
  simp only [dotProduct, cofactor]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Matrix.of (Fin.cons y fun j => M j) : Matrix (Fin 5) (Fin 5) ℝ).submatrix Fin.succ
      k.succAbove = M.submatrix id k.succAbove := by
    ext a b; simp
  rw [this]; simp; ring

/-- **Row 3.** The cofactor vector lies in `ker M` (as a Mathlib linear map). -/
theorem cofactor_mem_ker (M : Matrix (Fin 4) (Fin 5) ℝ) :
    cofactor M ∈ LinearMap.ker M.mulVecLin := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext i
  have hdet : (Matrix.of (Fin.cons (M i) fun j => M j) : Matrix (Fin 5) (Fin 5) ℝ).det = 0 := by
    refine Matrix.det_zero_of_row_eq (i := 0) (j := i.succ) (Fin.succ_ne_zero i).symm ?_
    funext k; simp
  rw [det_cons_eq_dotProduct] at hdet
  simpa [mulVec] using hdet

/-- **Row 3 (source form).** `M *ᵥ cofactor M = 0`. -/
theorem mulVec_cofactor (M : Matrix (Fin 4) (Fin 5) ℝ) : M *ᵥ cofactor M = 0 :=
  cofactor_mem_ker M

/-- **Row 3 (strengthening).** If the rows of `M` are linearly independent, the cofactor vector is a
*nonzero* kernel vector. -/
theorem cofactor_ne_zero (M : Matrix (Fin 4) (Fin 5) ℝ) (hM : LinearIndependent ℝ M.row) :
    cofactor M ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_linearIndependent_cons_of_lt_finrank hM
    (by simp : 4 < finrank ℝ (Fin 5 → ℝ))
  have hU : IsUnit (Matrix.of (Fin.cons y fun j => M j) : Matrix (Fin 5) (Fin 5) ℝ) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 hy
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  rw [det_cons_eq_dotProduct] at hdet
  intro h0
  rw [h0, dotProduct_zero] at hdet
  exact not_isUnit_zero hdet

/-! ## Row 4. `PaperK.B_G_cofactor_row` -/

theorem lieB_G_mulVec (P Y : Fin 5 → ℝ) : lieB (G *ᵥ P) Y = Y ⬝ᵥ P := by
  rw [lieB_apply]
  simp [G, mulVec, dotProduct, Fin.sum_univ_five]; ring

/-- **Row 4 (scaled kernel).** For every `P ∈ ker M`, `G P` is `B`-orthogonal
(`LinearMap.IsOrtho (toLinearMap₂' ℝ G)`) to every row of `M`. -/
theorem B_G_ker_row (M : Matrix (Fin 4) (Fin 5) ℝ) (P : Fin 5 → ℝ)
    (hP : P ∈ LinearMap.ker M.mulVecLin) (i : Fin 4) :
    (Matrix.toLinearMap₂' ℝ G).IsOrtho (G *ᵥ P) (M i) := by
  rw [LinearMap.isOrtho_def]
  change lieB (G *ᵥ P) (M i) = 0
  rw [lieB_G_mulVec]
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hP
  simpa [mulVec] using congrFun hP i

/-- **Row 4.** Every multiple of the G-adjoint cofactor vector is `B`-orthogonal to every row. -/
theorem B_G_cofactor_row_smul (M : Matrix (Fin 4) (Fin 5) ℝ) (c : ℝ) (i : Fin 4) :
    (Matrix.toLinearMap₂' ℝ G).IsOrtho (G *ᵥ (c • cofactor M)) (M i) :=
  B_G_ker_row M _ (Submodule.smul_mem _ c (cofactor_mem_ker M)) i

/-- **Row 4 (source form).** -/
theorem B_G_cofactor_row (M : Matrix (Fin 4) (Fin 5) ℝ) (i : Fin 4) :
    (Matrix.toLinearMap₂' ℝ G).IsOrtho (G *ᵥ cofactor M) (M i) :=
  B_G_ker_row M _ (cofactor_mem_ker M) i

/-! ## Row 5. `PaperK.prop31_cofactor` -/

theorem prop31 (X : Fin 4 → Fin 5 → ℝ) (i : Fin 4) (A A' P : Fin 5 → ℝ)
    (hspan : ∀ Y, (∀ j, j ≠ i → lieB Y (X j) = 0) → Y ∈ Submodule.span ℝ {A, A'})
    (hP : ∀ j, lieB P (X j) = 0)
    (hA : A 3 ≠ 0) (hA' : A' 3 ≠ 0) (hP3 : P 3 ≠ 0) :
    P ∈ Submodule.span ℝ {A, A'} ∧
      Collinear ℝ ({pX P, pX A, pX A'} : Set E2) := by
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

/-- **Row 5.** Collinearity of `P_X` (cofactor point), `A_X`, `A'_X` in the Euclidean plane. -/
theorem prop31_cofactor (M : Matrix (Fin 4) (Fin 5) ℝ) (i : Fin 4) (A A' : Fin 5 → ℝ)
    (hspan : ∀ Y, (∀ j, j ≠ i → lieB Y (M j) = 0) → Y ∈ Submodule.span ℝ {A, A'})
    (hA : A 3 ≠ 0) (hA' : A' 3 ≠ 0) (hP3 : (G *ᵥ cofactor M) 3 ≠ 0) :
    Collinear ℝ ({pX (G *ᵥ cofactor M), pX A, pX A'} : Set E2) :=
  (prop31 (fun j => M j) i A A' _ hspan (fun j => B_G_cofactor_row M j) hA hA' hP3).2

/-! ## Row 6. `PaperK.explicit_power_indep`, via `Sphere.power` -/

/-- `det [u₁ u₂ u₃ u₄]` of four column vectors, via `Matrix.det`. -/
def det4 (u₁ u₂ u₃ u₄ : Fin 4 → ℝ) : ℝ :=
  (Matrix.of fun i => ![u₁ i, u₂ i, u₃ i, u₄ i]).det

theorem det4_eq (u1 u2 u3 u4 : Fin 4 → ℝ) :
    det4 u1 u2 u3 u4 = 0 + u1 0*u2 1*u3 2*u4 3 - u1 0*u2 1*u4 2*u3 3 - u1 0*u3 1*u2 2*u4 3 + u1 0*u3 1*u4 2*u2 3 + u1 0*u4 1*u2 2*u3 3 - u1 0*u4 1*u3 2*u2 3 - u2 0*u1 1*u3 2*u4 3 + u2 0*u1 1*u4 2*u3 3 + u2 0*u3 1*u1 2*u4 3 - u2 0*u3 1*u4 2*u1 3 - u2 0*u4 1*u1 2*u3 3 + u2 0*u4 1*u3 2*u1 3 + u3 0*u1 1*u2 2*u4 3 - u3 0*u1 1*u4 2*u2 3 - u3 0*u2 1*u1 2*u4 3 + u3 0*u2 1*u4 2*u1 3 + u3 0*u4 1*u1 2*u2 3 - u3 0*u4 1*u2 2*u1 3 - u4 0*u1 1*u2 2*u3 3 + u4 0*u1 1*u3 2*u2 3 + u4 0*u2 1*u1 2*u3 3 - u4 0*u2 1*u3 2*u1 3 - u4 0*u3 1*u1 2*u2 3 + u4 0*u3 1*u2 2*u1 3 := by
  rw [det4, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

theorem row_relation (u1 u2 u3 u4 : Fin 4 → ℝ) (i : Fin 4) :
    u1 i * det4 u2 u3 u4 1 - u2 i * det4 u1 u3 u4 1 + u3 i * det4 u1 u2 u4 1
      - u4 i * det4 u1 u2 u3 1 + det4 u1 u2 u3 u4 = 0 := by
  simp only [det4_eq, Pi.one_apply]
  fin_cases i <;> simp <;> ring

/-- **Row 6 (common value).** Circle `i` has centre `c i` and signed radius `r i`. With
`D = det[r a b 1] ≠ 0` the explicit point `p` and radius `ρ` give `Sphere.power ⟨c i, ρ − r i⟩ p`
the `i`-independent value `p₀² + p₁² − ρ² + det[r a b s]/D`. -/
theorem explicit_power_sphere (r : Fin 4 → ℝ) (c : Fin 4 → E2)
    (hD : det4 r (fun i => c i 0) (fun i => c i 1) 1 ≠ 0) (i : Fin 4) :
    let a := fun i => c i 0
    let b := fun i => c i 1
    let s := fun i => a i ^ 2 + b i ^ 2 - r i ^ 2
    let D := det4 r a b 1
    let pa := -det4 r b s 1 / (2 * D)
    let pb := det4 r a s 1 / (2 * D)
    let ρ := -det4 a b s 1 / (2 * D)
    (⟨c i, ρ - r i⟩ : Sphere E2).power !₂[pa, pb]
      = pa ^ 2 + pb ^ 2 - ρ ^ 2 + det4 r a b s / D := by
  intro a b s D pa pb ρ
  have hrow : r i * det4 a b s 1 - a i * det4 r b s 1 + b i * det4 r a s 1
      - s i * det4 r a b 1 + det4 r a b s = 0 := row_relation r a b s i
  unfold Sphere.power
  simp only
  rw [dist_sq2]
  simp only [PiLp.toLp_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have key : (pa - c i 0) ^ 2 + (pb - c i 1) ^ 2 - (ρ - r i) ^ 2 - (pa ^ 2 + pb ^ 2 - ρ ^ 2)
      = s i - (2 * pa * a i + 2 * pb * b i - 2 * ρ * r i) := by
    simp only [s, a, b]; ring
  have hlin : s i - (2 * pa * a i + 2 * pb * b i - 2 * ρ * r i) = det4 r a b s / D := by
    simp only [pa, pb, ρ]
    have hD' : D ≠ 0 := hD
    field_simp
    linear_combination (-1 : ℝ) * hrow
  linarith

/-- **Row 6.** The four `Sphere.power`s at the explicit point are independent of the index. -/
theorem explicit_power_indep (r : Fin 4 → ℝ) (c : Fin 4 → E2)
    (hD : det4 r (fun i => c i 0) (fun i => c i 1) 1 ≠ 0) (i j : Fin 4) :
    let a := fun i => c i 0
    let b := fun i => c i 1
    let s := fun i => a i ^ 2 + b i ^ 2 - r i ^ 2
    let D := det4 r a b 1
    let pa := -det4 r b s 1 / (2 * D)
    let pb := det4 r a s 1 / (2 * D)
    let ρ := -det4 a b s 1 / (2 * D)
    (⟨c i, ρ - r i⟩ : Sphere E2).power !₂[pa, pb]
      = (⟨c j, ρ - r j⟩ : Sphere E2).power !₂[pa, pb] := by
  intro a b s D pa pb ρ
  rw [explicit_power_sphere r c hD i, explicit_power_sphere r c hD j]

/-! ## Row 7. `PaperK2.square_null_space`, as a matrix kernel -/

/-- Square centres `(1,1), (−1,1), (−1,−1), (1,−1)` (source order `sqa = ![1,-1,-1,1]`,
`sqb = ![1,1,-1,-1]`). -/
def sqc : Fin 4 → E2 := ![!₂[1, 1], !₂[-1, 1], !₂[-1, -1], !₂[1, -1]]

/-- The `4 × 5` matrix whose rows are the (G-dualised) four unit circles of the square:
`(Msq *ᵥ P) i = B(P, circ 1 (sqc i))`. -/
def Msq : Matrix (Fin 4) (Fin 5) ℝ := Matrix.of fun i => G *ᵥ circ 1 (sqc i)

theorem Msq_mulVec (P : Fin 5 → ℝ) (i : Fin 4) : (Msq *ᵥ P) i = lieB P (circ 1 (sqc i)) := by
  change (G *ᵥ circ 1 (sqc i)) ⬝ᵥ P = _
  rw [lieB_apply]
  simp [G, mulVec, dotProduct, Fin.sum_univ_five]; ring

/-- **Row 7 (source form, Mathlib `lieB`).** -/
theorem square_null_space (P : Fin 5 → ℝ) :
    (∀ i : Fin 4, lieB P (circ 1 (sqc i)) = 0) ↔
      (P 1 = 0 ∧ P 2 = 0 ∧ P 4 = P 0 + P 3 / 2) := by
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, lieB_apply]
  simp [circ, sqc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    refine ⟨by ring, by ring, by ring, by ring⟩

theorem mem_ker_Msq (P : Fin 5 → ℝ) :
    P ∈ LinearMap.ker Msq.mulVecLin ↔ (P 1 = 0 ∧ P 2 = 0 ∧ P 4 = P 0 + P 3 / 2) := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← square_null_space, funext_iff]
  simp only [Msq_mulVec, Pi.zero_apply]

def v1 : Fin 5 → ℝ := ![1, 0, 0, 0, 1]
def v2 : Fin 5 → ℝ := ![0, 0, 0, 1, 1 / 2]

/-- **Row 7.** `ker Msq = span {(1,0,0,0,1), (0,0,0,1,1/2)}`. -/
theorem ker_Msq : LinearMap.ker Msq.mulVecLin = Submodule.span ℝ {v1, v2} := by
  ext P
  rw [mem_ker_Msq, Submodule.mem_span_pair]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨P 0, P 3, ?_⟩
    funext i
    fin_cases i <;> simp [v1, v2, h1, h2, h3] <;> ring
  · rintro ⟨s, u, rfl⟩
    simp [v1, v2]
    ring

theorem v1_v2_linearIndependent : LinearIndependent ℝ ![v1, v2] := by
  rw [LinearIndependent.pair_iff]
  intro s u h
  have h0 := congrFun h 0
  have h3 := congrFun h 3
  simp [v1, v2] at h0 h3
  exact ⟨h0, h3⟩

/-- **Row 7.** The kernel is **two**-dimensional. -/
theorem finrank_ker_Msq : finrank ℝ (LinearMap.ker Msq.mulVecLin) = 2 := by
  rw [ker_Msq, ← Matrix.range_cons_cons_empty v1 v2 ![]]
  rw [finrank_span_eq_card v1_v2_linearIndependent]
  simp

/-- **Row 7.** Hence `Msq` has rank 3 (rank-nullity). -/
theorem rank_Msq : Msq.rank = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker Msq.mulVecLin
  rw [finrank_ker_Msq, Module.finrank_fin_fun] at h
  unfold Matrix.rank
  omega

/-- **Row 7 (correction to the brief).** The kernel is *not* one-dimensional: it is not the span
of any single vector. -/
theorem ker_Msq_not_span_singleton : ¬ ∃ v : Fin 5 → ℝ,
    LinearMap.ker Msq.mulVecLin = Submodule.span ℝ {v} := by
  rintro ⟨v, hv⟩
  have h := finrank_ker_Msq
  rw [hv] at h
  have hle : finrank ℝ (Submodule.span ℝ ({v} : Set (Fin 5 → ℝ))) ≤ 1 := by
    have := finrank_span_le_card (R := ℝ) ({v} : Set (Fin 5 → ℝ))
    simpa using this
  omega

/-! ## Row 8. `PaperK2.equal_power_point_unique`, via `Affine.Simplex.circumcenter` -/

def D3 (a b : Fin 3 → ℝ) : ℝ := (a 1 - a 0) * (b 2 - b 0) - (a 2 - a 0) * (b 1 - b 0)

def ccx (a b : Fin 3 → ℝ) : ℝ :=
  (((a 1) ^ 2 - (a 0) ^ 2 + (b 1) ^ 2 - (b 0) ^ 2) * (b 2 - b 0)
    - ((a 2) ^ 2 - (a 0) ^ 2 + (b 2) ^ 2 - (b 0) ^ 2) * (b 1 - b 0)) / (2 * D3 a b)

def ccy (a b : Fin 3 → ℝ) : ℝ :=
  ((a 1 - a 0) * ((a 2) ^ 2 - (a 0) ^ 2 + (b 2) ^ 2 - (b 0) ^ 2)
    - (a 2 - a 0) * ((a 1) ^ 2 - (a 0) ^ 2 + (b 1) ^ 2 - (b 0) ^ 2)) / (2 * D3 a b)

/-- The three centres as points of the Euclidean plane. -/
def tri (a b : Fin 3 → ℝ) : Fin 3 → E2 := fun i => !₂[a i, b i]

/-- **Row 8 (main).** For a triangle `s` and three circles of common radius `r₀` centred at its
vertices, a point has equal `Sphere.power` (radius `ρ − r₀`) to all three iff it is the circumcentre. -/
theorem equal_power_point_unique (s : Affine.Triangle ℝ E2) (r₀ ρ : ℝ) (x : E2) :
    ((⟨s.points 0, ρ - r₀⟩ : Sphere E2).power x = (⟨s.points 1, ρ - r₀⟩ : Sphere E2).power x ∧
     (⟨s.points 0, ρ - r₀⟩ : Sphere E2).power x = (⟨s.points 2, ρ - r₀⟩ : Sphere E2).power x)
      ↔ x = s.circumcenter := by
  simp only [Sphere.power]
  constructor
  · rintro ⟨h1, h2⟩
    have hspan : affineSpan ℝ (Set.range s.points) = ⊤ :=
      (s.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by simp)
    refine s.eq_circumcenter_of_dist_eq (r := dist (s.points 0) x) (by rw [hspan]; trivial) ?_
    intro i
    rw [dist_comm, dist_comm (s.points 0)]
    have hsq : dist x (s.points i) ^ 2 = dist x (s.points 0) ^ 2 := by
      fin_cases i
      · rfl
      · simp only [Fin.mk_one]; linarith
      · simp only [Fin.reduceFinMk]; linarith
    exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 hsq
  · rintro rfl
    simp only [s.dist_circumcenter_eq_circumradius']
    exact ⟨trivial, trivial⟩

/-- **Row 8 bridge (proved here).** `D3 a b ≠ 0 ↔ AffineIndependent ℝ (tri a b)`. -/
theorem D3_ne_zero_iff_affineIndependent (a b : Fin 3 → ℝ) :
    D3 a b ≠ 0 ↔ AffineIndependent ℝ (tri a b) := by
  rw [affineIndependent_iff_of_fintype]
  have hcomp : ∀ w : Fin 3 → ℝ, ∑ i, w i = 0 →
      (Finset.univ.weightedVSub (tri a b) w = (0 : E2) ↔
        (w 0 * a 0 + w 1 * a 1 + w 2 * a 2 = 0 ∧ w 0 * b 0 + w 1 * b 1 + w 2 * b 2 = 0)) := by
    intro w hw
    rw [Finset.weightedVSub_eq_linear_combination _ hw]
    constructor
    · intro h
      have e0 := congrArg (fun z : E2 => z 0) h
      have e1 := congrArg (fun z : E2 => z 1) h
      simp [Fin.sum_univ_three, tri] at e0 e1
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h0, h1⟩
      ext k
      fin_cases k
      · simp [Fin.sum_univ_three, tri]; linarith
      · simp [Fin.sum_univ_three, tri]; linarith
  unfold D3
  constructor
  · intro hD w hw hs
    have hw' : w 0 + w 1 + w 2 = 0 := by simpa [Fin.sum_univ_three] using hw
    obtain ⟨ea, eb⟩ := (hcomp w hw).1 hs
    have m1 : ((a 1 - a 0) * (b 2 - b 0) - (a 2 - a 0) * (b 1 - b 0)) * w 1 = 0 := by
      linear_combination (b 2 - b 0) * (ea - a 0 * hw') - (a 2 - a 0) * (eb - b 0 * hw')
    have m2 : ((a 1 - a 0) * (b 2 - b 0) - (a 2 - a 0) * (b 1 - b 0)) * w 2 = 0 := by
      linear_combination (a 1 - a 0) * (eb - b 0 * hw') - (b 1 - b 0) * (ea - a 0 * hw')
    have h1 := (mul_eq_zero.1 m1).resolve_left hD
    have h2 := (mul_eq_zero.1 m2).resolve_left hD
    intro i
    fin_cases i
    · simp; linarith
    · exact h1
    · exact h2
  · intro h hD
    have key : ∀ w1 w2 : ℝ,
        w1 * (a 1 - a 0) + w2 * (a 2 - a 0) = 0 → w1 * (b 1 - b 0) + w2 * (b 2 - b 0) = 0 →
        w1 = 0 ∧ w2 = 0 := by
      intro w1 w2 ha hb
      have hw : ∑ i, (![-(w1 + w2), w1, w2] : Fin 3 → ℝ) i = 0 := by
        simp [Fin.sum_univ_three]
      have hs := (hcomp _ hw).2 ⟨by simp; linarith, by simp; linarith⟩
      exact ⟨by simpa using h _ hw hs 1, by simpa using h _ hw hs 2⟩
    obtain ⟨ha2, ha1⟩ := key (a 2 - a 0) (-(a 1 - a 0)) (by ring)
      (by linear_combination (-1 : ℝ) * hD)
    obtain ⟨hb2, hb1⟩ := key (b 2 - b 0) (-(b 1 - b 0))
      (by linear_combination -(b 2 - b 0) * ha1 - (b 1 - b 0) * ha2) (by ring)
    have := (key 1 0 (by linarith) (by linarith)).1
    norm_num at this

lemma cc_generic (a0 a1 a2 b0 b1 b2 : ℝ)
    (hD : (a1 - a0) * (b2 - b0) - (a2 - a0) * (b1 - b0) ≠ 0) (x y : ℝ)
    (hx : x = ((a1 ^ 2 - a0 ^ 2 + b1 ^ 2 - b0 ^ 2) * (b2 - b0)
      - (a2 ^ 2 - a0 ^ 2 + b2 ^ 2 - b0 ^ 2) * (b1 - b0)) /
        (2 * ((a1 - a0) * (b2 - b0) - (a2 - a0) * (b1 - b0))))
    (hy : y = ((a1 - a0) * (a2 ^ 2 - a0 ^ 2 + b2 ^ 2 - b0 ^ 2)
      - (a2 - a0) * (a1 ^ 2 - a0 ^ 2 + b1 ^ 2 - b0 ^ 2)) /
        (2 * ((a1 - a0) * (b2 - b0) - (a2 - a0) * (b1 - b0)))) :
    (x - a0) ^ 2 + (y - b0) ^ 2 = (x - a1) ^ 2 + (y - b1) ^ 2 ∧
    (x - a0) ^ 2 + (y - b0) ^ 2 = (x - a2) ^ 2 + (y - b2) ^ 2 := by
  set D := (a1 - a0) * (b2 - b0) - (a2 - a0) * (b1 - b0) with hDdef
  have h2D : (2 * D) ≠ 0 := mul_ne_zero two_ne_zero hD
  have ex : x * (2 * D) = (a1 ^ 2 - a0 ^ 2 + b1 ^ 2 - b0 ^ 2) * (b2 - b0)
      - (a2 ^ 2 - a0 ^ 2 + b2 ^ 2 - b0 ^ 2) * (b1 - b0) := by
    rw [hx]; exact div_mul_cancel₀ _ h2D
  have ey : y * (2 * D) = (a1 - a0) * (a2 ^ 2 - a0 ^ 2 + b2 ^ 2 - b0 ^ 2)
      - (a2 - a0) * (a1 ^ 2 - a0 ^ 2 + b1 ^ 2 - b0 ^ 2) := by
    rw [hy]; exact div_mul_cancel₀ _ h2D
  have l1 : D * (2 * (a1 - a0) * x + 2 * (b1 - b0) * y - (a1 ^ 2 - a0 ^ 2 + b1 ^ 2 - b0 ^ 2)) = 0 := by
    linear_combination (a1 - a0) * ex + (b1 - b0) * ey
  have l2 : D * (2 * (a2 - a0) * x + 2 * (b2 - b0) * y - (a2 ^ 2 - a0 ^ 2 + b2 ^ 2 - b0 ^ 2)) = 0 := by
    linear_combination (a2 - a0) * ex + (b2 - b0) * ey
  have m1 := (mul_eq_zero.1 l1).resolve_left hD
  have m2 := (mul_eq_zero.1 l2).resolve_left hD
  constructor
  · linear_combination m1
  · linear_combination m2

/-- The triangle of three non-collinear centres. -/
def triS (a b : Fin 3 → ℝ) (hD : D3 a b ≠ 0) : Affine.Triangle ℝ E2 :=
  ⟨tri a b, (D3_ne_zero_iff_affineIndependent a b).1 hD⟩

/-- **Row 8 bridge (proved here).** The Cramer formula `(ccx, ccy)` is Mathlib's circumcentre. -/
theorem circumcenter_eq_cc (a b : Fin 3 → ℝ) (hD : D3 a b ≠ 0) :
    (triS a b hD).circumcenter = !₂[ccx a b, ccy a b] := by
  symm
  have hspan : affineSpan ℝ (Set.range (triS a b hD).points) = ⊤ :=
    ((triS a b hD).independent.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by simp)
  obtain ⟨e1, e2⟩ := cc_generic (a 0) (a 1) (a 2) (b 0) (b 1) (b 2) hD (ccx a b) (ccy a b) rfl rfl
  refine (triS a b hD).eq_circumcenter_of_dist_eq
    (r := dist ((triS a b hD).points 0) !₂[ccx a b, ccy a b]) (by rw [hspan]; trivial) ?_
  intro i
  refine (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 ?_
  rw [dist_sq2, dist_sq2]
  simp only [triS, tri, PiLp.toLp_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases i
  · rfl
  · simp; linarith
  · simp; linarith

/-- **Row 8 (source form, proved through the Mathlib statement).** For `D3 a b ≠ 0`, equal Laguerre
power to three circles of common radius `r₀` pins `(x, y) = (ccx, ccy)`. -/
theorem equal_power_point_unique_coords (a b : Fin 3 → ℝ) (hD : D3 a b ≠ 0) (r₀ ρ x y : ℝ) :
    ((x - a 0) ^ 2 + (y - b 0) ^ 2 - (ρ - r₀) ^ 2 = (x - a 1) ^ 2 + (y - b 1) ^ 2 - (ρ - r₀) ^ 2 ∧
     (x - a 0) ^ 2 + (y - b 0) ^ 2 - (ρ - r₀) ^ 2 = (x - a 2) ^ 2 + (y - b 2) ^ 2 - (ρ - r₀) ^ 2)
    ↔ (x = ccx a b ∧ y = ccy a b) := by
  have key := equal_power_point_unique (triS a b hD) r₀ ρ !₂[x, y]
  rw [circumcenter_eq_cc] at key
  simp only [Sphere.power, dist_sq2, triS, tri, PiLp.toLp_apply] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at key
  have hxy : (!₂[x, y] : E2) = !₂[ccx a b, ccy a b] ↔ (x = ccx a b ∧ y = ccy a b) := by
    constructor
    · intro h
      have h0 := congrArg (fun z : E2 => z 0) h
      have h1 := congrArg (fun z : E2 => z 1) h
      simp at h0 h1
      exact ⟨h0, h1⟩
    · rintro ⟨rfl, rfl⟩; rfl
  rw [← hxy, ← key]

end

end PaperKL14b
