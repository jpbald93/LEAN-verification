import Mathlib

/-!
# Paper K core (K1): the Lie form, the cofactor point `P_X`, Prop 3.1

Coordinates at `n = 2`: `X : Fin 5 → ℝ` ordered `(r, a, b, v, w)`, i.e. Lean index
`0 = r`, `1, 2 = c`, `3 = v`, `4 = w`.  The paper's 1-based slots `p₂,p₃ | p₄` are Lean
indices `1, 2 | 3`, so `P_X = (P 1, P 2) / P 3`.
-/

namespace PaperK

open Matrix

/-- The Lie form `B(X,Y) = r r' − c·c' − v w' − w v'` at `n = 2`. -/
def B (X Y : Fin 5 → ℝ) : ℝ := X 0*Y 0 - X 1*Y 1 - X 2*Y 2 - X 3*Y 4 - X 4*Y 3

/-- Gram matrix `G = diag(1, −1, −1, [[0,−1],[−1,0]])`. -/
def G : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
     0, -1, 0, 0, 0;
     0, 0, -1, 0, 0;
     0, 0, 0, 0, -1;
     0, 0, 0, -1, 0]

/-! ## A. Null cone (Lemma 2.4) -/

theorem B_self_eq_zero_iff (X : Fin 5 → ℝ) :
    B X X = 0 ↔ (X 0)^2 - (X 1)^2 - (X 2)^2 = 2*(X 3)*(X 4) := by
  unfold B
  constructor <;> intro h <;> linear_combination h

/-! ## B. Tangency identity (Lemma 2.5) -/

theorem tangency_identity (X Y : Fin 5 → ℝ) (hX : B X X = 0) (hY : B Y Y = 0) :
    -2 * X 3 * Y 3 * B X Y
      = (X 0*Y 3 - Y 0*X 3)^2 - ((X 1*Y 3 - Y 1*X 3)^2 + (X 2*Y 3 - Y 2*X 3)^2) := by
  unfold B at *
  linear_combination -(Y 3)^2 * hX - (X 3)^2 * hY

theorem tangency_of_B_eq_zero (X Y : Fin 5 → ℝ) (hX : B X X = 0) (hY : B Y Y = 0)
    (h : B X Y = 0) :
    (X 0*Y 3 - Y 0*X 3)^2 = (X 1*Y 3 - Y 1*X 3)^2 + (X 2*Y 3 - Y 2*X 3)^2 := by
  have := tangency_identity X Y hX hY
  rw [h] at this
  linarith

theorem B_eq_zero_iff_tangent (X Y : Fin 5 → ℝ) (hX : B X X = 0) (hY : B Y Y = 0)
    (hv : X 3 ≠ 0) (hv' : Y 3 ≠ 0) :
    B X Y = 0 ↔
      (X 0*Y 3 - Y 0*X 3)^2 = (X 1*Y 3 - Y 1*X 3)^2 + (X 2*Y 3 - Y 2*X 3)^2 := by
  refine ⟨tangency_of_B_eq_zero X Y hX hY, fun h => ?_⟩
  have hid := tangency_identity X Y hX hY
  have h2 : -2 * X 3 * Y 3 * B X Y = 0 := by rw [hid]; linarith
  have hne : -2 * X 3 * Y 3 ≠ 0 := by
    have : (-2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero this hv) hv'
  exact (mul_eq_zero.mp h2).resolve_left hne


/-- `B X Y = Xᵀ G Y`. -/
theorem B_eq_dot_G (X Y : Fin 5 → ℝ) : B X Y = X ⬝ᵥ (G *ᵥ Y) := by
  simp [B, G, mulVec, dotProduct, Fin.sum_univ_five]; ring

theorem G_mul_G : G * G = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [G, Matrix.mul_apply, Fin.sum_univ_five]

/-- The G-adjoint of `P` pairs with `Y` as the plain dot product. -/
theorem B_G_mulVec (P Y : Fin 5 → ℝ) : B (G *ᵥ P) Y = Y ⬝ᵥ P := by
  simp [B, G, mulVec, dotProduct, Fin.sum_univ_five]; ring

/-! ## C. The cofactor vector -/

/-- Signed `4 × 4` minors of a `4 × 5` matrix (generalised cross product). -/
noncomputable def cofactor (M : Matrix (Fin 4) (Fin 5) ℝ) : Fin 5 → ℝ :=
  fun k => (-1 : ℝ) ^ (k : ℕ) * (M.submatrix id (Fin.succAbove k)).det

/-- Laplace expansion of the `5 × 5` determinant with a repeated row. -/
theorem mulVec_cofactor (M : Matrix (Fin 4) (Fin 5) ℝ) : M *ᵥ cofactor M = 0 := by
  funext i
  let N : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of (Fin.cons (M i) (fun j => M j))
  have hN : N.det = 0 := by
    refine Matrix.det_zero_of_row_eq (i := 0) (j := i.succ) (Fin.succ_ne_zero i).symm ?_
    funext k; simp [N]
  have hexp := Matrix.det_succ_row_zero N
  rw [hN] at hexp
  simp only [Pi.zero_apply, mulVec, dotProduct, cofactor]
  rw [hexp]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : N.submatrix Fin.succ k.succAbove = M.submatrix id k.succAbove := by
    ext a b; simp [N]
  rw [this]; simp [N]; ring

/-- The G-adjoint `Q = G P` of the cofactor vector is B-orthogonal to every row. -/
theorem B_G_cofactor_row (M : Matrix (Fin 4) (Fin 5) ℝ) (i : Fin 4) :
    B (G *ᵥ cofactor M) (M i) = 0 := by
  rw [B_G_mulVec]
  have := congrFun (mulVec_cofactor M) i
  simpa [mulVec] using this

/-! ## D. Prop 3.1, the collinearity step -/

/-- Affine point `P_X = (P 1, P 2) / P 3` (paper slots `(p₂, p₃)/p₄`). -/
noncomputable def pt (P : Fin 5 → ℝ) : ℝ × ℝ := (P 1 / P 3, P 2 / P 3)

/-- If `P = α A + β A'` and all v-slots are nonzero, `pt P` lies on the line through
`pt A` and `pt A'` (explicit affine combination). -/
theorem pt_affine_comb (A A' : Fin 5 → ℝ) (α β : ℝ)
    (hA : A 3 ≠ 0) (hA' : A' 3 ≠ 0) (hP : (α • A + β • A') 3 ≠ 0) :
    ∃ s t : ℝ, s + t = 1 ∧ pt (α • A + β • A') = s • pt A + t • pt A' := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hP
  refine ⟨α * A 3 / (α * A 3 + β * A' 3), β * A' 3 / (α * A 3 + β * A' 3), ?_, ?_⟩
  · field_simp
  · simp only [pt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> field_simp

/-- **Prop 3.1 (collinearity step).** If the B-orthogonal complement of the rows `j ≠ i`
is spanned by `A, A'` and `P` is B-orthogonal to all rows, then `P ∈ span {A, A'}` and
`P_X, A_X, A'_X` are collinear. -/
theorem prop31 (X : Fin 4 → Fin 5 → ℝ) (i : Fin 4) (A A' P : Fin 5 → ℝ)
    (hspan : ∀ Y, (∀ j, j ≠ i → B Y (X j) = 0) → Y ∈ Submodule.span ℝ {A, A'})
    (hP : ∀ j, B P (X j) = 0)
    (hA : A 3 ≠ 0) (hA' : A' 3 ≠ 0) (hP3 : P 3 ≠ 0) :
    P ∈ Submodule.span ℝ {A, A'} ∧
      (∃ s t : ℝ, s + t = 1 ∧ pt P = s • pt A + t • pt A') ∧
      Collinear ℝ ({pt P, pt A, pt A'} : Set (ℝ × ℝ)) := by
  have hmem : P ∈ Submodule.span ℝ {A, A'} := hspan P (fun j _ => hP j)
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
  subst hαβ
  obtain ⟨s, t, hst, hpt⟩ := pt_affine_comb A A' α β hA hA' hP3
  refine ⟨hmem, ⟨s, t, hst, hpt⟩, ?_⟩
  apply collinear_insert_of_mem_affineSpan_pair
  have : pt (α • A + β • A') = AffineMap.lineMap (pt A) (pt A') t := by
    rw [hpt, AffineMap.lineMap_apply_module, ← hst]; simp
  rw [this]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- Prop 3.1 specialised to the G-adjoint cofactor vector of the four rows. -/
theorem prop31_cofactor (M : Matrix (Fin 4) (Fin 5) ℝ) (i : Fin 4) (A A' : Fin 5 → ℝ)
    (hspan : ∀ Y, (∀ j, j ≠ i → B Y (M j) = 0) → Y ∈ Submodule.span ℝ {A, A'})
    (hA : A 3 ≠ 0) (hA' : A' 3 ≠ 0) (hP3 : (G *ᵥ cofactor M) 3 ≠ 0) :
    Collinear ℝ ({pt (G *ᵥ cofactor M), pt A, pt A'} : Set (ℝ × ℝ)) :=
  (prop31 (fun j => M j) i A A' _ hspan (B_G_cofactor_row M) hA hA' hP3).2.2

/-! ## F. Equal Laguerre power -/

/-- Laguerre power of the point/radius `(p, ρ)` w.r.t. the normalised cycle `Y`. -/
def power (p : ℝ × ℝ) (ρ : ℝ) (Y : Fin 5 → ℝ) : ℝ :=
  (p.1 - Y 1)^2 + (p.2 - Y 2)^2 - (ρ - Y 0)^2

/-- **F.** If `P ⊥_B Y` for a normalised cycle `Y` (`v = 1`, null) and `P 3 ≠ 0`, then the
Laguerre power of `(P_X, ρ = P 0 / P 3)` w.r.t. `Y` equals the `Y`-independent constant
`−B(P,P)/P 3²`. -/
theorem power_eq_of_B_eq_zero (P Y : Fin 5 → ℝ) (hP3 : P 3 ≠ 0) (hv : Y 3 = 1)
    (hnull : B Y Y = 0) (h : B P Y = 0) :
    power (pt P) (P 0 / P 3) Y = -B P P / (P 3)^2 := by
  unfold power pt
  unfold B at *
  rw [hv] at hnull h
  field_simp
  linear_combination (-(P 3)^2) * hnull + (2 * P 3) * h

theorem equal_power {ι : Type*} (X : ι → Fin 5 → ℝ) (P : Fin 5 → ℝ) (hP3 : P 3 ≠ 0)
    (hv : ∀ i, X i 3 = 1) (hnull : ∀ i, B (X i) (X i) = 0) (h : ∀ i, B P (X i) = 0)
    (i j : ι) :
    power (pt P) (P 0 / P 3) (X i) = power (pt P) (P 0 / P 3) (X j) := by
  rw [power_eq_of_B_eq_zero P _ hP3 (hv i) (hnull i) (h i),
    power_eq_of_B_eq_zero P _ hP3 (hv j) (hnull j) (h j)]


/-! ## E. The explicit `n = 2` formula (extension E2)

Sign convention: the K0-verified formula is
`P_X = (−det[r b s 1], det[r a s 1]) / (2 det[r a b 1])`, `ρ = −det[a b s 1]/(2 det[r a b 1])`.
(The brief's display has the `a`/`b` columns swapped; that version fails numerically.) -/

section E

variable (r a b : Fin 4 → ℝ)

/-- `s_i = a_i² + b_i² − r_i²`. -/
def sq (i : Fin 4) : ℝ := a i ^ 2 + b i ^ 2 - r i ^ 2

/-- The `4 × 5` matrix with rows `(r_i, a_i, b_i, s_i, 1)`. -/
def Mrow : Matrix (Fin 4) (Fin 5) ℝ := Matrix.of fun i => ![r i, a i, b i, sq r a b i, 1]

/-- `det [u₁ u₂ u₃ u₄]` for four column vectors. -/
noncomputable def det4 (u₁ u₂ u₃ u₄ : Fin 4 → ℝ) : ℝ :=
  (Matrix.of fun i => ![u₁ i, u₂ i, u₃ i, u₄ i]).det

lemma cof0 : cofactor (Mrow r a b) 0 = det4 a b (sq r a b) 1 := by
  simp only [cofactor, det4]
  rw [show ((-1 : ℝ) ^ ((0 : Fin 5) : ℕ)) = 1 by norm_num, one_mul]
  congr 1

lemma cof1 : cofactor (Mrow r a b) 1 = -det4 r b (sq r a b) 1 := by
  simp only [cofactor, det4]
  rw [show ((-1 : ℝ) ^ ((1 : Fin 5) : ℕ)) = -1 by norm_num, neg_one_mul]
  congr 2; ext i j; fin_cases j <;> rfl

lemma cof2 : cofactor (Mrow r a b) 2 = det4 r a (sq r a b) 1 := by
  simp only [cofactor, det4]
  rw [show ((-1 : ℝ) ^ ((2 : Fin 5) : ℕ)) = 1 by norm_num, one_mul]
  congr 1; ext i j; fin_cases j <;> rfl

lemma cof3 : cofactor (Mrow r a b) 3 = -det4 r a b 1 := by
  simp only [cofactor, det4]
  rw [show ((-1 : ℝ) ^ ((3 : Fin 5) : ℕ)) = -1 by norm_num, neg_one_mul]
  congr 2; ext i j; fin_cases j <;> rfl

lemma cof4 : cofactor (Mrow r a b) 4 = det4 r a b (sq r a b) := by
  simp only [cofactor, det4]
  rw [show ((-1 : ℝ) ^ ((4 : Fin 5) : ℕ)) = 1 by norm_num, one_mul]
  congr 1; ext i j; fin_cases j <;> rfl

/-- Row relation from the Laplace expansion: `r_i q₀ + a_i q₁ + b_i q₂ + s_i q₃ + q₄ = 0`. -/
lemma row_relation (i : Fin 4) :
    r i * det4 a b (sq r a b) 1 - a i * det4 r b (sq r a b) 1 + b i * det4 r a (sq r a b) 1
      - sq r a b i * det4 r a b 1 + det4 r a b (sq r a b) = 0 := by
  have h := congrFun (mulVec_cofactor (Mrow r a b)) i
  simp only [mulVec, dotProduct, Fin.sum_univ_five, Pi.zero_apply] at h
  rw [cof0, cof1, cof2, cof3, cof4] at h
  simp [Mrow] at h
  linear_combination h

/-- **E2.** With `D = det[r a b 1] ≠ 0`, the explicit point
`p = (−det[r b s 1], det[r a s 1]) / (2D)` and radius `ρ = −det[a b s 1]/(2D)` have the same
Laguerre power `‖p − c_i‖² − (ρ − r_i)²` with respect to all four circles; the common value is
`‖p‖² − ρ² + det[r a b s]/D`. -/
theorem explicit_power (hD : det4 r a b 1 ≠ 0) (i : Fin 4) :
    let D := det4 r a b 1
    let pa := -det4 r b (sq r a b) 1 / (2 * D)
    let pb := det4 r a (sq r a b) 1 / (2 * D)
    let ρ := -det4 a b (sq r a b) 1 / (2 * D)
    (pa - a i)^2 + (pb - b i)^2 - (ρ - r i)^2
      = pa^2 + pb^2 - ρ^2 + det4 r a b (sq r a b) / D := by
  intro D pa pb ρ
  have h := row_relation r a b i
  have hs : sq r a b i = a i ^ 2 + b i ^ 2 - r i ^ 2 := rfl
  have key : (pa - a i)^2 + (pb - b i)^2 - (ρ - r i)^2 - (pa^2 + pb^2 - ρ^2)
      = sq r a b i - (2 * pa * a i + 2 * pb * b i - 2 * ρ * r i) := by rw [hs]; ring
  have hlin : sq r a b i - (2 * pa * a i + 2 * pb * b i - 2 * ρ * r i)
      = det4 r a b (sq r a b) / D := by
    simp only [pa, pb, ρ, D]
    field_simp
    linear_combination (-1 : ℝ) * h
  linarith

theorem explicit_power_indep (hD : det4 r a b 1 ≠ 0) (i j : Fin 4) :
    let D := det4 r a b 1
    let pa := -det4 r b (sq r a b) 1 / (2 * D)
    let pb := det4 r a (sq r a b) 1 / (2 * D)
    let ρ := -det4 a b (sq r a b) 1 / (2 * D)
    (pa - a i)^2 + (pb - b i)^2 - (ρ - r i)^2 = (pa - a j)^2 + (pb - b j)^2 - (ρ - r j)^2 := by
  intro D pa pb ρ
  rw [explicit_power r a b hD i, explicit_power r a b hD j]

end E

end PaperK

#print axioms PaperK.B_self_eq_zero_iff
#print axioms PaperK.tangency_identity
#print axioms PaperK.B_eq_zero_iff_tangent
#print axioms PaperK.mulVec_cofactor
#print axioms PaperK.B_G_cofactor_row
#print axioms PaperK.prop31
#print axioms PaperK.prop31_cofactor
#print axioms PaperK.explicit_power
#print axioms PaperK.explicit_power_indep
#print axioms PaperK.equal_power
