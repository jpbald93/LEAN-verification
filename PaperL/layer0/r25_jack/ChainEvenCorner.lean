import Clifford.Mobius

/-!
# The Morley interpolation kernel (Paper L / J2)

Invert at `M = 0`: circle `k` (centre `c k`) becomes the line `w = a_k + t_k conj w`,
`a_k = 1/conj c_k`, `t_k = -c_k/conj c_k` (`onCircleM_iff_lineOf`, `lineOf_eq_line`).

* `K n a t`: the literal matrix of the brief (`j = 0 … ⌊n/2⌋` in both blocks). For even `n` it is
  `n × (n+2)` and `finrank ker ≥ 2` (`K_finrank_ker_ge_two`), so the rank-one statement is false
  for it. The working matrix is `Kc` / `Kf` (`Q`-block `j = 0 … n-⌊n/2⌋-1`), `n × (n+1)`.
* Rank: `finrank (ker) = 1` iff-direction we need holds under **one nonzero maximal minor**
  (`finrank_ker_eq_one`, `Kc_finrank_ker_eq_one`); the kernel is then spanned by the
  cross-product vector `crossVec` (`ker_eq_span_crossVec`, `Kf_ker_smul`).
* `n = 4`: `P₂ = mD`, `Q₁ = -mN`, so `-Q₁/P₂ = miquel` (`levelPoint_four`, `Kf_four_finrank`).
* `n = 5`: `P₀ = k3`, `Q₀ = k1`, `Q₂ = A57`, and by a three-term Plücker relation
  (`plucker5`, `k0k3_sub_k1k2`) the kernel circle is `k3 · cliffordEq` (`oddCircleEq_five_cross`,
  `oddCircle_five`, `step_four_five`).
* Step shape: `Kf_border_even`, `Kf_border_odd`; open step lemmas `StepEven`, `StepOdd` (defs).
-/

namespace Clifford.MorleyKernel

open Complex ComplexConjugate Matrix Module



/-! ## 1. Line model -/

/-- The inverted image of a circle through `M`: the line `w = a + t * conj w`. -/
def LineOf (a t w : ℂ) : Prop := w = a + t * conj w

theorem norm_t_eq_one {c : ℂ} (hc : c ≠ 0) : ‖-c / conj c‖ = 1 := by
  have : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  rw [norm_div, norm_neg, Complex.norm_conj, div_self this]

theorem lineOf_iff {c w : ℂ} (hc : c ≠ 0) :
    LineOf (1 / conj c) (-c / conj c) w ↔ w * conj c = 1 - c * conj w := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  have : 1 / conj c + (-c / conj c) * conj w = (1 - c * conj w) / conj c := by ring
  rw [LineOf, this, eq_div_iff hc']

/-- Inversion `z ↦ 1 / conj z` maps the circle through `0` with centre `c` onto `LineOf`. -/
theorem onCircleM_iff_lineOf {c z : ℂ} (hc : c ≠ 0) (hz : z ≠ 0) :
    OnCircleM c z ↔ LineOf (1 / conj c) (-c / conj c) (1 / conj z) := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  have hz' : conj z ≠ 0 := (map_ne_zero _).2 hz
  rw [onCircleM_iff, lineOf_iff hc]
  simp only [map_div₀, map_one, starRingEnd_self_apply]
  constructor
  · intro h; field_simp; linear_combination -h
  · intro h; field_simp at h; linear_combination -h

/-- `LineOf (1/conj c) (-c/conj c)` is exactly a (real) line, `p + ℝ v` with `v ≠ 0`. -/
theorem lineOf_eq_line {c : ℂ} (hc : c ≠ 0) :
    {w | LineOf (1 / conj c) (-c / conj c) w} =
      {w | ∃ s : ℝ, w = 1 / (2 * conj c) + s • (I / conj c)} := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  ext w
  simp only [Set.mem_ofPred_eq, lineOf_iff hc]
  constructor
  · intro h
    exact mem_line_of hc' (by rw [starRingEnd_self_apply]; linear_combination -h)
  · rintro ⟨s, rfl⟩
    simp only [Complex.real_smul, map_add, map_mul, map_div₀, map_one, Complex.conj_ofReal,
      Complex.conj_I, starRingEnd_self_apply, map_ofNat]
    field_simp
    ring

theorem exists_line {c : ℂ} (hc : c ≠ 0) :
    ∃ p v : ℂ, v ≠ 0 ∧ {w | LineOf (1 / conj c) (-c / conj c) w} = {w | ∃ s : ℝ, w = p + s • v} :=
  ⟨_, _, div_ne_zero I_ne_zero ((map_ne_zero _).2 hc), lineOf_eq_line hc⟩


/-! ## 2. The matrix -/



/-- The literal matrix of the brief: `j = 0 … ⌊n/2⌋` in **both** blocks
(`n × (2⌊n/2⌋+2)`; this is `n × (n+1)` only for odd `n`). -/
def K (n : ℕ) (a t : Fin n → ℂ) : Matrix (Fin n) (Fin (n / 2 + 1) ⊕ Fin (n / 2 + 1)) ℂ :=
  fun k j => match j with
    | Sum.inl j => t k ^ (j : ℕ)
    | Sum.inr j => -a k * t k ^ (j : ℕ)

/-- The corrected Morley matrix, `n × (n+1)`: `P`-block `j = 0 … ⌊n/2⌋`,
`Q`-block `j = 0 … n - ⌊n/2⌋ - 1` (`= ⌊n/2⌋ - 1` for even `n`, `⌊n/2⌋` for odd `n`). -/
def Kc (n : ℕ) (a t : Fin n → ℂ) : Matrix (Fin n) (Fin (n / 2 + 1) ⊕ Fin (n - n / 2)) ℂ :=
  fun k j => match j with
    | Sum.inl j => t k ^ (j : ℕ)
    | Sum.inr j => -a k * t k ^ (j : ℕ)

/-- The same matrix with the columns flattened to `Fin (n+1)`
(`P_0, …, P_m, Q_0, …`). -/
def Kf (n : ℕ) (a t : Fin n → ℂ) : Matrix (Fin n) (Fin (n + 1)) ℂ :=
  fun k j => if (j : ℕ) ≤ n / 2 then t k ^ (j : ℕ) else -a k * t k ^ ((j : ℕ) - (n / 2 + 1))

/-- The kernel of any matrix with more columns than rows is nontrivial. -/
theorem exists_ker_of_lt {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (h : Fintype.card ι < Fintype.card κ) : ∃ v ≠ 0, A *ᵥ v = 0 := by
  have hk : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨v, hv0, by simpa using hv⟩

theorem card_cols_K (n : ℕ) : Fintype.card (Fin (n / 2 + 1) ⊕ Fin (n / 2 + 1)) = 2 * (n / 2) + 2 := by
  simp; ring

theorem card_cols_Kc (n : ℕ) : Fintype.card (Fin (n / 2 + 1) ⊕ Fin (n - n / 2)) = n + 1 := by
  simp; omega

/-- Kernel existence for the literal matrix (all `n`). -/
theorem K_exists_ker (n : ℕ) (a t : Fin n → ℂ) : ∃ v ≠ 0, K n a t *ᵥ v = 0 :=
  exists_ker_of_lt _ (by rw [card_cols_K]; simp; omega)

/-- Kernel existence for the corrected matrix (all `n`). -/
theorem Kc_exists_ker (n : ℕ) (a t : Fin n → ℂ) : ∃ v ≠ 0, Kc n a t *ᵥ v = 0 :=
  exists_ker_of_lt _ (by rw [card_cols_Kc]; simp)

/-- rank–nullity for a matrix. -/
theorem finrank_ker_add_rank {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) :
    A.rank + finrank ℂ (LinearMap.ker A.mulVecLin) = Fintype.card κ := by
  have := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Matrix.rank]; simpa using this

/-- For **even** `n` the literal matrix `K` has a kernel of dimension `≥ 2`, so
`finrank (ker K) = 1` is false there; the statement must be made for `Kc`. -/
theorem K_finrank_ker_ge_two {n : ℕ} (hn : n % 2 = 0) (a t : Fin n → ℂ) :
    2 ≤ finrank ℂ (LinearMap.ker (K n a t).mulVecLin) := by
  have h1 := finrank_ker_add_rank (K n a t)
  have h2 := Matrix.rank_le_card_height (K n a t)
  rw [card_cols_K] at h1; simp at h2; omega

/-- **Rank statement.** If some `n × n` column-selection of `A : n × (n+1)` has nonzero
determinant, the kernel is a line. -/
theorem finrank_ker_eq_one {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (Fin n) κ ℂ) (hκ : Fintype.card κ = n + 1)
    (col : Fin n → κ) (hdet : (A.submatrix id col).det ≠ 0) :
    finrank ℂ (LinearMap.ker A.mulVecLin) = 1 := by
  have h1 := finrank_ker_add_rank A
  have h2 := Matrix.rank_le_card_height A
  have h3 : n ≤ A.rank := by
    have := Matrix.rank_submatrix_le A id col
    rw [Matrix.rank_of_det_ne_zero hdet] at this; simpa using this
  simp at h2; omega

/-- The rank statement for the corrected Morley matrix: under a nonzero maximal minor
(e.g. the denominator `P_m ≠ 0` of the level point), `finrank (ker Kc) = 1`. -/
theorem Kc_finrank_ker_eq_one {n : ℕ} (a t : Fin n → ℂ)
    (col : Fin n → Fin (n / 2 + 1) ⊕ Fin (n - n / 2))
    (hdet : ((Kc n a t).submatrix id col).det ≠ 0) :
    finrank ℂ (LinearMap.ker (Kc n a t).mulVecLin) = 1 :=
  finrank_ker_eq_one _ (card_cols_Kc n) col hdet

/-! ### The explicit kernel vector (generalized cross product) -/

/-- `crossVec A j = (-1)^j det (A without column j)`. -/
def crossVec {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) R) :
    Fin (n + 1) → R :=
  fun j => (-1) ^ (j : ℕ) * (A.submatrix id j.succAbove).det

/-- The cross-product vector is in the kernel (Laplace along a repeated row). -/
theorem mulVec_crossVec {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) R) :
    A *ᵥ crossVec A = 0 := by
  funext k
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun i l => Fin.cases (A k l) (fun r => A r l) i
  have hB : B.det = 0 :=
    Matrix.det_zero_of_row_eq (i := 0) (j := k.succ) (Fin.succ_ne_zero k).symm (by
      funext l; simp only [B, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ])
  rw [Matrix.det_succ_row_zero] at hB
  simp only [Pi.zero_apply, mulVec, dotProduct, crossVec]
  rw [← hB]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : B.submatrix Fin.succ j.succAbove = A.submatrix id j.succAbove := by
    ext r s; simp only [B, Matrix.submatrix_apply, Matrix.of_apply, Fin.cases_succ, id]
  rw [this]; simp only [B, Matrix.of_apply, Fin.cases_zero]; ring

theorem crossVec_ne_zero {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) R)
    (j : Fin (n + 1)) (h : (A.submatrix id j.succAbove).det ≠ 0) : crossVec A ≠ 0 := by
  intro h0
  have := congrFun h0 j
  simp only [crossVec, Pi.zero_apply] at this
  exact h ((isUnit_neg_one.pow _).mul_right_eq_zero.1 this)

/-- Under a nonzero maximal minor the kernel of `Kf` is spanned by the cross product. -/
theorem Kf_ker_eq_span {n : ℕ} (a t : Fin n → ℂ) (j : Fin (n + 1))
    (h : ((Kf n a t).submatrix id j.succAbove).det ≠ 0) :
    LinearMap.ker (Kf n a t).mulVecLin = Submodule.span ℂ {crossVec (Kf n a t)} := by
  have h1 := finrank_ker_eq_one (Kf n a t) (by simp) j.succAbove h
  have hv : crossVec (Kf n a t) ∈ LinearMap.ker (Kf n a t).mulVecLin := by
    simpa using mulVec_crossVec (Kf n a t)
  have hne := crossVec_ne_zero _ j h
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 hv
  · rw [h1, finrank_span_singleton hne]


/-! ## Polynomial (row-scaled) form and explicit coordinates -/



theorem det_fin_four' {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    A.det = det4 (A 0 0) (A 0 1) (A 0 2) (A 0 3) (A 1 0) (A 1 1) (A 1 2) (A 1 3)
      (A 2 0) (A 2 1) (A 2 2) (A 2 3) (A 3 0) (A 3 1) (A 3 2) (A 3 3) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.lt_def, det4, det3]
  ring

/-- Polynomial (row-scaled) Morley matrix in `x = c`, `y = conj c`: row `k` of `Kf` times
`y_k ^ (n - n/2)`. -/
def KP {R : Type*} [CommRing R] (n : ℕ) (x y : Fin n → R) : Matrix (Fin n) (Fin (n + 1)) R :=
  fun k j => if (j : ℕ) ≤ n / 2 then (-x k) ^ (j : ℕ) * y k ^ (n - n / 2 - j)
    else -((-x k) ^ ((j : ℕ) - (n / 2 + 1)) * y k ^ (n - n / 2 - 1 - ((j : ℕ) - (n / 2 + 1))))

/-- `aOf c = 1 / conj c`, `tOf c = - c / conj c`: the inverted lines. -/
noncomputable def aOf {n : ℕ} (c : Fin n → ℂ) : Fin n → ℂ := fun k => 1 / conj (c k)
noncomputable def tOf {n : ℕ} (c : Fin n → ℂ) : Fin n → ℂ := fun k => -c k / conj (c k)

theorem KP_eq_scale {n : ℕ} (c : Fin n → ℂ) (hc : ∀ k, c k ≠ 0) (k : Fin n) (j : Fin (n + 1)) :
    KP n c (fun k => conj (c k)) k j = conj (c k) ^ (n - n / 2) * Kf n (aOf c) (tOf c) k j := by
  have hy : conj (c k) ≠ 0 := (map_ne_zero _).2 (hc k)
  unfold KP Kf aOf tOf
  split_ifs with h
  · have e : conj (c k) ^ (n - n / 2) = conj (c k) ^ (n - n / 2 - j) * conj (c k) ^ (j : ℕ) := by
      rw [← pow_add]; congr 1; omega
    rw [e, div_pow]; field_simp
  · have e : conj (c k) ^ (n - n / 2) = conj (c k) ^ (n - n / 2 - 1 - ((j : ℕ) - (n / 2 + 1))) *
        conj (c k) ^ ((j : ℕ) - (n / 2 + 1)) * conj (c k) := by
      rw [← pow_add, ← pow_succ]; congr 1; omega
    rw [e, div_pow]; field_simp

/-- Row scaling does not change the kernel: `ker KP = ker Kf` for nonzero centres. -/
theorem KP_mulVec_eq_zero_iff {n : ℕ} (c : Fin n → ℂ) (hc : ∀ k, c k ≠ 0) (v : Fin (n + 1) → ℂ) :
    KP n c (fun k => conj (c k)) *ᵥ v = 0 ↔ Kf n (aOf c) (tOf c) *ᵥ v = 0 := by
  have h : ∀ k, (KP n c (fun k => conj (c k)) *ᵥ v) k =
      conj (c k) ^ (n - n / 2) * (Kf n (aOf c) (tOf c) *ᵥ v) k := by
    intro k
    simp only [mulVec, dotProduct, KP_eq_scale c hc, Finset.mul_sum, mul_assoc]
  constructor
  · intro h0; funext k
    have := h k; rw [h0] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ ((map_ne_zero _).2 (hc k)))
  · intro h0; funext k; rw [h k, h0]; simp

theorem det_fin_five' {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) :
    A.det = det5 (A 0 0) (A 0 1) (A 0 2) (A 0 3) (A 0 4) (A 1 0) (A 1 1) (A 1 2) (A 1 3) (A 1 4)
      (A 2 0) (A 2 1) (A 2 2) (A 2 3) (A 2 4) (A 3 0) (A 3 1) (A 3 2) (A 3 3) (A 3 4)
      (A 4 0) (A 4 1) (A 4 2) (A 4 3) (A 4 4) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, det_fin_four', Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.lt_def, det5]
  ring

/-- `n = 5`: `P_0` is the `z conj z` coefficient `k3`. -/
theorem crossVec_KP5_P0 {R : Type*} [CommRing R] (x y : Fin 5 → R) :
    crossVec (KP 5 x y) 0 = k3 (x 0) (x 1) (x 2) (x 3) (x 4) (y 0) (y 1) (y 2) (y 3) (y 4) := by
  simp only [crossVec, det_fin_five']
  simp [KP, k3, det5, det4, det3]
  ring

/-- `n = 4`: the `P_2` coordinate of the cross-product kernel vector is `mD`. -/
theorem crossVec_KP4_P2 {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    crossVec (KP 4 x y) 2 = mD (x 0) (x 1) (x 2) (x 3) (y 0) (y 1) (y 2) (y 3) := by
  simp only [crossVec, det_fin_four']
  simp [KP, Fin.succAbove, Fin.lt_def, mD, det4, det3]
  ring

/-- `n = 4`: the `Q_1` coordinate of the cross-product kernel vector is `-mN`. -/
theorem crossVec_KP4_Q1 {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    crossVec (KP 4 x y) 4 = -mN (x 0) (x 1) (x 2) (x 3) (y 0) (y 1) (y 2) (y 3) := by
  simp only [crossVec, det_fin_four']
  simp [KP, Fin.succAbove, Fin.lt_def, mN, det4, det3]
  ring


/-! ## Generic: kernel of a full-rank `n × (n+1)` matrix is the span of the cross vector -/

theorem ker_eq_span_crossVec {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) ℂ) (j : Fin (n + 1))
    (h : crossVec A j ≠ 0) :
    LinearMap.ker A.mulVecLin = Submodule.span ℂ {crossVec A} := by
  have hm : (A.submatrix id j.succAbove).det ≠ 0 := fun h0 => h (by simp [crossVec, h0])
  have h1 := finrank_ker_eq_one A (by simp) j.succAbove hm
  have hv : crossVec A ∈ LinearMap.ker A.mulVecLin := by simpa using mulVec_crossVec A
  have hne : crossVec A ≠ 0 := fun h0 => h (by rw [h0]; rfl)
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 hv
  · rw [h1, finrank_span_singleton hne]

/-- Every kernel vector of the (unscaled) Morley matrix `Kf` is a multiple of the polynomial
cross vector of `KP`, as soon as one coordinate of that cross vector is nonzero. -/
theorem Kf_ker_smul {n : ℕ} (c : Fin n → ℂ) (hc : ∀ k, c k ≠ 0) (j : Fin (n + 1))
    (hj : crossVec (KP n c (fun k => conj (c k))) j ≠ 0) {v : Fin (n + 1) → ℂ}
    (hv : Kf n (aOf c) (tOf c) *ᵥ v = 0) :
    ∃ r : ℂ, v = r • crossVec (KP n c (fun k => conj (c k))) := by
  have hv' : v ∈ LinearMap.ker (KP n c (fun k => conj (c k))).mulVecLin := by
    simpa using (KP_mulVec_eq_zero_iff c hc v).2 hv
  rw [ker_eq_span_crossVec _ j hj, Submodule.mem_span_singleton] at hv'
  obtain ⟨r, hr⟩ := hv'
  exact ⟨r, hr.symm⟩

theorem crossVec_KP_mem_ker {n : ℕ} (c : Fin n → ℂ) (hc : ∀ k, c k ≠ 0) :
    Kf n (aOf c) (tOf c) *ᵥ crossVec (KP n c (fun k => conj (c k))) = 0 :=
  (KP_mulVec_eq_zero_iff c hc _).1 (mulVec_crossVec _)

/-! ## 3a. `n = 4`: the level point `-Q₁ / P₂` is the Miquel point -/

/-- The even-level object read off a kernel vector `v` of `Kf (2m)`: `-Q_{m-1} / P_m`. -/
noncomputable def levelPoint (m : ℕ) (v : Fin (2 * m + 1) → ℂ) : ℂ :=
  -v ⟨2 * m, by omega⟩ / v ⟨m, by omega⟩

theorem c4_ne_zero {c : Fin 4 → ℂ} (h : GenPos4 (c 0) (c 1) (c 2) (c 3)) : ∀ k, c k ≠ 0 := by
  intro k; fin_cases k
  exacts [h.ab.left_ne_zero, h.ab.right_ne_zero, h.ac.right_ne_zero, h.ad.right_ne_zero]

/-- **Closed form at `n = 4` (equality of objects).** For four circles in general position,
every nonzero kernel vector `v` of the Morley matrix gives `-Q₁/P₂ = miquel`. -/
theorem levelPoint_four {c : Fin 4 → ℂ} (h : GenPos4 (c 0) (c 1) (c 2) (c 3))
    {v : Fin 5 → ℂ} (hv : Kf 4 (aOf c) (tOf c) *ᵥ v = 0) (hv0 : v ≠ 0) :
    levelPoint 2 v = miquel (c 0) (c 1) (c 2) (c 3) := by
  have hc := c4_ne_zero h
  have hD := h.mD_ne_zero
  have h2 : crossVec (KP 4 c (fun k => conj (c k))) 2 ≠ 0 := by rw [crossVec_KP4_P2]; exact hD
  obtain ⟨r, rfl⟩ := Kf_ker_smul c hc 2 h2 hv
  have hr : r ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
  have e2 := crossVec_KP4_P2 c (fun k => conj (c k))
  have e4 := crossVec_KP4_Q1 c (fun k => conj (c k))
  simp only [levelPoint, Pi.smul_apply, smul_eq_mul, miquel]
  rw [show (⟨2 * 2, by omega⟩ : Fin 5) = 4 from rfl, show (⟨2, by omega⟩ : Fin 5) = 2 from rfl,
    e2, e4]
  field_simp

/-- `n = 4`, existence + uniqueness: under `GenPos4` the kernel of the Morley matrix is a line. -/
theorem Kf_four_finrank {c : Fin 4 → ℂ} (h : GenPos4 (c 0) (c 1) (c 2) (c 3)) :
    finrank ℂ (LinearMap.ker (Kf 4 (aOf c) (tOf c)).mulVecLin) = 1 := by
  have hc := c4_ne_zero h
  have h2 : crossVec (KP 4 c (fun k => conj (c k))) 2 ≠ 0 := by
    rw [crossVec_KP4_P2]; exact h.mD_ne_zero
  have hne : crossVec (KP 4 c (fun k => conj (c k))) ≠ 0 := fun h0 => h2 (by rw [h0]; rfl)
  have hker : LinearMap.ker (Kf 4 (aOf c) (tOf c)).mulVecLin =
      Submodule.span ℂ {crossVec (KP 4 c (fun k => conj (c k)))} := by
    ext v
    rw [← ker_eq_span_crossVec _ 2 h2]
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact (KP_mulVec_eq_zero_iff c hc v).symm
  rw [hker, finrank_span_singleton hne]


/-! ## Plücker relation (three-term, 5×5) -/

/-- Laplace expansion of a `5 × 5` determinant along its last two columns `p`, `q`; the
`m i j` are the complementary `3 × 3` minors of the first three columns. -/

def lap2 {R : Type*} [CommRing R] (m₁₂ m₁₃ m₁₄ m₁₅ m₂₃ m₂₄ m₂₅ m₃₄ m₃₅ m₄₅ p₁ p₂ p₃ p₄ p₅ q₁ q₂ q₃ q₄ q₅ : R) : R :=
  (p₁ * q₂ - p₂ * q₁) * m₁₂ - (p₁ * q₃ - p₃ * q₁) * m₁₃ + (p₁ * q₄ - p₄ * q₁) * m₁₄ - (p₁ * q₅ - p₅ * q₁) * m₁₅ + (p₂ * q₃ - p₃ * q₂) * m₂₃ - (p₂ * q₄ - p₄ * q₂) * m₂₄ + (p₂ * q₅ - p₅ * q₂) * m₂₅ + (p₃ * q₄ - p₄ * q₃) * m₃₄ - (p₃ * q₅ - p₅ * q₃) * m₃₅ + (p₄ * q₅ - p₅ * q₄) * m₄₅

theorem det5_lap2 {R : Type*} [CommRing R] (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ a₅ b₅ c₅ p₁ p₂ p₃ p₄ p₅ q₁ q₂ q₃ q₄ q₅ : R) :
    det5 a₁ b₁ c₁ p₁ q₁ a₂ b₂ c₂ p₂ q₂ a₃ b₃ c₃ p₃ q₃ a₄ b₄ c₄ p₄ q₄ a₅ b₅ c₅ p₅ q₅ =
    lap2 (det3 a₃ b₃ c₃ a₄ b₄ c₄ a₅ b₅ c₅) (det3 a₂ b₂ c₂ a₄ b₄ c₄ a₅ b₅ c₅) (det3 a₂ b₂ c₂ a₃ b₃ c₃ a₅ b₅ c₅) (det3 a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄) (det3 a₁ b₁ c₁ a₄ b₄ c₄ a₅ b₅ c₅) (det3 a₁ b₁ c₁ a₃ b₃ c₃ a₅ b₅ c₅) (det3 a₁ b₁ c₁ a₃ b₃ c₃ a₄ b₄ c₄) (det3 a₁ b₁ c₁ a₂ b₂ c₂ a₅ b₅ c₅) (det3 a₁ b₁ c₁ a₂ b₂ c₂ a₄ b₄ c₄) (det3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃) p₁ p₂ p₃ p₄ p₅ q₁ q₂ q₃ q₄ q₅ := by
  unfold det5 det4 det3 lap2; ring

theorem plucker_abs {R : Type*} [CommRing R] (m₁₂ m₁₃ m₁₄ m₁₅ m₂₃ m₂₄ m₂₅ m₃₄ m₃₅ m₄₅ u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ v₄ v₅ w₁ w₂ w₃ w₄ w₅ s₁ s₂ s₃ s₄ s₅ : R)
    (h0 : m₁₂*m₃₄ - m₁₃*m₂₄ + m₁₄*m₂₃ = 0) (h1 : m₁₂*m₃₅ - m₁₃*m₂₅ + m₁₅*m₂₃ = 0) (h2 : m₁₂*m₄₅ - m₁₄*m₂₅ + m₁₅*m₂₄ = 0) (h3 : m₁₃*m₄₅ - m₁₄*m₃₅ + m₁₅*m₃₄ = 0) (h4 : m₂₃*m₄₅ - m₂₄*m₃₅ + m₂₅*m₃₄ = 0) :
    lap2 m₁₂ m₁₃ m₁₄ m₁₅ m₂₃ m₂₄ m₂₅ m₃₄ m₃₅ m₄₅ u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ v₄ v₅ * lap2 m₁₂ m₁₃ m₁₄ m₁₅ m₂₃ m₂₄ m₂₅ m₃₄ m₃₅ m₄₅ w₁ w₂ w₃ w₄ w₅ s₁ s₂ s₃ s₄ s₅ - lap2 m₁₂ m₁₃ m₁₄ m₁₅ m₂₃ m₂₄ m₂₅ m₃₄ m₃₅ m₄₅ u₁ u₂ u₃ u₄ u₅ w₁ w₂ w₃ w₄ w₅ * lap2 m₁₂ m₁₃ m₁₄ m₁₅ m₂₃ m₂₄ m₂₅ m₃₄ m₃₅ m₄₅ v₁ v₂ v₃ v₄ v₅ s₁ s₂ s₃ s₄ s₅ + lap2 m₁₂ m₁₃ m₁₄ m₁₅ m₂₃ m₂₄ m₂₅ m₃₄ m₃₅ m₄₅ u₁ u₂ u₃ u₄ u₅ s₁ s₂ s₃ s₄ s₅ * lap2 m₁₂ m₁₃ m₁₄ m₁₅ m₂₃ m₂₄ m₂₅ m₃₄ m₃₅ m₄₅ v₁ v₂ v₃ v₄ v₅ w₁ w₂ w₃ w₄ w₅ = 0 := by
  unfold lap2
  linear_combination (-s₁*u₂*v₃*w₄ + s₁*u₂*v₄*w₃ + s₁*u₃*v₂*w₄ - s₁*u₃*v₄*w₂ - s₁*u₄*v₂*w₃ + s₁*u₄*v₃*w₂ + s₂*u₁*v₃*w₄ - s₂*u₁*v₄*w₃ - s₂*u₃*v₁*w₄ + s₂*u₃*v₄*w₁ + s₂*u₄*v₁*w₃ - s₂*u₄*v₃*w₁ - s₃*u₁*v₂*w₄ + s₃*u₁*v₄*w₂ + s₃*u₂*v₁*w₄ - s₃*u₂*v₄*w₁ - s₃*u₄*v₁*w₂ + s₃*u₄*v₂*w₁ + s₄*u₁*v₂*w₃ - s₄*u₁*v₃*w₂ - s₄*u₂*v₁*w₃ + s₄*u₂*v₃*w₁ + s₄*u₃*v₁*w₂ - s₄*u₃*v₂*w₁) * h0 + (s₁*u₂*v₃*w₅ - s₁*u₂*v₅*w₃ - s₁*u₃*v₂*w₅ + s₁*u₃*v₅*w₂ + s₁*u₅*v₂*w₃ - s₁*u₅*v₃*w₂ - s₂*u₁*v₃*w₅ + s₂*u₁*v₅*w₃ + s₂*u₃*v₁*w₅ - s₂*u₃*v₅*w₁ - s₂*u₅*v₁*w₃ + s₂*u₅*v₃*w₁ + s₃*u₁*v₂*w₅ - s₃*u₁*v₅*w₂ - s₃*u₂*v₁*w₅ + s₃*u₂*v₅*w₁ + s₃*u₅*v₁*w₂ - s₃*u₅*v₂*w₁ - s₅*u₁*v₂*w₃ + s₅*u₁*v₃*w₂ + s₅*u₂*v₁*w₃ - s₅*u₂*v₃*w₁ - s₅*u₃*v₁*w₂ + s₅*u₃*v₂*w₁) * h1 + (-s₁*u₂*v₄*w₅ + s₁*u₂*v₅*w₄ + s₁*u₄*v₂*w₅ - s₁*u₄*v₅*w₂ - s₁*u₅*v₂*w₄ + s₁*u₅*v₄*w₂ + s₂*u₁*v₄*w₅ - s₂*u₁*v₅*w₄ - s₂*u₄*v₁*w₅ + s₂*u₄*v₅*w₁ + s₂*u₅*v₁*w₄ - s₂*u₅*v₄*w₁ - s₄*u₁*v₂*w₅ + s₄*u₁*v₅*w₂ + s₄*u₂*v₁*w₅ - s₄*u₂*v₅*w₁ - s₄*u₅*v₁*w₂ + s₄*u₅*v₂*w₁ + s₅*u₁*v₂*w₄ - s₅*u₁*v₄*w₂ - s₅*u₂*v₁*w₄ + s₅*u₂*v₄*w₁ + s₅*u₄*v₁*w₂ - s₅*u₄*v₂*w₁) * h2 + (s₁*u₃*v₄*w₅ - s₁*u₃*v₅*w₄ - s₁*u₄*v₃*w₅ + s₁*u₄*v₅*w₃ + s₁*u₅*v₃*w₄ - s₁*u₅*v₄*w₃ - s₃*u₁*v₄*w₅ + s₃*u₁*v₅*w₄ + s₃*u₄*v₁*w₅ - s₃*u₄*v₅*w₁ - s₃*u₅*v₁*w₄ + s₃*u₅*v₄*w₁ + s₄*u₁*v₃*w₅ - s₄*u₁*v₅*w₃ - s₄*u₃*v₁*w₅ + s₄*u₃*v₅*w₁ + s₄*u₅*v₁*w₃ - s₄*u₅*v₃*w₁ - s₅*u₁*v₃*w₄ + s₅*u₁*v₄*w₃ + s₅*u₃*v₁*w₄ - s₅*u₃*v₄*w₁ - s₅*u₄*v₁*w₃ + s₅*u₄*v₃*w₁) * h3 + (-s₂*u₃*v₄*w₅ + s₂*u₃*v₅*w₄ + s₂*u₄*v₃*w₅ - s₂*u₄*v₅*w₃ - s₂*u₅*v₃*w₄ + s₂*u₅*v₄*w₃ + s₃*u₂*v₄*w₅ - s₃*u₂*v₅*w₄ - s₃*u₄*v₂*w₅ + s₃*u₄*v₅*w₂ + s₃*u₅*v₂*w₄ - s₃*u₅*v₄*w₂ - s₄*u₂*v₃*w₅ + s₄*u₂*v₅*w₃ + s₄*u₃*v₂*w₅ - s₄*u₃*v₅*w₂ - s₄*u₅*v₂*w₃ + s₄*u₅*v₃*w₂ + s₅*u₂*v₃*w₄ - s₅*u₂*v₄*w₃ - s₅*u₃*v₂*w₄ + s₅*u₃*v₄*w₂ + s₅*u₄*v₂*w₃ - s₅*u₄*v₃*w₂) * h4

/-- Three-term Plücker relation for `5 × 5` determinants sharing three columns. -/
theorem plucker5 {R : Type*} [CommRing R] (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ a₅ b₅ c₅ u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ v₄ v₅ w₁ w₂ w₃ w₄ w₅ s₁ s₂ s₃ s₄ s₅ : R) :
    (det5 a₁ b₁ c₁ u₁ v₁ a₂ b₂ c₂ u₂ v₂ a₃ b₃ c₃ u₃ v₃ a₄ b₄ c₄ u₄ v₄ a₅ b₅ c₅ u₅ v₅) * (det5 a₁ b₁ c₁ w₁ s₁ a₂ b₂ c₂ w₂ s₂ a₃ b₃ c₃ w₃ s₃ a₄ b₄ c₄ w₄ s₄ a₅ b₅ c₅ w₅ s₅) - (det5 a₁ b₁ c₁ u₁ w₁ a₂ b₂ c₂ u₂ w₂ a₃ b₃ c₃ u₃ w₃ a₄ b₄ c₄ u₄ w₄ a₅ b₅ c₅ u₅ w₅) * (det5 a₁ b₁ c₁ v₁ s₁ a₂ b₂ c₂ v₂ s₂ a₃ b₃ c₃ v₃ s₃ a₄ b₄ c₄ v₄ s₄ a₅ b₅ c₅ v₅ s₅) + (det5 a₁ b₁ c₁ u₁ s₁ a₂ b₂ c₂ u₂ s₂ a₃ b₃ c₃ u₃ s₃ a₄ b₄ c₄ u₄ s₄ a₅ b₅ c₅ u₅ s₅) * (det5 a₁ b₁ c₁ v₁ w₁ a₂ b₂ c₂ v₂ w₂ a₃ b₃ c₃ v₃ w₃ a₄ b₄ c₄ v₄ w₄ a₅ b₅ c₅ v₅ w₅) = 0 := by
  simp only [det5_lap2]
  apply plucker_abs <;> (unfold det3; ring)

section Five
variable {R : Type*} [CommRing R]

/-- The determinant `det5 (xy, x²y, xy², y³, y²)` (the `Q₂` coordinate at `n = 5`). -/
def kA57 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) : R :=
  det5 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (y₁ ^ 3) (y₁ ^ 2)
    (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2) (y₂ ^ 3) (y₂ ^ 2)
    (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (y₃ ^ 3) (y₃ ^ 2)
    (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (y₄ ^ 3) (y₄ ^ 2)
    (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2) (y₅ ^ 3) (y₅ ^ 2)

/-- The determinant `det5 (xy, x²y, xy², x³, x²)`. -/
def kA46 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) : R :=
  det5 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₁ ^ 3) (x₁ ^ 2)
    (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2) (x₂ ^ 3) (x₂ ^ 2)
    (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (x₃ ^ 3) (x₃ ^ 2)
    (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (x₄ ^ 3) (x₄ ^ 2)
    (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2) (x₅ ^ 3) (x₅ ^ 2)

theorem map_kA57 {S : Type*} [CommRing S] (f : R →+* S) (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) :
    f (kA57 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅) =
      kA57 (f x₁) (f x₂) (f x₃) (f x₄) (f x₅) (f y₁) (f y₂) (f y₃) (f y₄) (f y₅) := by
  simp [kA57, map_det5]

theorem kA57_swap (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) :
    kA57 y₁ y₂ y₃ y₄ y₅ x₁ x₂ x₃ x₄ x₅ = -kA46 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ := by
  unfold kA57 kA46 det5 det4 det3; ring

/-- The Clifford-circle discriminant identity `k0 k3 - k1 k2 = A46 · A57` (Plücker). -/
theorem k0k3_sub_k1k2 (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) :
    k0 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ * k3 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ -
      k1 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ * k2 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ =
    kA46 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ * kA57 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ := by
  have h := plucker5 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2)
    (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2)
    (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2)
    (x₁ ^ 3) (x₂ ^ 3) (x₃ ^ 3) (x₄ ^ 3) (x₅ ^ 3) (y₁ ^ 3) (y₂ ^ 3) (y₃ ^ 3) (y₄ ^ 3) (y₅ ^ 3)
    (x₁ ^ 2) (x₂ ^ 2) (x₃ ^ 2) (x₄ ^ 2) (x₅ ^ 2) (y₁ ^ 2) (y₂ ^ 2) (y₃ ^ 2) (y₄ ^ 2) (y₅ ^ 2)
  have hk1 : det5 (x₁ * y₁) (x₁ ^ 2 * y₁) (x₁ * y₁ ^ 2) (y₁ ^ 3) (x₁ ^ 2)
      (x₂ * y₂) (x₂ ^ 2 * y₂) (x₂ * y₂ ^ 2) (y₂ ^ 3) (x₂ ^ 2)
      (x₃ * y₃) (x₃ ^ 2 * y₃) (x₃ * y₃ ^ 2) (y₃ ^ 3) (x₃ ^ 2)
      (x₄ * y₄) (x₄ ^ 2 * y₄) (x₄ * y₄ ^ 2) (y₄ ^ 3) (x₄ ^ 2)
      (x₅ * y₅) (x₅ ^ 2 * y₅) (x₅ * y₅ ^ 2) (y₅ ^ 3) (x₅ ^ 2) =
      -k1 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ := by
    unfold k1 det5 det4 det3; ring
  rw [hk1] at h
  unfold k0 k2 k3 kA46 kA57
  linear_combination h

theorem crossVec_KP5_Q0 (x y : Fin 5 → R) :
    crossVec (KP 5 x y) 3 = k1 (x 0) (x 1) (x 2) (x 3) (x 4) (y 0) (y 1) (y 2) (y 3) (y 4) := by
  simp only [crossVec, det_fin_five']
  simp [KP, Fin.succAbove, Fin.lt_def, k1, det5, det4, det3]
  ring

theorem crossVec_KP5_Q2 (x y : Fin 5 → R) :
    crossVec (KP 5 x y) 5 = kA57 (x 0) (x 1) (x 2) (x 3) (x 4) (y 0) (y 1) (y 2) (y 3) (y 4) := by
  simp only [crossVec, det_fin_five']
  simp [KP, Fin.succAbove, Fin.lt_def, kA57, det5, det4, det3]
  ring

end Five

/-! ## 3b. `n = 5`: the kernel circle is the Clifford circle -/

/-- The odd-level object read off a kernel vector `v` of `Kf n` (`n = 2m+1`; coordinates
`P₀ = v 0`, `Q₀ = v (m+1)`, `Q_m = v (2m+1)`): the generalized circle
`|P₀|² z z̄ - conj P₀ Q₀ z - P₀ conj Q₀ z̄ + |Q₀|² - |Q_m|² = 0`
(centre `conj Q₀ / conj P₀`, radius `|Q_m / P₀|`; invariant under `v ↦ r v`). -/
noncomputable def oddCircleEq (m : ℕ) (v : Fin (2 * m + 2) → ℂ) (z : ℂ) : ℂ :=
  conj (v 0) * v 0 * z * conj z - conj (v 0) * v ⟨m + 1, by omega⟩ * z -
    v 0 * conj (v ⟨m + 1, by omega⟩) * conj z +
    v ⟨m + 1, by omega⟩ * conj (v ⟨m + 1, by omega⟩) - v (Fin.last _) * conj (v (Fin.last _))

/-- The even-level object read off a kernel vector `v` of `Kf n` (`n = 2m`): `-Q_{m-1} / P_m`. -/
noncomputable def levelPointN (n : ℕ) (v : Fin (n + 1) → ℂ) : ℂ :=
  -v (Fin.last n) / v ⟨n / 2, by omega⟩

theorem levelPointN_four {c : Fin 4 → ℂ} (h : GenPos4 (c 0) (c 1) (c 2) (c 3))
    {v : Fin 5 → ℂ} (hv : Kf 4 (aOf c) (tOf c) *ᵥ v = 0) (hv0 : v ≠ 0) :
    levelPointN 4 v = miquel (c 0) (c 1) (c 2) (c 3) :=
  levelPoint_four h hv hv0

/-- The polynomial identity behind the `n = 5` closed form:
`oddCircleEq (cross vector) z = k3 · cliffordEq z`, with no hypothesis. -/
theorem oddCircleEq_five_cross (c : Fin 5 → ℂ) (z : ℂ) :
    oddCircleEq 2 (crossVec (KP 5 c (fun k => conj (c k)))) z =
      k3 (c 0) (c 1) (c 2) (c 3) (c 4) (conj (c 0)) (conj (c 1)) (conj (c 2)) (conj (c 3))
        (conj (c 4)) * cliffordEq (c 0) (c 1) (c 2) (c 3) (c 4) z := by
  have e3 : (⟨2 + 1, by omega⟩ : Fin 6) = 3 := rfl
  have e5 : (Fin.last (2 * 2 + 1) : Fin 6) = 5 := rfl
  simp only [oddCircleEq, e3, e5, crossVec_KP5_P0, crossVec_KP5_Q0, crossVec_KP5_Q2]
  have c3 : ∀ x₁ x₂ x₃ x₄ x₅ : ℂ,
      conj (k3 x₁ x₂ x₃ x₄ x₅ (conj x₁) (conj x₂) (conj x₃) (conj x₄) (conj x₅)) =
      k3 x₁ x₂ x₃ x₄ x₅ (conj x₁) (conj x₂) (conj x₃) (conj x₄) (conj x₅) := by
    intros; rw [map_k3]; simp only [starRingEnd_self_apply]; exact k3_swap _ _ _ _ _ _ _ _ _ _
  have c1 : ∀ x₁ x₂ x₃ x₄ x₅ : ℂ,
      conj (k1 x₁ x₂ x₃ x₄ x₅ (conj x₁) (conj x₂) (conj x₃) (conj x₄) (conj x₅)) =
      k2 x₁ x₂ x₃ x₄ x₅ (conj x₁) (conj x₂) (conj x₃) (conj x₄) (conj x₅) := by
    intros; rw [map_k1]; simp only [starRingEnd_self_apply]; rw [k2_swap]
  have cA : ∀ x₁ x₂ x₃ x₄ x₅ : ℂ,
      conj (kA57 x₁ x₂ x₃ x₄ x₅ (conj x₁) (conj x₂) (conj x₃) (conj x₄) (conj x₅)) =
      -kA46 x₁ x₂ x₃ x₄ x₅ (conj x₁) (conj x₂) (conj x₃) (conj x₄) (conj x₅) := by
    intros; rw [map_kA57]; simp only [starRingEnd_self_apply]; exact kA57_swap _ _ _ _ _ _ _ _ _ _
  rw [c3, c1, cA, cliffordEq, kK_expand]
  linear_combination -k0k3_sub_k1k2 (c 0) (c 1) (c 2) (c 3) (c 4) (conj (c 0)) (conj (c 1))
    (conj (c 2)) (conj (c 3)) (conj (c 4))

/-- **Closed form at `n = 5` (membership equivalence).** If the Clifford circle is
non-degenerate (`CliffordNondeg`, i.e. `P₀ = k3 ≠ 0`), every nonzero kernel vector `v` of the
Morley matrix defines the Clifford circle: `oddCircleEq 2 v z = 0 ↔ cliffordEq … z = 0`. -/
theorem oddCircle_five {c : Fin 5 → ℂ} (hc : ∀ k, c k ≠ 0)
    (hk : CliffordNondeg (c 0) (c 1) (c 2) (c 3) (c 4))
    {v : Fin 6 → ℂ} (hv : Kf 5 (aOf c) (tOf c) *ᵥ v = 0) (hv0 : v ≠ 0) (z : ℂ) :
    oddCircleEq 2 v z = 0 ↔ cliffordEq (c 0) (c 1) (c 2) (c 3) (c 4) z = 0 := by
  have h0 : crossVec (KP 5 c (fun k => conj (c k))) 0 ≠ 0 := by rw [crossVec_KP5_P0]; exact hk
  obtain ⟨r, rfl⟩ := Kf_ker_smul c hc 0 h0 hv
  have hr : r ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
  have hr' : conj r ≠ 0 := (map_ne_zero _).2 hr
  have hs : oddCircleEq 2 (r • crossVec (KP 5 c (fun k => conj (c k)))) z =
      r * conj r * oddCircleEq 2 (crossVec (KP 5 c (fun k => conj (c k)))) z := by
    simp only [oddCircleEq, Pi.smul_apply, smul_eq_mul, map_mul]; ring
  have hk' : k3 (c 0) (c 1) (c 2) (c 3) (c 4) (conj (c 0)) (conj (c 1)) (conj (c 2)) (conj (c 3))
      (conj (c 4)) ≠ 0 := hk
  rw [hs, oddCircleEq_five_cross]
  simp [hr, hk']

/-- In the degenerate case `k3 = 0` the cross-vector circle equation vanishes identically:
the kernel then carries the *line* `k0 - z k1 - z̄ k2 = 0` only through `k0`, which is not a
kernel coordinate. (So the kernel form needs `P₀ ≠ 0`.) -/
theorem oddCircleEq_five_degenerate (c : Fin 5 → ℂ)
    (hk : ¬ CliffordNondeg (c 0) (c 1) (c 2) (c 3) (c 4)) (z : ℂ) :
    oddCircleEq 2 (crossVec (KP 5 c (fun k => conj (c k)))) z = 0 := by
  rw [oddCircleEq_five_cross, not_not.1 hk, zero_mul]

/-- **Step `4 ⟹ 5` in kernel language.** Each of the five level-4 points (`miquel` of a
4-subfamily) lies on the kernel circle of the five circles. -/
theorem step_four_five {c : Fin 5 → ℂ} (h : GenPos5 (c 0) (c 1) (c 2) (c 3) (c 4))
    (hk : CliffordNondeg (c 0) (c 1) (c 2) (c 3) (c 4))
    {v : Fin 6 → ℂ} (hv : Kf 5 (aOf c) (tOf c) *ᵥ v = 0) (hv0 : v ≠ 0) :
    ∀ z ∈ ({miquel (c 0) (c 1) (c 2) (c 3), miquel (c 0) (c 1) (c 2) (c 4),
      miquel (c 0) (c 1) (c 3) (c 4), miquel (c 0) (c 2) (c 3) (c 4),
      miquel (c 1) (c 2) (c 3) (c 4)} : Set ℂ), oddCircleEq 2 v z = 0 := by
  have hc : ∀ k, c k ≠ 0 := by
    intro k; fin_cases k
    exacts [h.ab.left_ne_zero, h.ab.right_ne_zero, h.ac.right_ne_zero, h.ad.right_ne_zero,
      h.ae.right_ne_zero]
  intro z hz
  exact (oddCircle_five hc hk hv hv0 z).2 (clifford_points_on h z hz)

/-! ## 4. Step shape: bordering -/

/-- Even `n = 2m → 2m+1`: `Kf (2m+1)` is `Kf (2m)` bordered by one new row (circle `2m`) and
one new **last** column (`Q_m`). -/
theorem Kf_border_even (m : ℕ) (a t : Fin (2 * m + 1) → ℂ) :
    (Kf (2 * m + 1) a t).submatrix Fin.castSucc Fin.castSucc =
      Kf (2 * m) (a ∘ Fin.castSucc) (t ∘ Fin.castSucc) := by
  ext k j
  have e : (2 * m + 1) / 2 = m := by omega
  have e' : 2 * m / 2 = m := by omega
  simp only [Matrix.submatrix_apply, Kf, Fin.val_castSucc, Function.comp_apply, e, e']

/-- Odd `n = 2m+1 → 2m+2`: `Kf (2m+2)` is `Kf (2m+1)` bordered by one new row and one new
column `P_{m+1}`, inserted at position `m+1` (between the `P`- and `Q`-blocks). -/
theorem Kf_border_odd (m : ℕ) (a t : Fin (2 * m + 2) → ℂ) :
    (Kf (2 * m + 2) a t).submatrix Fin.castSucc (Fin.succAbove ⟨m + 1, by omega⟩) =
      Kf (2 * m + 1) (a ∘ Fin.castSucc) (t ∘ Fin.castSucc) := by
  ext k j
  have e : (2 * m + 2) / 2 = m + 1 := by omega
  have e' : (2 * m + 1) / 2 = m := by omega
  simp only [Matrix.submatrix_apply, Kf, Function.comp_apply, e, e']
  rcases Nat.lt_or_ge (j : ℕ) (m + 1) with hj | hj
  · have hs : ((Fin.succAbove ⟨m + 1, by omega⟩ j : Fin _) : ℕ) = j := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]; simp
    rw [hs, if_pos (by omega), if_pos (by omega)]
  · have hs : ((Fin.succAbove ⟨m + 1, by omega⟩ j : Fin _) : ℕ) = j + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; simp
    rw [hs, if_neg (by omega), if_neg (by omega)]
    congr 2; omega

/-- The odd-to-even step lemma that would give `C_{2m+1} ⟹ C_{2m+2}` in kernel language
(statement only; **not proved**, numerically true for `m = 2, 3`): the level point of
`2m+2` circles lies on the kernel circle of every `2m+1`-subfamily. -/
def StepEven (m : ℕ) : Prop :=
  ∀ c : Fin (2 * m + 2) → ℂ, (∀ k, c k ≠ 0) →
    crossVec (KP (2 * m + 2) c (fun k => conj (c k))) ⟨m + 1, by omega⟩ ≠ 0 →
    ∀ i : Fin (2 * m + 2),
      oddCircleEq m (crossVec (KP (2 * m + 1) (c ∘ i.succAbove)
          (fun k => conj ((c ∘ i.succAbove) k))))
        (levelPointN (2 * m + 2) (crossVec (KP (2 * m + 2) c (fun k => conj (c k))))) = 0

/-- The even-to-odd step lemma (`C_{2m} ⟹ C_{2m+1}`; statement only, **proved for `m = 2`**
in the form `step_four_five`): every level point of a `2m`-subfamily lies on the kernel
circle of the `2m+1` circles. -/
def StepOdd (m : ℕ) : Prop :=
  ∀ c : Fin (2 * m + 1) → ℂ, (∀ k, c k ≠ 0) →
    ∀ i : Fin (2 * m + 1),
      crossVec (KP (2 * m) (c ∘ i.succAbove) (fun k => conj ((c ∘ i.succAbove) k)))
          ⟨m, by omega⟩ ≠ 0 →
      oddCircleEq m (crossVec (KP (2 * m + 1) c (fun k => conj (c k))))
        (levelPointN (2 * m) (crossVec (KP (2 * m) (c ∘ i.succAbove)
          (fun k => conj ((c ∘ i.succAbove) k))))) = 0

end Clifford.MorleyKernel

/-! # Paper L / J5: `StepEven 2`

The file reproduces `scratch/MorleyKernel.lean` verbatim above (that scratch file has no
`.olean`, so it cannot be imported); everything below is new. -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section Rel
theorem rowRel1 {R : Type*} [CommRing R] (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 v0 v1 v2 v3 v4 v5 v6 : R)
    (h0 : y0^3*v0 - x0*y0^2*v1 + x0^2*y0*v2 - x0^3*v3 - y0^2*v4 + x0*y0*v5 - x0^2*v6 = 0)
    (h1 : y1^3*v0 - x1*y1^2*v1 + x1^2*y1*v2 - x1^3*v3 - y1^2*v4 + x1*y1*v5 - x1^2*v6 = 0)
    (h2 : y2^3*v0 - x2*y2^2*v1 + x2^2*y2*v2 - x2^3*v3 - y2^2*v4 + x2*y2*v5 - x2^2*v6 = 0)
    (h3 : y3^3*v0 - x3*y3^2*v1 + x3^2*y3*v2 - x3^3*v3 - y3^2*v4 + x3*y3*v5 - x3^2*v6 = 0)
    (h4 : y4^3*v0 - x4*y4^2*v1 + x4^2*y4*v2 - x4^3*v3 - y4^2*v4 + x4*y4*v5 - x4^2*v6 = 0) :
    -k0 x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 * v3 + kA57 x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 * v4 - k1 x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 * v6 = 0 := by
  unfold k0 k1 kA57
  linear_combination (norm := (simp only [det5, det4, det3]; ring1)) (det4 ((y1)^3) (-(x1)*(y1)^2) ((x1)^2*(y1)) ((x1)*(y1)) ((y2)^3) (-(x2)*(y2)^2) ((x2)^2*(y2)) ((x2)*(y2)) ((y3)^3) (-(x3)*(y3)^2) ((x3)^2*(y3)) ((x3)*(y3)) ((y4)^3) (-(x4)*(y4)^2) ((x4)^2*(y4)) ((x4)*(y4))) * h0 + -(det4 ((y0)^3) (-(x0)*(y0)^2) ((x0)^2*(y0)) ((x0)*(y0)) ((y2)^3) (-(x2)*(y2)^2) ((x2)^2*(y2)) ((x2)*(y2)) ((y3)^3) (-(x3)*(y3)^2) ((x3)^2*(y3)) ((x3)*(y3)) ((y4)^3) (-(x4)*(y4)^2) ((x4)^2*(y4)) ((x4)*(y4))) * h1 + (det4 ((y0)^3) (-(x0)*(y0)^2) ((x0)^2*(y0)) ((x0)*(y0)) ((y1)^3) (-(x1)*(y1)^2) ((x1)^2*(y1)) ((x1)*(y1)) ((y3)^3) (-(x3)*(y3)^2) ((x3)^2*(y3)) ((x3)*(y3)) ((y4)^3) (-(x4)*(y4)^2) ((x4)^2*(y4)) ((x4)*(y4))) * h2 + -(det4 ((y0)^3) (-(x0)*(y0)^2) ((x0)^2*(y0)) ((x0)*(y0)) ((y1)^3) (-(x1)*(y1)^2) ((x1)^2*(y1)) ((x1)*(y1)) ((y2)^3) (-(x2)*(y2)^2) ((x2)^2*(y2)) ((x2)*(y2)) ((y4)^3) (-(x4)*(y4)^2) ((x4)^2*(y4)) ((x4)*(y4))) * h3 + (det4 ((y0)^3) (-(x0)*(y0)^2) ((x0)^2*(y0)) ((x0)*(y0)) ((y1)^3) (-(x1)*(y1)^2) ((x1)^2*(y1)) ((x1)*(y1)) ((y2)^3) (-(x2)*(y2)^2) ((x2)^2*(y2)) ((x2)*(y2)) ((y3)^3) (-(x3)*(y3)^2) ((x3)^2*(y3)) ((x3)*(y3))) * h4

theorem rowRel2 {R : Type*} [CommRing R] (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 v0 v1 v2 v3 v4 v5 v6 : R)
    (h0 : y0^3*v0 - x0*y0^2*v1 + x0^2*y0*v2 - x0^3*v3 - y0^2*v4 + x0*y0*v5 - x0^2*v6 = 0)
    (h1 : y1^3*v0 - x1*y1^2*v1 + x1^2*y1*v2 - x1^3*v3 - y1^2*v4 + x1*y1*v5 - x1^2*v6 = 0)
    (h2 : y2^3*v0 - x2*y2^2*v1 + x2^2*y2*v2 - x2^3*v3 - y2^2*v4 + x2*y2*v5 - x2^2*v6 = 0)
    (h3 : y3^3*v0 - x3*y3^2*v1 + x3^2*y3*v2 - x3^3*v3 - y3^2*v4 + x3*y3*v5 - x3^2*v6 = 0)
    (h4 : y4^3*v0 - x4*y4^2*v1 + x4^2*y4*v2 - x4^3*v3 - y4^2*v4 + x4*y4*v5 - x4^2*v6 = 0) :
    -kA57 x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 * v0 + k2 x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 * v3 + k3 x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 * v6 = 0 := by
  unfold k2 k3 kA57
  linear_combination (norm := (simp only [det5, det4, det3]; ring1)) (det4 (-(x1)*(y1)^2) ((x1)^2*(y1)) (-(y1)^2) ((x1)*(y1)) (-(x2)*(y2)^2) ((x2)^2*(y2)) (-(y2)^2) ((x2)*(y2)) (-(x3)*(y3)^2) ((x3)^2*(y3)) (-(y3)^2) ((x3)*(y3)) (-(x4)*(y4)^2) ((x4)^2*(y4)) (-(y4)^2) ((x4)*(y4))) * h0 + -(det4 (-(x0)*(y0)^2) ((x0)^2*(y0)) (-(y0)^2) ((x0)*(y0)) (-(x2)*(y2)^2) ((x2)^2*(y2)) (-(y2)^2) ((x2)*(y2)) (-(x3)*(y3)^2) ((x3)^2*(y3)) (-(y3)^2) ((x3)*(y3)) (-(x4)*(y4)^2) ((x4)^2*(y4)) (-(y4)^2) ((x4)*(y4))) * h1 + (det4 (-(x0)*(y0)^2) ((x0)^2*(y0)) (-(y0)^2) ((x0)*(y0)) (-(x1)*(y1)^2) ((x1)^2*(y1)) (-(y1)^2) ((x1)*(y1)) (-(x3)*(y3)^2) ((x3)^2*(y3)) (-(y3)^2) ((x3)*(y3)) (-(x4)*(y4)^2) ((x4)^2*(y4)) (-(y4)^2) ((x4)*(y4))) * h2 + -(det4 (-(x0)*(y0)^2) ((x0)^2*(y0)) (-(y0)^2) ((x0)*(y0)) (-(x1)*(y1)^2) ((x1)^2*(y1)) (-(y1)^2) ((x1)*(y1)) (-(x2)*(y2)^2) ((x2)^2*(y2)) (-(y2)^2) ((x2)*(y2)) (-(x4)*(y4)^2) ((x4)^2*(y4)) (-(y4)^2) ((x4)*(y4))) * h3 + (det4 (-(x0)*(y0)^2) ((x0)^2*(y0)) (-(y0)^2) ((x0)*(y0)) (-(x1)*(y1)^2) ((x1)^2*(y1)) (-(y1)^2) ((x1)*(y1)) (-(x2)*(y2)^2) ((x2)^2*(y2)) (-(y2)^2) ((x2)*(y2)) (-(x3)*(y3)^2) ((x3)^2*(y3)) (-(y3)^2) ((x3)*(y3))) * h4

end Rel

/-- Row `k` of `KP 6 x y` applied to its own cross vector. -/
theorem KP6_row {R : Type*} [CommRing R] (x y : Fin 6 → R) (k : Fin 6) :
    y k ^ 3 * crossVec (KP 6 x y) 0 - x k * y k ^ 2 * crossVec (KP 6 x y) 1 +
      x k ^ 2 * y k * crossVec (KP 6 x y) 2 - x k ^ 3 * crossVec (KP 6 x y) 3 -
      y k ^ 2 * crossVec (KP 6 x y) 4 + x k * y k * crossVec (KP 6 x y) 5 -
      x k ^ 2 * crossVec (KP 6 x y) 6 = 0 := by
  have h := congrFun (mulVec_crossVec (KP 6 x y)) k
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.zero_apply] at h
  simp [KP, Fin.succ] at h
  linear_combination h

theorem det6_expand {R : Type*} [CommRing R] (A : Matrix (Fin 6) (Fin 6) R) :
    A.det = A 0 0 * (A.submatrix Fin.succ (Fin.succAbove 0)).det
      - A 0 1 * (A.submatrix Fin.succ (Fin.succAbove 1)).det
      + A 0 2 * (A.submatrix Fin.succ (Fin.succAbove 2)).det
      - A 0 3 * (A.submatrix Fin.succ (Fin.succAbove 3)).det
      + A 0 4 * (A.submatrix Fin.succ (Fin.succAbove 4)).det
      - A 0 5 * (A.submatrix Fin.succ (Fin.succAbove 5)).det := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_six]
  norm_num
  ring

/-- Swapping `x ↔ y` permutes the columns of `KP 6`: `P₃ ↔ P₀` up to sign. -/
theorem crossVec_KP6_swap3 {R : Type*} [CommRing R] (x y : Fin 6 → R) :
    crossVec (KP 6 y x) 3 = crossVec (KP 6 x y) 0 := by
  simp only [crossVec, det6_expand, det_fin_five']
  simp [KP, Fin.succAbove, Fin.lt_def, det5, det4, det3]
  ring

theorem crossVec_KP6_swap6 {R : Type*} [CommRing R] (x y : Fin 6 → R) :
    crossVec (KP 6 y x) 6 = -crossVec (KP 6 x y) 4 := by
  simp only [crossVec, det6_expand, det_fin_five']
  simp [KP, Fin.succAbove, Fin.lt_def, det5, det4, det3]
  ring

theorem conj_crossVec_KP6 (c : Fin 6 → ℂ) (j : Fin 7) :
    conj (crossVec (KP 6 c (fun k => conj (c k))) j) =
      crossVec (KP 6 (fun k => conj (c k)) c) j := by
  simp only [crossVec, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, KP, id]
  split_ifs <;> simp

/-- **`StepEven 2`.** For six circles through `M` with `P₃ ≠ 0`, the level-6 point `−Q₂/P₃`
lies on the kernel circle of every 5-subfamily. -/
theorem stepEven_two : StepEven 2 := by
  intro c hc h3 i
  set v := crossVec (KP 6 c (fun k => conj (c k))) with hv
  have e3 : (⟨2 + 1, by omega⟩ : Fin 6) = 3 := rfl
  have e5 : (Fin.last (2 * 2 + 1) : Fin 6) = 5 := rfl
  have hP3 : v 3 ≠ 0 := h3
  have hcv3 : conj (v 3) = v 0 := by
    rw [hv, conj_crossVec_KP6, crossVec_KP6_swap3]
  have hcv6 : conj (v 6) = -v 4 := by
    rw [hv, conj_crossVec_KP6, crossVec_KP6_swap6]
  have hP0 : v 0 ≠ 0 := by rw [← hcv3]; exact (map_ne_zero _).2 hP3
  have hz : levelPointN (2 * 2 + 2) v = -v 6 / v 3 := rfl
  have hzc : conj (-v 6 / v 3) = v 4 / v 0 := by
    rw [map_div₀, map_neg, hcv3, hcv6, neg_neg]
  rw [hz, oddCircleEq_five_cross, cliffordEq, kK_expand, hzc]
  have r : ∀ j : Fin 5, conj (c (i.succAbove j)) ^ 3 * v 0 - c (i.succAbove j) * conj (c (i.succAbove j)) ^ 2 * v 1 +
      c (i.succAbove j) ^ 2 * conj (c (i.succAbove j)) * v 2 - c (i.succAbove j) ^ 3 * v 3 -
      conj (c (i.succAbove j)) ^ 2 * v 4 + c (i.succAbove j) * conj (c (i.succAbove j)) * v 5 -
      c (i.succAbove j) ^ 2 * v 6 = 0 := fun j =>
    KP6_row c (fun k => conj (c k)) (i.succAbove j)
  have R1 := rowRel1 (c (i.succAbove 0)) (c (i.succAbove 1)) (c (i.succAbove 2)) (c (i.succAbove 3))
    (c (i.succAbove 4)) (conj (c (i.succAbove 0))) (conj (c (i.succAbove 1)))
    (conj (c (i.succAbove 2))) (conj (c (i.succAbove 3))) (conj (c (i.succAbove 4)))
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (r 0) (r 1) (r 2) (r 3) (r 4)
  have R2 := rowRel2 (c (i.succAbove 0)) (c (i.succAbove 1)) (c (i.succAbove 2)) (c (i.succAbove 3))
    (c (i.succAbove 4)) (conj (c (i.succAbove 0))) (conj (c (i.succAbove 1)))
    (conj (c (i.succAbove 2))) (conj (c (i.succAbove 3))) (conj (c (i.succAbove 4)))
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (r 0) (r 1) (r 2) (r 3) (r 4)
  simp only [Function.comp_apply]
  have key : k0 (c (i.succAbove 0)) (c (i.succAbove 1)) (c (i.succAbove 2)) (c (i.succAbove 3))
      (c (i.succAbove 4)) (conj (c (i.succAbove 0))) (conj (c (i.succAbove 1)))
      (conj (c (i.succAbove 2))) (conj (c (i.succAbove 3))) (conj (c (i.succAbove 4))) -
      -v 6 / v 3 * k1 (c (i.succAbove 0)) (c (i.succAbove 1)) (c (i.succAbove 2)) (c (i.succAbove 3))
      (c (i.succAbove 4)) (conj (c (i.succAbove 0))) (conj (c (i.succAbove 1)))
      (conj (c (i.succAbove 2))) (conj (c (i.succAbove 3))) (conj (c (i.succAbove 4))) -
      v 4 / v 0 * k2 (c (i.succAbove 0)) (c (i.succAbove 1)) (c (i.succAbove 2)) (c (i.succAbove 3))
      (c (i.succAbove 4)) (conj (c (i.succAbove 0))) (conj (c (i.succAbove 1)))
      (conj (c (i.succAbove 2))) (conj (c (i.succAbove 3))) (conj (c (i.succAbove 4))) +
      -v 6 / v 3 * (v 4 / v 0) * k3 (c (i.succAbove 0)) (c (i.succAbove 1)) (c (i.succAbove 2))
      (c (i.succAbove 3)) (c (i.succAbove 4)) (conj (c (i.succAbove 0))) (conj (c (i.succAbove 1)))
      (conj (c (i.succAbove 2))) (conj (c (i.succAbove 3))) (conj (c (i.succAbove 4))) = 0 := by
    field_simp
    linear_combination (-(v 0)) * R1 - v 4 * R2
  rw [key, mul_zero]

end Clifford.MorleyKernel

/-! # Paper L / J6: general-`m` conjugation relation for the cross vector

Everything below is new. The column-permutation lemma `crossVec_colPerm` is fully abstract:
if `B k j = d j * A k (σ j)` then `d j * crossVec B j = (∏ d) * sign σ * crossVec A (σ j)`
(proved through the bordered determinant `det [w; A] = ∑ w_l · crossVec A l`, never by
expanding a determinant). -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix Equiv

section ColPerm
variable {R : Type*} [CommRing R]

/-- The `(n+1) × (n+1)` matrix with first row `w` and remaining rows `A`. -/
def border {n : ℕ} (w : Fin (n + 1) → R) (A : Matrix (Fin n) (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i l => Fin.cases (w l) (fun r => A r l) i

theorem det_border {n : ℕ} (w : Fin (n + 1) → R) (A : Matrix (Fin n) (Fin (n + 1)) R) :
    (border w A).det = ∑ l, w l * crossVec A l := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (border w A).submatrix Fin.succ j.succAbove = A.submatrix id j.succAbove := by
    ext r s; simp only [border, Matrix.submatrix_apply, Matrix.of_apply, Fin.cases_succ, id]
  rw [this]; simp only [border, Matrix.of_apply, Fin.cases_zero, crossVec]; ring

theorem det_border_single {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) R) (j : Fin (n + 1))
    (r : R) : (border (Pi.single j r) A).det = r * crossVec A j := by
  rw [det_border]
  simp [Pi.single_apply]

/-- **Abstract column-permutation lemma.** If the columns of `B` are the columns of `A`
permuted by `σ` and rescaled by `d`, the cross vectors are related by `sign σ · ∏ d`. -/
theorem crossVec_colPerm {n : ℕ} (A B : Matrix (Fin n) (Fin (n + 1)) R)
    (σ : Perm (Fin (n + 1))) (d : Fin (n + 1) → R) (h : ∀ k j, B k j = d j * A k (σ j))
    (j : Fin (n + 1)) :
    d j * crossVec B j = (∏ l, d l) * ((Perm.sign σ : ℤ) : R) * crossVec A (σ j) := by
  set C := border (Pi.single (σ j) (1 : R)) A
  have hC : C.det = crossVec A (σ j) := by rw [det_border_single, one_mul]
  have hP : (C.submatrix id σ).det = ((Perm.sign σ : ℤ) : R) * C.det := det_permute' σ C
  have hM : (Matrix.of fun i l => d l * (C.submatrix id σ) i l).det =
      (∏ l, d l) * (C.submatrix id σ).det := det_mul_row d _
  have hE : (Matrix.of fun i l => d l * (C.submatrix id σ) i l) = border (Pi.single j (d j)) B := by
    ext i l
    refine Fin.cases ?_ (fun r => ?_) i
    · simp only [C, border, Matrix.of_apply, Matrix.submatrix_apply, id, Fin.cases_zero,
        Pi.single_apply, σ.injective.eq_iff]
      split_ifs with hl
      · subst hl; ring
      · ring
    · simp only [C, border, Matrix.of_apply, Matrix.submatrix_apply, id, Fin.cases_succ, h]
  rw [hE, det_border_single, hP, hC] at hM
  rw [hM]; ring

end ColPerm

/-! ## The sign of `Fin.revPerm` (recursion) -/

theorem sign_revPerm_succ (k : ℕ) :
    Perm.sign (Fin.revPerm : Perm (Fin (k + 1))) = (-1) ^ k * Perm.sign (Fin.revPerm : Perm (Fin k)) := by
  have h : finRotate (k + 1) * Fin.revPerm = Perm.decomposeFin.symm (0, Fin.revPerm) := by
    ext x
    refine Fin.cases ?_ (fun i => ?_) x
    · simp
    · rw [Perm.decomposeFin_symm_apply_succ, swap_self, Equiv.refl_apply, Perm.mul_apply,
        Fin.revPerm_apply, Fin.revPerm_apply, coe_finRotate]
      simp only [Fin.val_succ, Fin.val_rev]
      split_ifs with hl
      · exfalso; have := congrArg Fin.val hl; simp at this; omega
      · simp
  have h2 := congrArg Perm.sign h
  rw [Perm.sign_mul, sign_finRotate, Perm.decomposeFin.symm_sign, if_pos rfl, one_mul] at h2
  have e : ((-1 : ℤˣ) ^ (k.succ - 1)) = (-1) ^ k := by simp
  rw [e] at h2
  rw [← h2, ← mul_assoc, Int.units_mul_self, one_mul]

/-! ## The block-reversal permutation of `KP (2m+2)` -/

/-- `Fin (m+2) ⊕ Fin (m+1)` (the `P`- and `Q`-blocks) as the columns of `KP (2m+2)`. -/
def blockEquiv (m : ℕ) : Fin (m + 2) ⊕ Fin (m + 1) ≃ Fin (2 * m + 2 + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- Reverse the columns within each block: `P_j ↔ P_{m+1-j}`, `Q_i ↔ Q_{m-i}`. -/
def blockRev (m : ℕ) : Perm (Fin (2 * m + 2 + 1)) :=
  (blockEquiv m).permCongr (Equiv.sumCongr Fin.revPerm Fin.revPerm)

theorem blockEquiv_inl (m : ℕ) (a : Fin (m + 2)) : ((blockEquiv m (Sum.inl a)) : ℕ) = a := by
  simp [blockEquiv]

theorem blockEquiv_inr (m : ℕ) (b : Fin (m + 1)) :
    ((blockEquiv m (Sum.inr b)) : ℕ) = m + 2 + b := by
  simp [blockEquiv]

theorem blockRev_blockEquiv (m : ℕ) (s : Fin (m + 2) ⊕ Fin (m + 1)) :
    blockRev m (blockEquiv m s) = blockEquiv m (Equiv.sumCongr Fin.revPerm Fin.revPerm s) := by
  simp [blockRev, Equiv.permCongr_apply]

theorem blockRev_val (m : ℕ) (j : Fin (2 * m + 2 + 1)) :
    ((blockRev m j : Fin _) : ℕ) = if (j : ℕ) ≤ m + 1 then m + 1 - j else 3 * m + 4 - j := by
  obtain ⟨s, rfl⟩ := (blockEquiv m).surjective j
  rw [blockRev_blockEquiv]
  rcases s with a | b
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, blockEquiv_inl, Fin.revPerm_apply, Fin.val_rev]
    rw [if_pos (by omega)]; omega
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, blockEquiv_inr, Fin.revPerm_apply, Fin.val_rev]
    rw [if_neg (by omega)]; omega

theorem sign_blockRev (m : ℕ) : Perm.sign (blockRev m) = (-1) ^ (m + 1) := by
  rw [blockRev, Perm.sign_permCongr, Perm.sign_sumCongr, sign_revPerm_succ (m + 1), mul_assoc,
    Int.units_mul_self, mul_one]

/-- The column scalars: `(-1)^(m+1)` on the `P`-block, `(-1)^m` on the `Q`-block. -/
def blockSign {R : Type*} [CommRing R] (m : ℕ) (j : Fin (2 * m + 2 + 1)) : R :=
  if (j : ℕ) ≤ m + 1 then (-1) ^ (m + 1) else (-1) ^ m

theorem prod_blockSign {R : Type*} [CommRing R] (m : ℕ) :
    ∏ l, (blockSign m l : R) = 1 := by
  rw [← (blockEquiv m).prod_comp, Fintype.prod_sum_type]
  simp only [blockSign, blockEquiv_inl, blockEquiv_inr]
  have h1 : ∀ a : Fin (m + 2), ((a : ℕ) ≤ m + 1) := fun a => by omega
  have h2 : ∀ b : Fin (m + 1), ¬ (m + 2 + (b : ℕ) ≤ m + 1) := fun b => by omega
  simp only [h1, h2, if_true, if_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_mul, ← pow_add]
  exact Even.neg_one_pow ⟨(m + 1) ^ 2, by ring⟩

theorem aux_pow_swap {R : Type*} [CommRing R] (a b : ℕ) (x y : R) :
    (-y) ^ a * x ^ b = (-1) ^ (a + b) * ((-x) ^ b * y ^ a) := by
  have hu : ((-1 : R) ^ b) * (-1) ^ b = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨b, rfl⟩
  rw [neg_pow, neg_pow, pow_add]
  linear_combination (-((-1 : R) ^ a * y ^ a * x ^ b)) * hu

/-- **Swapping `x ↔ y` in `KP (2m+2)` = block reversal of the columns, rescaled.** -/
theorem KP_swap_entry {R : Type*} [CommRing R] (m : ℕ) (x y : Fin (2 * m + 2) → R)
    (k : Fin (2 * m + 2)) (j : Fin (2 * m + 2 + 1)) :
    KP (2 * m + 2) y x k j = blockSign m j * KP (2 * m + 2) x y k (blockRev m j) := by
  have e1 : (2 * m + 2) / 2 = m + 1 := by omega
  have e2 : 2 * m + 2 - (m + 1) = m + 1 := by omega
  have hv := blockRev_val m j
  simp only [KP, blockSign, e1, e2]
  by_cases hj : (j : ℕ) ≤ m + 1
  · rw [if_pos hj] at hv
    rw [if_pos hj, if_pos hj, if_pos (by omega), hv]
    obtain ⟨b, hb⟩ : ∃ b, m + 1 = j + b := ⟨m + 1 - j, by omega⟩
    rw [show m + 1 - (j : ℕ) = b by omega, show m + 1 - b = (j : ℕ) by omega, hb,
      aux_pow_swap]
  · rw [if_neg hj] at hv
    rw [if_neg hj, if_neg hj, if_neg (by omega), hv]
    obtain ⟨c, hc⟩ : ∃ c, m = ((j : ℕ) - (m + 1 + 1)) + c := ⟨m - ((j : ℕ) - (m + 1 + 1)), by omega⟩
    rw [show m + 1 - 1 - ((j : ℕ) - (m + 1 + 1)) = c by omega,
      show 3 * m + 4 - (j : ℕ) - (m + 1 + 1) = c by omega,
      show m + 1 - 1 - c = (j : ℕ) - (m + 1 + 1) by omega]
    rw [aux_pow_swap, show (j : ℕ) - (m + 1 + 1) + c = m by omega]; ring

/-- The swap relation, general `m`: `crossVec (KP y x) (m+1) = crossVec (KP x y) 0`. -/
theorem crossVec_KP_swap_P {R : Type*} [CommRing R] (m : ℕ) (x y : Fin (2 * m + 2) → R) :
    crossVec (KP (2 * m + 2) y x) ⟨m + 1, by omega⟩ = crossVec (KP (2 * m + 2) x y) 0 := by
  have H := crossVec_colPerm (KP (2 * m + 2) x y) (KP (2 * m + 2) y x) (blockRev m)
    (blockSign m) (KP_swap_entry m x y) ⟨m + 1, by omega⟩
  have hσ : blockRev m ⟨m + 1, by omega⟩ = 0 := by
    ext; rw [blockRev_val]; simp
  rw [prod_blockSign, sign_blockRev, hσ, one_mul] at H
  simp only [blockSign, le_refl, if_true] at H
  push_cast at H
  have hu : ((-1 : R) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m + 1, rfl⟩
  linear_combination ((-1 : R) ^ (m + 1)) * H -
    (crossVec (KP (2 * m + 2) y x) ⟨m + 1, by omega⟩ - crossVec (KP (2 * m + 2) x y) 0) * hu

/-- The swap relation, general `m`: `crossVec (KP y x) Q_m = - crossVec (KP x y) Q_0`. -/
theorem crossVec_KP_swap_Q {R : Type*} [CommRing R] (m : ℕ) (x y : Fin (2 * m + 2) → R) :
    crossVec (KP (2 * m + 2) y x) (Fin.last _) = -crossVec (KP (2 * m + 2) x y) ⟨m + 2, by omega⟩ := by
  have H := crossVec_colPerm (KP (2 * m + 2) x y) (KP (2 * m + 2) y x) (blockRev m)
    (blockSign m) (KP_swap_entry m x y) (Fin.last _)
  have hσ : blockRev m (Fin.last _) = ⟨m + 2, by omega⟩ := by
    ext; rw [blockRev_val, Fin.val_last, if_neg (by omega)]
    show 3 * m + 4 - (2 * m + 2) = m + 2; omega
  rw [prod_blockSign, sign_blockRev, hσ, one_mul] at H
  have hn : ¬ ((Fin.last (2 * m + 2) : Fin _) : ℕ) ≤ m + 1 := by rw [Fin.val_last]; omega
  simp only [blockSign, hn, if_false] at H
  push_cast at H
  have hu : ((-1 : R) ^ m) * (-1) ^ m = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
  rw [pow_succ] at H
  linear_combination ((-1 : R) ^ m) * H -
    (crossVec (KP (2 * m + 2) y x) (Fin.last _) + crossVec (KP (2 * m + 2) x y) ⟨m + 2, by omega⟩) * hu

/-- Complex conjugation of the polynomial cross vector = the cross vector with `x ↔ y`
(all `n`; generalizes `conj_crossVec_KP6`). -/
theorem conj_crossVec_KP (n : ℕ) (c : Fin n → ℂ) (j : Fin (n + 1)) :
    conj (crossVec (KP n c (fun k => conj (c k))) j) =
      crossVec (KP n (fun k => conj (c k)) c) j := by
  simp only [crossVec, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, KP, id]
  split_ifs <;> simp

/-- **Target 1 (general `m`).** `conj P_{m+1} = P₀`. -/
theorem conj_crossVec_even (m : ℕ) (c : Fin (2 * m + 2) → ℂ) :
    conj (crossVec (KP (2 * m + 2) c (fun k => conj (c k))) ⟨m + 1, by omega⟩)
      = crossVec (KP (2 * m + 2) c (fun k => conj (c k))) 0 := by
  rw [conj_crossVec_KP, crossVec_KP_swap_P]

/-- **Target 1 (general `m`), `Q`-part.** `conj Q_m = -Q₀`. -/
theorem conj_crossVec_even_Q (m : ℕ) (c : Fin (2 * m + 2) → ℂ) :
    conj (crossVec (KP (2 * m + 2) c (fun k => conj (c k))) (Fin.last _))
      = -crossVec (KP (2 * m + 2) c (fun k => conj (c k))) ⟨m + 2, by omega⟩ := by
  rw [conj_crossVec_KP, crossVec_KP_swap_Q]

theorem crossVec_even_P0_ne_zero (m : ℕ) (c : Fin (2 * m + 2) → ℂ)
    (h : crossVec (KP (2 * m + 2) c (fun k => conj (c k))) ⟨m + 1, by omega⟩ ≠ 0) :
    crossVec (KP (2 * m + 2) c (fun k => conj (c k))) 0 ≠ 0 := by
  rw [← conj_crossVec_even]; exact (map_ne_zero _).2 h

/-- The level point's conjugate, general `m`: `conj (-Q_m / P_{m+1}) = Q₀ / P₀`. -/
theorem conj_levelPointN_even (m : ℕ) (c : Fin (2 * m + 2) → ℂ) :
    conj (levelPointN (2 * m + 2) (crossVec (KP (2 * m + 2) c (fun k => conj (c k))))) =
      crossVec (KP (2 * m + 2) c (fun k => conj (c k))) ⟨m + 2, by omega⟩ /
        crossVec (KP (2 * m + 2) c (fun k => conj (c k))) 0 := by
  have e : (⟨(2 * m + 2) / 2, by omega⟩ : Fin (2 * m + 2 + 1)) = ⟨m + 1, by omega⟩ := by
    ext; exact (by omega : (2 * m + 2) / 2 = m + 1)
  rw [levelPointN, e, map_div₀, map_neg, conj_crossVec_even_Q, conj_crossVec_even, neg_neg]

/-! ### Instances `m = 2` (reproduces `conj_crossVec_KP6`/`crossVec_KP6_swap*`) and `m = 3` -/

theorem conj_crossVec_KP6_P (c : Fin 6 → ℂ) :
    conj (crossVec (KP 6 c (fun k => conj (c k))) 3) = crossVec (KP 6 c (fun k => conj (c k))) 0 :=
  conj_crossVec_even 2 c

theorem conj_crossVec_KP6_Q (c : Fin 6 → ℂ) :
    conj (crossVec (KP 6 c (fun k => conj (c k))) 6) = -crossVec (KP 6 c (fun k => conj (c k))) 4 :=
  conj_crossVec_even_Q 2 c

theorem conj_crossVec_KP8_P (c : Fin 8 → ℂ) :
    conj (crossVec (KP 8 c (fun k => conj (c k))) 4) = crossVec (KP 8 c (fun k => conj (c k))) 0 :=
  conj_crossVec_even 3 c

theorem conj_crossVec_KP8_Q (c : Fin 8 → ℂ) :
    conj (crossVec (KP 8 c (fun k => conj (c k))) 8) = -crossVec (KP 8 c (fun k => conj (c k))) 5 :=
  conj_crossVec_even_Q 3 c

/-- Consistency with the J5 brute-force lemma (now a corollary of the abstract one). -/
example {R : Type*} [CommRing R] (x y : Fin 6 → R) :
    crossVec (KP 6 y x) 3 = crossVec (KP 6 x y) 0 := crossVec_KP_swap_P 2 x y

end Clifford.MorleyKernel

/-! # Paper L / J6, target 2: `StepOdd 2` (variant with one extra `triP` hypothesis) -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- The level point of four circles, read off the polynomial cross vector, is their Miquel
point as soon as `P₂ = mD ≠ 0` (no `GenPos4` needed). -/
theorem levelPointN_four_cross (d : Fin 4 → ℂ)
    (h : crossVec (KP 4 d (fun k => conj (d k))) ⟨2, by omega⟩ ≠ 0) :
    levelPointN 4 (crossVec (KP 4 d (fun k => conj (d k)))) = miquel (d 0) (d 1) (d 2) (d 3) := by
  have e2 : (⟨4 / 2, by omega⟩ : Fin 5) = 2 := rfl
  have e4 : (Fin.last 4 : Fin 5) = 4 := rfl
  have h2 : crossVec (KP 4 d (fun k => conj (d k))) 2 ≠ 0 := h
  rw [crossVec_KP4_P2] at h2
  rw [levelPointN, e2, e4, crossVec_KP4_P2, crossVec_KP4_Q1, miquel, neg_neg]

/-- **`StepOdd 2`, variant.** Identical to `StepOdd 2` except for the extra hypothesis that the
first three centres of the removed-`i` subfamily are not collinear (`triP ≠ 0`), which is what
`cliffordEq_miquel` (Desnanot–Jacobi) needs. -/
theorem stepOdd_two_triP (c : Fin 5 → ℂ) (hc : ∀ k, c k ≠ 0) (i : Fin 5)
    (ht : triP (c (i.succAbove 0)) (c (i.succAbove 1)) (c (i.succAbove 2))
      (conj (c (i.succAbove 0))) (conj (c (i.succAbove 1))) (conj (c (i.succAbove 2))) ≠ 0)
    (hP : crossVec (KP 4 (c ∘ i.succAbove) (fun k => conj ((c ∘ i.succAbove) k)))
      ⟨2, by omega⟩ ≠ 0) :
    oddCircleEq 2 (crossVec (KP 5 c (fun k => conj (c k))))
      (levelPointN 4 (crossVec (KP 4 (c ∘ i.succAbove)
        (fun k => conj ((c ∘ i.succAbove) k))))) = 0 := by
  rw [levelPointN_four_cross _ hP, oddCircleEq_five_cross]
  have hD : mD (c (i.succAbove 0)) (c (i.succAbove 1)) (c (i.succAbove 2)) (c (i.succAbove 3))
      (conj (c (i.succAbove 0))) (conj (c (i.succAbove 1))) (conj (c (i.succAbove 2)))
      (conj (c (i.succAbove 3))) ≠ 0 := by
    have h2 : crossVec (KP 4 (c ∘ i.succAbove) (fun k => conj ((c ∘ i.succAbove) k))) 2 ≠ 0 := hP
    rwa [crossVec_KP4_P2] at h2
  have H := cliffordEq_miquel (e := c i) (hc _) (hc _) (hc _) ht hD
  simp only [Function.comp_apply]
  refine mul_eq_zero_of_right _ ?_
  fin_cases i
  · rw [cliffordEq, kK_p23451] at H; exact H
  · rw [cliffordEq, kK_p13452, neg_eq_zero] at H; exact H
  · rw [cliffordEq, kK_p12453] at H; exact H
  · rw [cliffordEq, kK_p12354, neg_eq_zero] at H; exact H
  · exact H

end Clifford.MorleyKernel

/-! # Paper L / J7: general Cramer row relations for the subfamily rows

Everything below is new. The prefix above is `scratch/GeneralStep.lean` verbatim. -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section Cramer
variable {R : Type*} [CommRing R]

/-- Column-bordered square matrix: first column `u`, remaining columns the columns `g e` of `M`. -/
def colBorder {n p : ℕ} (M : Matrix (Fin (n + 1)) (Fin p) R) (g : Fin n → Fin p)
    (u : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun r l => Fin.cases (u r) (fun e => M r (g e)) l

/-- The selected columns of `M`, transposed (an `n × (n+1)` matrix). -/
def selCols {n p : ℕ} (M : Matrix (Fin (n + 1)) (Fin p) R) (g : Fin n → Fin p) :
    Matrix (Fin n) (Fin (n + 1)) R :=
  Matrix.of fun e r => M r (g e)

theorem colBorder_transpose {n p : ℕ} (M : Matrix (Fin (n + 1)) (Fin p) R) (g : Fin n → Fin p)
    (u : Fin (n + 1) → R) : (colBorder M g u)ᵀ = border u (selCols M g) := by
  ext a b; refine Fin.cases ?_ (fun e => ?_) a <;> rfl

/-- The column-bordered determinant is a `border` determinant (via `det_border`). -/
theorem det_colBorder {n p : ℕ} (M : Matrix (Fin (n + 1)) (Fin p) R) (g : Fin n → Fin p)
    (u : Fin (n + 1) → R) : (colBorder M g u).det = ∑ r, u r * crossVec (selCols M g) r := by
  rw [← det_transpose, colBorder_transpose, det_border]

/-- Cramer coefficient of column `k`: the bordered determinant `det [M_k | M_g]`. -/
def cramerCoef {n p : ℕ} (M : Matrix (Fin (n + 1)) (Fin p) R) (g : Fin n → Fin p) (k : Fin p) : R :=
  (colBorder M g (fun r => M r k)).det

theorem cramerCoef_self {n p : ℕ} (M : Matrix (Fin (n + 1)) (Fin p) R) (g : Fin n → Fin p)
    (e : Fin n) : cramerCoef M g (g e) = 0 := by
  unfold cramerCoef
  refine Matrix.det_zero_of_column_eq (i := 0) (j := e.succ) (Fin.succ_ne_zero e).symm ?_
  intro r; simp [colBorder]

/-- **General Cramer relation.** If `M v = 0` then `∑ₖ v k · det [M_k | M_g] = 0`. -/
theorem cramer_sum {n p : ℕ} (M : Matrix (Fin (n + 1)) (Fin p) R) (g : Fin n → Fin p)
    (v : Fin p → R) (hv : M *ᵥ v = 0) : ∑ k, v k * cramerCoef M g k = 0 := by
  simp only [cramerCoef, det_colBorder, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ r, ∑ k, M r k * v k = 0 := fun r => by
    have := congrFun hv r; simpa [mulVec, dotProduct] using this
  calc ∑ r, ∑ k, v k * (M r k * crossVec (selCols M g) r)
      = ∑ r, (∑ k, M r k * v k) * crossVec (selCols M g) r := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ = 0 := by simp [h]

/-- **Three-term Cramer relation.** All columns other than `a, b, c` are among the `g e`. -/
theorem cramer_three {n p : ℕ} (M : Matrix (Fin (n + 1)) (Fin p) R) (g : Fin n → Fin p)
    (v : Fin p → R) (hv : M *ᵥ v = 0) (a b c : Fin p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hg : ∀ k, k ≠ a → k ≠ b → k ≠ c → ∃ e, g e = k) :
    v a * cramerCoef M g a + v b * cramerCoef M g b + v c * cramerCoef M g c = 0 := by
  have h := cramer_sum M g v hv
  rw [← Finset.sum_subset (Finset.subset_univ {a, b, c})] at h
  · rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton] at h
    linear_combination h
  · intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨e, rfl⟩ := hg k hk.1 hk.2.1 hk.2.2
    rw [cramerCoef_self, mul_zero]

end Cramer

section SubRows
variable {R : Type*} [CommRing R]

/-- The `2m+1` rows of the parent matrix `KP (2m+2)` belonging to the subfamily `c ∘ i.succAbove`. -/
def subRows (m : ℕ) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 3)) R :=
  (KP (2 * m + 2) x y).submatrix i.succAbove id

theorem subRows_mulVec (m : ℕ) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    subRows m x y i *ᵥ crossVec (KP (2 * m + 2) x y) = 0 := by
  funext r
  have := congrFun (mulVec_crossVec (KP (2 * m + 2) x y)) (i.succAbove r)
  simpa [subRows, mulVec, dotProduct] using this

/-- **Column identification.** The subfamily matrix is the parent matrix with row `i` and column
`P_{m+1}` removed. -/
theorem KP_sub_eq (m : ℕ) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    KP (2 * m + 1) (x ∘ i.succAbove) (y ∘ i.succAbove) =
      (subRows m x y i).submatrix id (Fin.succAbove ⟨m + 1, by omega⟩) := by
  ext k j
  have e : (2 * m + 2) / 2 = m + 1 := by omega
  have e' : (2 * m + 1) / 2 = m := by omega
  simp only [subRows, Matrix.submatrix_apply, KP, Function.comp_apply, e, e', id]
  rcases Nat.lt_or_ge (j : ℕ) (m + 1) with hj | hj
  · have hs : ((Fin.succAbove ⟨m + 1, by omega⟩ j : Fin _) : ℕ) = j := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]; simp
    simp only [hs]
    split_ifs <;> first | (exfalso; omega) | (congr 2 <;> omega) | (congr 3 <;> omega)
  · have hs : ((Fin.succAbove ⟨m + 1, by omega⟩ j : Fin _) : ℕ) = j + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; simp
    simp only [hs]
    split_ifs <;> first | (exfalso; omega) | (congr 2 <;> omega) | (congr 3 <;> omega)

/-- Eliminated columns for relation 1: `P₀ … P_m, Q₁ … Q_{m-1}` (kept: `P_{m+1}, Q₀, Q_m`). -/
def elim1 (m : ℕ) : Fin (2 * m) → Fin (2 * m + 3) :=
  fun e => if (e : ℕ) ≤ m then ⟨e, by omega⟩ else ⟨e + 2, by omega⟩

/-- Eliminated columns for relation 2: `P₁ … P_m, Q₀ … Q_{m-1}` (kept: `P₀, P_{m+1}, Q_m`). -/
def elim2 (m : ℕ) : Fin (2 * m) → Fin (2 * m + 3) :=
  fun e => if (e : ℕ) < m then ⟨e + 1, by omega⟩ else ⟨e + 2, by omega⟩

/-- **General row relation 1** (`m = 2`: `rowRel1`). -/
theorem rowRelGen1 (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    crossVec (KP (2 * m + 2) x y) ⟨m + 1, by omega⟩ * cramerCoef (subRows m x y i) (elim1 m) ⟨m + 1, by omega⟩ +
    crossVec (KP (2 * m + 2) x y) ⟨m + 2, by omega⟩ * cramerCoef (subRows m x y i) (elim1 m) ⟨m + 2, by omega⟩ +
    crossVec (KP (2 * m + 2) x y) (Fin.last _) * cramerCoef (subRows m x y i) (elim1 m) (Fin.last _) = 0 := by
  refine cramer_three _ _ _ (subRows_mulVec m x y i) _ _ _ ?_ ?_ ?_ ?_
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk]; omega
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk]; omega
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk]; omega
  · intro k ha hb hc
    simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_mk] at ha hb hc
    by_cases hk : (k : ℕ) ≤ m
    · exact ⟨⟨k, by omega⟩, by ext; simp only [elim1]; split_ifs <;> (try simp only [Fin.val_mk]) <;> omega⟩
    · exact ⟨⟨k - 2, by omega⟩, by ext; simp only [elim1]; split_ifs <;> (try simp only [Fin.val_mk]) <;> omega⟩

/-- **General row relation 2** (`m = 2`: `rowRel2`). -/
theorem rowRelGen2 (m : ℕ) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    crossVec (KP (2 * m + 2) x y) 0 * cramerCoef (subRows m x y i) (elim2 m) 0 +
    crossVec (KP (2 * m + 2) x y) ⟨m + 1, by omega⟩ * cramerCoef (subRows m x y i) (elim2 m) ⟨m + 1, by omega⟩ +
    crossVec (KP (2 * m + 2) x y) (Fin.last _) * cramerCoef (subRows m x y i) (elim2 m) (Fin.last _) = 0 := by
  refine cramer_three _ _ _ (subRows_mulVec m x y i) _ _ _ ?_ ?_ ?_ ?_
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk]; omega
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk]; omega
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk]; omega
  · intro k ha hb hc
    simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk] at ha hb hc
    by_cases hk : (k : ℕ) ≤ m
    · exact ⟨⟨k - 1, by omega⟩, by ext; simp only [elim2]; split_ifs <;> (try simp only [Fin.val_mk]) <;> omega⟩
    · exact ⟨⟨k - 2, by omega⟩, by ext; simp only [elim2]; split_ifs <;> (try simp only [Fin.val_mk]) <;> omega⟩

end SubRows


section Ident
variable {R : Type*} [CommRing R]

/-- Move column `q` of a square matrix to the front. -/
def colFront {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (q : Fin (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun r l => Fin.cases (A r q) (fun e => A r (q.succAbove e)) l

theorem det_colFront {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (q : Fin (n + 1)) :
    (colFront A q).det = (-1) ^ (q : ℕ) * A.det := by
  rw [Matrix.det_succ_column _ 0, Matrix.det_succ_column A q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have : (colFront A q).submatrix r.succAbove (Fin.succAbove 0) = A.submatrix r.succAbove q.succAbove := by
    ext a b; simp [colFront]
  have h2 : ((-1 : R) ^ (q : ℕ)) * (-1) ^ (q : ℕ) = 1 := by rw [← mul_pow]; simp
  rw [this]; simp only [colFront, Matrix.of_apply, Fin.cases_zero, Fin.val_zero, add_zero, pow_add]
  linear_combination (-((-1 : R) ^ (r : ℕ) * A r q * (A.submatrix r.succAbove q.succAbove).det)) * h2

/-- **Bordered-determinant identification.** A Cramer coefficient whose columns are all columns
of `N` except column `j` (with the bordering column at position `q`) is a signed coordinate of
`crossVec N`. -/
theorem cramerCoef_eq_crossVec {n p : ℕ} (M : Matrix (Fin (n + 1)) (Fin p) R) (g : Fin n → Fin p)
    (k : Fin p) (N : Matrix (Fin (n + 1)) (Fin (n + 2)) R) (j : Fin (n + 2)) (q : Fin (n + 1))
    (hk : ∀ r, M r k = N r (j.succAbove q))
    (hg : ∀ r e, M r (g e) = N r (j.succAbove (q.succAbove e))) :
    cramerCoef M g k = (-1) ^ (q : ℕ) * (-1) ^ (j : ℕ) * crossVec N j := by
  have h : colBorder M g (fun r => M r k) = colFront (N.submatrix id j.succAbove) q := by
    ext r l; refine Fin.cases ?_ (fun e => ?_) l
    · simp [colBorder, colFront, hk]
    · simp [colBorder, colFront, hg]
  have hs : ((-1 : R) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := by rw [← mul_pow]; simp
  unfold cramerCoef; rw [h, det_colFront, crossVec]
  linear_combination (-(1 : R)) ^ (q : ℕ) * (N.submatrix id j.succAbove).det * hs.symm

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (e : Fin n) :
    ((p.succAbove e : Fin (n + 1)) : ℕ) = if (e : ℕ) < (p : ℕ) then (e : ℕ) else (e : ℕ) + 1 := by
  rcases Nat.lt_or_ge (e : ℕ) (p : ℕ) with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega), if_pos h]; simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega), if_neg (by omega)]; simp

/-- The subfamily vector `w`. -/
abbrev subVec (m : ℕ) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) : Fin (2 * m + 2) → R :=
  crossVec (KP (2 * m + 1) (x ∘ i.succAbove) (y ∘ i.succAbove))

theorem subRows_entry (m : ℕ) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) (r : Fin (2 * m + 1))
    (l : Fin (2 * m + 2)) :
    subRows m x y i r ((⟨m + 1, by omega⟩ : Fin (2 * m + 3)).succAbove l) =
      KP (2 * m + 1) (x ∘ i.succAbove) (y ∘ i.succAbove) r l := by
  rw [KP_sub_eq]; rfl

/-- Relation 1, coefficient of `Q₀ (parent)` = `(-1)^m · Q_m(w)` (`m = 2`: `A57`). -/
theorem cramer1_Q0 (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    cramerCoef (subRows m x y i) (elim1 m) ⟨m + 2, by omega⟩ =
      (-1) ^ (m + 1) * (-1) ^ (2 * m + 1) * subVec m x y i (Fin.last _) := by
  refine cramerCoef_eq_crossVec _ _ _ _ (Fin.last _) ⟨m + 1, by omega⟩ (fun r => ?_) (fun r e => ?_)
  · rw [← subRows_entry]; congr 1; ext; simp only [val_succAbove, Fin.val_last, Fin.val_mk]; split_ifs <;> first | omega | (simp_all; done) | (simp_all; omega)
  · rw [← subRows_entry]; congr 1; ext
    simp only [val_succAbove, Fin.val_last, elim1]; split_ifs <;> first | omega | (simp_all; done) | (simp_all; omega)

/-- Relation 1, coefficient of `Q_m (parent)` = `(-1)^(m+1) · Q₀(w)` (`m = 2`: `-k1`). -/
theorem cramer1_Qm (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    cramerCoef (subRows m x y i) (elim1 m) (Fin.last _) =
      (-1) ^ (2 * m) * (-1) ^ (m + 1) * subVec m x y i ⟨m + 1, by omega⟩ := by
  refine cramerCoef_eq_crossVec _ _ _ _ ⟨m + 1, by omega⟩ (Fin.last _) (fun r => ?_) (fun r e => ?_)
  · rw [← subRows_entry]; congr 1; ext; simp only [val_succAbove, Fin.val_last]; split_ifs <;> first | omega | (simp_all; done) | (simp_all; omega)
  · rw [← subRows_entry]; congr 1; ext
    simp only [val_succAbove, Fin.val_last, elim1]; split_ifs <;> first | omega | (simp_all; done) | (simp_all; omega)

/-- Relation 2, coefficient of `P₀ (parent)` = `(-1)^(2m+1) · Q_m(w)` (`m = 2`: `-A57`). -/
theorem cramer2_P0 (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    cramerCoef (subRows m x y i) (elim2 m) 0 =
      (-1) ^ (0 : ℕ) * (-1) ^ (2 * m + 1) * subVec m x y i (Fin.last _) := by
  refine cramerCoef_eq_crossVec _ _ _ _ (Fin.last _) 0 (fun r => ?_) (fun r e => ?_)
  · rw [← subRows_entry]; congr 1
  · rw [← subRows_entry]; congr 1; ext
    simp only [val_succAbove, Fin.val_last, Fin.val_zero, elim2]; split_ifs <;> first | omega | (simp_all; done) | (simp_all; omega)

/-- Relation 2, coefficient of `Q_m (parent)` = `(-1)^(2m) · P₀(w)` (`m = 2`: `k3`). -/
theorem cramer2_Qm (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    cramerCoef (subRows m x y i) (elim2 m) (Fin.last _) =
      (-1) ^ (2 * m) * (-1) ^ (0 : ℕ) * subVec m x y i 0 := by
  refine cramerCoef_eq_crossVec _ _ _ _ 0 (Fin.last _) (fun r => ?_) (fun r e => ?_)
  · rw [← subRows_entry]; congr 1; ext; simp only [val_succAbove, Fin.val_last, Fin.val_zero]; split_ifs <;> first | omega | (simp_all; done) | (simp_all; omega)
  · rw [← subRows_entry]; congr 1; ext
    simp only [val_succAbove, Fin.val_last, Fin.val_zero, elim2]; split_ifs <;> first | omega | (simp_all; done) | (simp_all; omega)

end Ident


section Assembled
variable {R : Type*} [CommRing R]

/-- **Row relation 1, general `m`, in coordinates.** `v` = parent cross vector, `w` = subfamily
cross vector, `C₁` = Cramer coefficient of `P_{m+1}`:
`v_{m+1}·C₁ + (-1)^m (Q₀(v)·Q_m(w) − Q_m(v)·Q₀(w)) = 0`. (`m = 2`: `rowRel1`, `C₁ = −k0`.) -/
theorem rowRel1_gen (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    crossVec (KP (2 * m + 2) x y) ⟨m + 1, by omega⟩ *
        cramerCoef (subRows m x y i) (elim1 m) ⟨m + 1, by omega⟩ +
      (-1) ^ m * (crossVec (KP (2 * m + 2) x y) ⟨m + 2, by omega⟩ * subVec m x y i (Fin.last _) -
        crossVec (KP (2 * m + 2) x y) (Fin.last _) * subVec m x y i ⟨m + 1, by omega⟩) = 0 := by
  have h := rowRelGen1 m hm x y i
  rw [cramer1_Q0 m hm, cramer1_Qm m hm] at h
  simp only [pow_succ, pow_mul, neg_one_sq, one_pow] at h
  linear_combination h

/-- **Row relation 2, general `m`, in coordinates.**
`−P₀(v)·Q_m(w) + v_{m+1}·C₂ + Q_m(v)·P₀(w) = 0`. (`m = 2`: `rowRel2`, `C₂ = k2`.) -/
theorem rowRel2_gen (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    -(crossVec (KP (2 * m + 2) x y) 0 * subVec m x y i (Fin.last _)) +
      crossVec (KP (2 * m + 2) x y) ⟨m + 1, by omega⟩ *
        cramerCoef (subRows m x y i) (elim2 m) ⟨m + 1, by omega⟩ +
      crossVec (KP (2 * m + 2) x y) (Fin.last _) * subVec m x y i 0 = 0 := by
  have h := rowRelGen2 m x y i
  rw [cramer2_P0 m hm, cramer2_Qm m hm] at h
  simp only [pow_succ, pow_zero, pow_mul, neg_one_sq, one_pow] at h
  linear_combination h

/-- `m = 2` instance of `rowRel1_gen`, with `w` read through the existing closed forms
(`Q₀(w) = k1`, `Q₂(w) = kA57`); compare `rowRel1 : −k0·v3 + A57·v4 − k1·v6 = 0`. -/
theorem rowRel1_m2 (x y : Fin 6 → R) (i : Fin 6) :
    crossVec (KP 6 x y) 3 * cramerCoef (subRows 2 x y i) (elim1 2) 3 +
      (kA57 (x (i.succAbove 0)) (x (i.succAbove 1)) (x (i.succAbove 2)) (x (i.succAbove 3))
          (x (i.succAbove 4)) (y (i.succAbove 0)) (y (i.succAbove 1)) (y (i.succAbove 2))
          (y (i.succAbove 3)) (y (i.succAbove 4)) * crossVec (KP 6 x y) 4 -
        k1 (x (i.succAbove 0)) (x (i.succAbove 1)) (x (i.succAbove 2)) (x (i.succAbove 3))
          (x (i.succAbove 4)) (y (i.succAbove 0)) (y (i.succAbove 1)) (y (i.succAbove 2))
          (y (i.succAbove 3)) (y (i.succAbove 4)) * crossVec (KP 6 x y) 6) = 0 := by
  have h := rowRel1_gen 2 (by norm_num) x y i
  simp only [subVec, crossVec_KP5_Q0, crossVec_KP5_Q2, Function.comp_apply] at h
  have e5 : (Fin.last (2 * 2 + 1) : Fin 6) = 5 := rfl
  have e3 : (⟨2 + 1, by omega⟩ : Fin 6) = 3 := rfl
  rw [e5, e3, crossVec_KP5_Q2, crossVec_KP5_Q0] at h
  simp only [Function.comp_apply] at h
  have a0 : crossVec (KP (2 * 2 + 2) x y) 0 = crossVec (KP 6 x y) 0 := rfl
  have a3 : crossVec (KP (2 * 2 + 2) x y) ⟨2 + 1, by omega⟩ = crossVec (KP 6 x y) 3 := rfl
  have a4 : crossVec (KP (2 * 2 + 2) x y) ⟨2 + 2, by omega⟩ = crossVec (KP 6 x y) 4 := rfl
  have a6 : crossVec (KP (2 * 2 + 2) x y) (Fin.last _) = crossVec (KP 6 x y) 6 := rfl
  have b1 : cramerCoef (subRows 2 x y i) (elim1 2) ⟨2 + 1, by omega⟩ =
    cramerCoef (subRows 2 x y i) (elim1 2) 3 := rfl
  have b2 : cramerCoef (subRows 2 x y i) (elim2 2) ⟨2 + 1, by omega⟩ =
    cramerCoef (subRows 2 x y i) (elim2 2) 3 := rfl
  rw [a3, a6] at h
  try rw [b1] at h
  try rw [b2] at h
  try rw [a0] at h
  try rw [a4] at h
  linear_combination h

/-- `m = 2` instance of `rowRel2_gen` (`P₀(w) = k3`); compare
`rowRel2 : −A57·v0 + k2·v3 + k3·v6 = 0`. -/
theorem rowRel2_m2 (x y : Fin 6 → R) (i : Fin 6) :
    -(crossVec (KP 6 x y) 0 * kA57 (x (i.succAbove 0)) (x (i.succAbove 1)) (x (i.succAbove 2))
        (x (i.succAbove 3)) (x (i.succAbove 4)) (y (i.succAbove 0)) (y (i.succAbove 1))
        (y (i.succAbove 2)) (y (i.succAbove 3)) (y (i.succAbove 4))) +
      crossVec (KP 6 x y) 3 * cramerCoef (subRows 2 x y i) (elim2 2) 3 +
      crossVec (KP 6 x y) 6 * k3 (x (i.succAbove 0)) (x (i.succAbove 1)) (x (i.succAbove 2))
        (x (i.succAbove 3)) (x (i.succAbove 4)) (y (i.succAbove 0)) (y (i.succAbove 1))
        (y (i.succAbove 2)) (y (i.succAbove 3)) (y (i.succAbove 4)) = 0 := by
  have h := rowRel2_gen 2 (by norm_num) x y i
  have e5 : (Fin.last (2 * 2 + 1) : Fin 6) = 5 := rfl
  simp only [subVec] at h
  rw [e5, crossVec_KP5_Q2, crossVec_KP5_P0] at h
  simp only [Function.comp_apply] at h
  have a0 : crossVec (KP (2 * 2 + 2) x y) 0 = crossVec (KP 6 x y) 0 := rfl
  have a3 : crossVec (KP (2 * 2 + 2) x y) ⟨2 + 1, by omega⟩ = crossVec (KP 6 x y) 3 := rfl
  have a4 : crossVec (KP (2 * 2 + 2) x y) ⟨2 + 2, by omega⟩ = crossVec (KP 6 x y) 4 := rfl
  have a6 : crossVec (KP (2 * 2 + 2) x y) (Fin.last _) = crossVec (KP 6 x y) 6 := rfl
  have b1 : cramerCoef (subRows 2 x y i) (elim1 2) ⟨2 + 1, by omega⟩ =
    cramerCoef (subRows 2 x y i) (elim1 2) 3 := rfl
  have b2 : cramerCoef (subRows 2 x y i) (elim2 2) ⟨2 + 1, by omega⟩ =
    cramerCoef (subRows 2 x y i) (elim2 2) 3 := rfl
  rw [a3, a6] at h
  try rw [b1] at h
  try rw [b2] at h
  try rw [a0] at h
  try rw [a4] at h
  linear_combination h

end Assembled


section Cleared
variable {R : Type*} [CommRing R]

/-- **General-`m` cleared step identity (linear half of `StepEven m`).** With `v` the parent and
`w` the subfamily cross vector, `C₁, C₂` the two Cramer coefficients of `P_{m+1}`:
`−v₀ v_{m+1} C₁ + (−1)^m (v₀ v_last Q₀(w) − v_{m+2} v_{m+1} C₂ − v_{m+2} v_last P₀(w)) = 0`.
This is `(−v₀)·rowRel1_gen − (−1)^m v_{m+2}·rowRel2_gen`; at `m = 2` it is the identity used in
`stepEven_two` (`C₁ = −k0`, `C₂ = k2`). -/
theorem stepEven_cleared_gen (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    -(crossVec (KP (2 * m + 2) x y) 0 * crossVec (KP (2 * m + 2) x y) ⟨m + 1, by omega⟩ *
        cramerCoef (subRows m x y i) (elim1 m) ⟨m + 1, by omega⟩) +
      (-1) ^ m * (crossVec (KP (2 * m + 2) x y) 0 * crossVec (KP (2 * m + 2) x y) (Fin.last _) *
          subVec m x y i ⟨m + 1, by omega⟩ -
        crossVec (KP (2 * m + 2) x y) ⟨m + 2, by omega⟩ * crossVec (KP (2 * m + 2) x y) ⟨m + 1, by omega⟩ *
          cramerCoef (subRows m x y i) (elim2 m) ⟨m + 1, by omega⟩ -
        crossVec (KP (2 * m + 2) x y) ⟨m + 2, by omega⟩ * crossVec (KP (2 * m + 2) x y) (Fin.last _) *
          subVec m x y i 0) = 0 := by
  linear_combination (-crossVec (KP (2 * m + 2) x y) 0) * rowRel1_gen m hm x y i -
    (-1) ^ m * crossVec (KP (2 * m + 2) x y) ⟨m + 2, by omega⟩ * rowRel2_gen m hm x y i

end Cleared

end Clifford.MorleyKernel

/-! # Paper L / J8: odd-size column reversal, the four odd-size facts, and `StepEven m`

Everything below is new; the prefix above is `scratch/CramerStep.lean` verbatim.

Note. Swapping `x ↔ y` does **not** permute the columns of `KP (2m+1) x y` itself: the swap
sends the `P`-block monomials `x^a y^(m+1-a)` (`a ≤ m`) to `x^(m+1-a) y^a`, and `x^(m+1)` is
not a column of `KP (2m+1) x y`. The swap is a block reversal onto `KPhi m x y`, the
`(2m+1) × (2m+2)` matrix with columns `P_1 … P_{m+1}, Q_0 … Q_m` (the parent columns minus
`P_0`; for a subfamily it is `subRows` with column `P_0` removed, `KPhi_sub_eq`). -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix Equiv

section Odd
variable {R : Type*} [CommRing R]

/-- Columns `P_1 … P_{m+1}` (`(-x)^(j+1) y^(m-j)`, `j ≤ m`) and `Q_0 … Q_m` (as in `KP (2m+1)`). -/
def KPhi (m : ℕ) (x y : Fin (2 * m + 1) → R) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 2)) R :=
  fun k j => if (j : ℕ) ≤ m then (-x k) ^ ((j : ℕ) + 1) * y k ^ (m - j)
    else -((-x k) ^ ((j : ℕ) - (m + 1)) * y k ^ (m - ((j : ℕ) - (m + 1))))

/-- `KPhi` of a subfamily = the subfamily rows of the parent with column `P_0` removed. -/
theorem KPhi_sub_eq (m : ℕ) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    KPhi m (x ∘ i.succAbove) (y ∘ i.succAbove) = (subRows m x y i).submatrix id Fin.succ := by
  ext k j
  have e : (2 * m + 2) / 2 = m + 1 := by omega
  simp only [subRows, Matrix.submatrix_apply, KP, KPhi, Function.comp_apply, e, id, Fin.val_succ]
  split_ifs <;> first | (exfalso; omega) | rfl | (congr 2 <;> omega) | (congr 3 <;> omega)

def blockEquivOdd (m : ℕ) : Fin (m + 1) ⊕ Fin (m + 1) ≃ Fin (2 * m + 1 + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- Reverse within each block of `Fin (2m+2)`: `j ↦ m - j` (`j ≤ m`), `j ↦ 3m+2-j` (`j > m`). -/
def blockRevOdd (m : ℕ) : Perm (Fin (2 * m + 1 + 1)) :=
  (blockEquivOdd m).permCongr (Equiv.sumCongr Fin.revPerm Fin.revPerm)

theorem blockEquivOdd_inl (m : ℕ) (a : Fin (m + 1)) : ((blockEquivOdd m (Sum.inl a)) : ℕ) = a := by
  simp [blockEquivOdd]

theorem blockEquivOdd_inr (m : ℕ) (b : Fin (m + 1)) :
    ((blockEquivOdd m (Sum.inr b)) : ℕ) = m + 1 + b := by
  simp [blockEquivOdd]; omega

theorem blockRevOdd_blockEquivOdd (m : ℕ) (s : Fin (m + 1) ⊕ Fin (m + 1)) :
    blockRevOdd m (blockEquivOdd m s) =
      blockEquivOdd m (Equiv.sumCongr Fin.revPerm Fin.revPerm s) := by
  simp [blockRevOdd, Equiv.permCongr_apply]

theorem blockRevOdd_val (m : ℕ) (j : Fin (2 * m + 1 + 1)) :
    ((blockRevOdd m j : Fin _) : ℕ) = if (j : ℕ) ≤ m then m - j else 3 * m + 2 - j := by
  obtain ⟨s, rfl⟩ := (blockEquivOdd m).surjective j
  rw [blockRevOdd_blockEquivOdd]
  rcases s with a | b
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, blockEquivOdd_inl, Fin.revPerm_apply, Fin.val_rev]
    rw [if_pos (by omega)]; omega
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, blockEquivOdd_inr, Fin.revPerm_apply, Fin.val_rev]
    rw [if_neg (by omega)]; omega

/-- The two block reversals have equal sign, so `sign (blockRevOdd m) = 1` for every `m`. -/
theorem sign_blockRevOdd (m : ℕ) : Perm.sign (blockRevOdd m) = 1 := by
  rw [blockRevOdd, Perm.sign_permCongr, Perm.sign_sumCongr, Int.units_mul_self]

/-- Column scalars: `(-1)^(m+1)` on the `P`-block, `(-1)^m` on the `Q`-block. -/
def blockSignOdd (m : ℕ) (j : Fin (2 * m + 1 + 1)) : R :=
  if (j : ℕ) ≤ m then (-1) ^ (m + 1) else (-1) ^ m

theorem blockSignOdd_sq (m : ℕ) (j : Fin (2 * m + 1 + 1)) :
    (blockSignOdd m j : R) * blockSignOdd m j = 1 := by
  unfold blockSignOdd; split_ifs <;> (rw [← pow_add]; exact Even.neg_one_pow ⟨_, rfl⟩)

theorem prod_blockSignOdd (m : ℕ) : ∏ l, (blockSignOdd m l : R) = (-1) ^ (m + 1) := by
  rw [← (blockEquivOdd m).prod_comp, Fintype.prod_sum_type]
  simp only [blockSignOdd, blockEquivOdd_inl, blockEquivOdd_inr]
  have h1 : ∀ a : Fin (m + 1), ((a : ℕ) ≤ m) := fun a => by omega
  have h2 : ∀ b : Fin (m + 1), ¬ (m + 1 + (b : ℕ) ≤ m) := fun b => by omega
  simp only [h1, h2, if_true, if_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_mul, ← pow_add,
    show (m + 1) * (m + 1) + m * (m + 1) = (m + 1) + 2 * (m * (m + 1)) by ring,
    pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **Odd-size swap = block reversal onto `KPhi`** (analogue of `KP_swap_entry`). -/
theorem KP_swap_entry_odd (m : ℕ) (x y : Fin (2 * m + 1) → R)
    (k : Fin (2 * m + 1)) (j : Fin (2 * m + 1 + 1)) :
    KP (2 * m + 1) y x k j = blockSignOdd m j * KPhi m x y k (blockRevOdd m j) := by
  have e1 : (2 * m + 1) / 2 = m := by omega
  have e2 : 2 * m + 1 - m = m + 1 := by omega
  have hv := blockRevOdd_val m j
  simp only [KP, KPhi, blockSignOdd, e1, e2]
  by_cases hj : (j : ℕ) ≤ m
  · rw [if_pos hj] at hv
    rw [if_pos hj, if_pos hj, if_pos (by omega), hv]
    obtain ⟨b, hb⟩ : ∃ b, m = j + b := ⟨m - j, by omega⟩
    rw [show m + 1 - (j : ℕ) = b + 1 by omega, show m - (m - (j : ℕ)) = (j : ℕ) by omega,
      show m - (j : ℕ) + 1 = b + 1 by omega, aux_pow_swap, show (j : ℕ) + (b + 1) = m + 1 by omega]
  · rw [if_neg hj] at hv
    rw [if_neg hj, if_neg hj, if_neg (by omega), hv]
    obtain ⟨c, hc⟩ : ∃ c, m = ((j : ℕ) - (m + 1)) + c := ⟨m - ((j : ℕ) - (m + 1)), by omega⟩
    rw [show m + 1 - 1 - ((j : ℕ) - (m + 1)) = c by omega,
      show 3 * m + 2 - (j : ℕ) - (m + 1) = c by omega,
      show m - c = (j : ℕ) - (m + 1) by omega]
    rw [aux_pow_swap, show (j : ℕ) - (m + 1) + c = m by omega]; ring

/-- The swap through `crossVec_colPerm`: `crossVec (KP y x) j = d_j (-1)^(m+1) crossVec (KPhi x y) (σ j)`. -/
theorem crossVec_KP_odd_swap (m : ℕ) (x y : Fin (2 * m + 1) → R) (j : Fin (2 * m + 1 + 1)) :
    crossVec (KP (2 * m + 1) y x) j =
      blockSignOdd m j * (-1) ^ (m + 1) * crossVec (KPhi m x y) (blockRevOdd m j) := by
  have H := crossVec_colPerm (KPhi m x y) (KP (2 * m + 1) y x) (blockRevOdd m)
    (blockSignOdd m) (KP_swap_entry_odd m x y) j
  rw [prod_blockSignOdd, sign_blockRevOdd] at H
  simp only [Units.val_one, Int.cast_one, mul_one] at H
  linear_combination (blockSignOdd m j : R) * H - crossVec (KP (2 * m + 1) y x) j * blockSignOdd_sq (R := R) m j

/-- `KPhi` without `P_{m+1}` is `KP (2m+1)` without `P_0`. -/
theorem KPhi_del_m (m : ℕ) (x y : Fin (2 * m + 1) → R) :
    (KPhi m x y).submatrix id (⟨m, by omega⟩ : Fin (2 * m + 2)).succAbove =
      (KP (2 * m + 1) x y).submatrix id (0 : Fin (2 * m + 2)).succAbove := by
  ext k l
  have e1 : (2 * m + 1) / 2 = m := by omega
  have hl := val_succAbove (⟨m, by omega⟩ : Fin (2 * m + 2)) l
  simp only [Fin.val_mk] at hl
  simp only [Matrix.submatrix_apply, id, KPhi, KP, e1, Fin.succAbove_zero, Fin.val_succ, hl]
  split_ifs <;> first | (exfalso; omega) | rfl | (congr 2 <;> omega) | (congr 3 <;> omega)

/-- **Fact 1 (ring form).** `crossVec (KP (2m+1) y x) 0 = (-1)^m crossVec (KP (2m+1) x y) 0`. -/
theorem crossVec_KP_odd_swap_P0 (m : ℕ) (x y : Fin (2 * m + 1) → R) :
    crossVec (KP (2 * m + 1) y x) 0 = (-1) ^ m * crossVec (KP (2 * m + 1) x y) 0 := by
  rw [crossVec_KP_odd_swap]
  have hσ : blockRevOdd m 0 = ⟨m, by omega⟩ := by ext; rw [blockRevOdd_val]; simp
  have hs : (blockSignOdd m (0 : Fin (2 * m + 1 + 1)) : R) = (-1) ^ (m + 1) := by
    simp [blockSignOdd]
  rw [hσ, hs]
  have hc : crossVec (KPhi m x y) ⟨m, by omega⟩ = (-1) ^ m * crossVec (KP (2 * m + 1) x y) 0 := by
    simp only [crossVec, KPhi_del_m, Fin.val_zero, pow_zero, one_mul]
  rw [hc]
  have hu : ((-1 : R) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m + 1, rfl⟩
  linear_combination ((-1 : R) ^ m * crossVec (KP (2 * m + 1) x y) 0) * hu

/-- **Fact 3 (ring form).** `crossVec (KP (2m+1) y x) Q_m = - A′`, `A′ = crossVec (KPhi m x y) (m+1)`
(the maximal minor of the parent subfamily rows deleting `P_0` and `Q_0`; `m = 2`: `kA46`). -/
theorem crossVec_KP_odd_swap_last (m : ℕ) (x y : Fin (2 * m + 1) → R) :
    crossVec (KP (2 * m + 1) y x) (Fin.last _) = -crossVec (KPhi m x y) ⟨m + 1, by omega⟩ := by
  rw [crossVec_KP_odd_swap]
  have hσ : blockRevOdd m (Fin.last _) = ⟨m + 1, by omega⟩ := by
    ext; rw [blockRevOdd_val, Fin.val_last, if_neg (by omega)]; show 3 * m + 2 - (2 * m + 1) = m + 1; omega
  have hs : (blockSignOdd m (Fin.last (2 * m + 1)) : R) = (-1) ^ m := by
    simp only [blockSignOdd, Fin.val_last]; rw [if_neg (by omega)]
  rw [hσ, hs]
  have hu : ((-1 : R) ^ m) * (-1) ^ m = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
  rw [pow_succ]
  linear_combination (-crossVec (KPhi m x y) ⟨m + 1, by omega⟩) * hu

/-- **Fact 2 (ring form), swap half.** `crossVec (KP (2m+1) y x) Q_0 = - crossVec (KPhi m x y) last`. -/
theorem crossVec_KP_odd_swap_Q0 (m : ℕ) (x y : Fin (2 * m + 1) → R) :
    crossVec (KP (2 * m + 1) y x) ⟨m + 1, by omega⟩ = -crossVec (KPhi m x y) (Fin.last _) := by
  rw [crossVec_KP_odd_swap]
  have hσ : blockRevOdd m ⟨m + 1, by omega⟩ = Fin.last _ := by
    ext; rw [blockRevOdd_val, Fin.val_last]; simp only [Fin.val_mk]; rw [if_neg (by omega)]; omega
  have hs : (blockSignOdd m (⟨m + 1, by omega⟩ : Fin (2 * m + 1 + 1)) : R) = (-1) ^ m := by
    simp only [blockSignOdd, Fin.val_mk]; rw [if_neg (by omega)]
  rw [hσ, hs]
  have hu : ((-1 : R) ^ m) * (-1) ^ m = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
  rw [pow_succ]
  linear_combination (-crossVec (KPhi m x y) (Fin.last _)) * hu

/-- `C₂` as a `KPhi` coordinate: `C₂ = (-1)^m (-1)^(2m+1) crossVec (KPhi (sub)) last`. -/
theorem cramer2_Pm1 (m : ℕ) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    cramerCoef (subRows m x y i) (elim2 m) ⟨m + 1, by omega⟩ =
      (-1) ^ m * (-1) ^ (2 * m + 1) * crossVec (KPhi m (x ∘ i.succAbove) (y ∘ i.succAbove)) (Fin.last _) := by
  refine cramerCoef_eq_crossVec _ _ _ _ (Fin.last _) ⟨m, by omega⟩ (fun r => ?_) (fun r e => ?_)
  · rw [KPhi_sub_eq]; simp only [Matrix.submatrix_apply, id]; congr 1; ext
    simp only [Fin.val_succ, val_succAbove, Fin.val_last, Fin.val_mk]; split_ifs <;> omega
  · rw [KPhi_sub_eq]; simp only [Matrix.submatrix_apply, id]; congr 1; ext
    simp only [Fin.val_succ, val_succAbove, Fin.val_last, Fin.val_mk, elim2]
    split_ifs <;> simp only [Fin.val_mk] at * <;> omega

end Odd

/-! ### The conjugation facts over `ℂ` -/

/-- **Fact 1.** `conj w₀ = (-1)^m w₀` for the odd cross vector. -/
theorem conj_crossVec_odd_P0 (m : ℕ) (c : Fin (2 * m + 1) → ℂ) :
    conj (crossVec (KP (2 * m + 1) c (fun k => conj (c k))) 0) =
      (-1) ^ m * crossVec (KP (2 * m + 1) c (fun k => conj (c k))) 0 := by
  rw [conj_crossVec_KP, crossVec_KP_odd_swap_P0]

/-- **Fact 3.** `conj w_last = -A′`, `A′ = crossVec (KPhi m c (conj c)) (m+1)`. -/
theorem conj_crossVec_odd_last (m : ℕ) (c : Fin (2 * m + 1) → ℂ) :
    conj (crossVec (KP (2 * m + 1) c (fun k => conj (c k))) (Fin.last _)) =
      -crossVec (KPhi m c (fun k => conj (c k))) ⟨m + 1, by omega⟩ := by
  rw [conj_crossVec_KP, crossVec_KP_odd_swap_last]

/-- **Fact 2.** `conj w_{m+1} = (-1)^m C₂` for the subfamily vector `w`. -/
theorem conj_subVec_Q0 (m : ℕ) (c : Fin (2 * m + 2) → ℂ) (i : Fin (2 * m + 2)) :
    conj (subVec m c (fun k => conj (c k)) i ⟨m + 1, by omega⟩) =
      (-1) ^ m * cramerCoef (subRows m c (fun k => conj (c k)) i) (elim2 m) ⟨m + 1, by omega⟩ := by
  rw [cramer2_Pm1, subVec]
  rw [show ((fun k => conj (c k)) ∘ i.succAbove) = fun k => conj ((c ∘ i.succAbove) k) from rfl]
  rw [conj_crossVec_KP (2 * m + 1) (c ∘ i.succAbove), crossVec_KP_odd_swap_Q0]
  have hu : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
  have h2 : (-1 : ℂ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h2]
  linear_combination (crossVec (KPhi m (c ∘ i.succAbove) (fun k => conj ((c ∘ i.succAbove) k)))
    (Fin.last _)) * hu

end Clifford.MorleyKernel

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix Equiv

/-! ### Fact 4: the three-term Plücker relation, general `m` (via `cramer_three`) -/

section Pl
variable {R : Type*} [CommRing R]

/-- Eliminated columns for fact 4: `P₁ … P_{m+1}, Q₁ … Q_{m-1}` (kept: `P₀, Q₀, Q_m`). -/
def elim3 (m : ℕ) : Fin (2 * m) → Fin (2 * m + 3) :=
  fun e => if (e : ℕ) ≤ m then ⟨e + 1, by omega⟩ else ⟨e + 2, by omega⟩

/-- The subfamily vector `w`, re-inserted with a `0` at column `P_{m+1}`, is a kernel vector of
the subfamily rows of the parent matrix. -/
macro "fin_idx" : tactic => `(tactic| first | done | (
  ext
  try simp only [Fin.succAbove_zero, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc,
    val_succAbove, Fin.val_last, Fin.val_zero, Fin.val_mk, elim1, elim2, elim3, id,
    apply_ite Fin.val, Fin.val_mk] at *
  all_goals ((try split_ifs) <;> (try simp only [Fin.val_mk, Fin.val_zero] at *) <;> omega)))

theorem ins_eval {n : ℕ} (p : Fin (n + 1)) (w : Fin n → R) (k : Fin (n + 1)) (j : Fin n)
    (hk : k = p.succAbove j) : Fin.insertNth (α := fun _ => R) p 0 w k = w j := by
  subst hk; simp

theorem subRows_mulVec_ins (m : ℕ) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    subRows m x y i *ᵥ Fin.insertNth (α := fun _ => R) (⟨m + 1, by omega⟩ : Fin (2 * m + 3)) 0 (subVec m x y i) = 0 := by
  funext r
  have h := congrFun (mulVec_crossVec (KP (2 * m + 1) (x ∘ i.succAbove) (y ∘ i.succAbove))) r
  simp only [mulVec, dotProduct, Pi.zero_apply] at h ⊢
  rw [Fin.sum_univ_succAbove _ (⟨m + 1, by omega⟩ : Fin (2 * m + 3))]
  simp only [Fin.insertNth_apply_same, mul_zero, zero_add, Fin.insertNth_apply_succAbove, subRows_entry]
  exact h

theorem cramer3_P0 (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    cramerCoef (subRows m x y i) (elim3 m) 0 =
      (-1) ^ (m + 1) * cramerCoef (subRows m x y i) (elim1 m) ⟨m + 1, by omega⟩ := by
  set N := (subRows m x y i).submatrix id (Fin.succAbove (⟨m + 2, by omega⟩ : Fin (2 * m + 3)))
  have h1 : cramerCoef (subRows m x y i) (elim3 m) 0 = _ :=
    cramerCoef_eq_crossVec (subRows m x y i) (elim3 m) 0 N (Fin.last _) 0
    (fun r => by
      simp only [N, Matrix.submatrix_apply, id]; congr 1 <;> fin_idx)
    (fun r e => by
      simp only [N, Matrix.submatrix_apply, id]; congr 1 <;> fin_idx)
  have h2 : cramerCoef (subRows m x y i) (elim1 m) ⟨m + 1, by omega⟩ = _ :=
    cramerCoef_eq_crossVec (subRows m x y i) (elim1 m) ⟨m + 1, by omega⟩ N (Fin.last _)
    ⟨m + 1, by omega⟩
    (fun r => by
      simp only [N, Matrix.submatrix_apply, id]; congr 1 <;> fin_idx)
    (fun r e => by
      simp only [N, Matrix.submatrix_apply, id]; congr 1 <;> fin_idx)
  rw [h1, h2]
  simp only [Fin.val_zero, Fin.val_mk, Fin.val_last, pow_zero, one_mul]
  have hu : ((-1 : R) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m + 1, rfl⟩
  linear_combination (-((-1 : R) ^ (2 * m + 1) * crossVec N (Fin.last _))) * hu

theorem cramer3_Q0 (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    cramerCoef (subRows m x y i) (elim3 m) ⟨m + 2, by omega⟩ =
      -cramerCoef (subRows m x y i) (elim2 m) ⟨m + 1, by omega⟩ := by
  rw [cramer2_Pm1]
  rw [cramerCoef_eq_crossVec _ _ _ (KPhi m (x ∘ i.succAbove) (y ∘ i.succAbove)) (Fin.last _) ⟨m + 1, by omega⟩ (fun r => ?_) (fun r e => ?_)]
  · simp only [Fin.val_mk, Fin.val_last, pow_succ, pow_mul, neg_one_sq, one_pow]; ring
  · rw [KPhi_sub_eq]; simp only [Matrix.submatrix_apply, id]; congr 1 <;> fin_idx
  · rw [KPhi_sub_eq]; simp only [Matrix.submatrix_apply, id]; congr 1 <;> fin_idx

theorem cramer3_Qm (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    cramerCoef (subRows m x y i) (elim3 m) (Fin.last _) =
      (-1) ^ (m + 1) * crossVec (KPhi m (x ∘ i.succAbove) (y ∘ i.succAbove)) ⟨m + 1, by omega⟩ := by
  rw [cramerCoef_eq_crossVec _ _ _ (KPhi m (x ∘ i.succAbove) (y ∘ i.succAbove)) ⟨m + 1, by omega⟩ (Fin.last _) (fun r => ?_) (fun r e => ?_)]
  · simp only [Fin.val_mk, Fin.val_last, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]; ring
  · rw [KPhi_sub_eq]; simp only [Matrix.submatrix_apply, id]; congr 1 <;> fin_idx
  · rw [KPhi_sub_eq]; simp only [Matrix.submatrix_apply, id]; congr 1 <;> fin_idx

/-- **Fact 4 (Plücker, general `m`).** `w₀·C₁ + (-1)^m w_{m+1}·C₂ + w_last·A′ = 0`
(`m = 2`: `-k3 k0 + k1 k2 + kA57 kA46 = 0`, i.e. `k0k3_sub_k1k2`). -/
theorem plucker_odd (m : ℕ) (hm : 1 ≤ m) (x y : Fin (2 * m + 2) → R) (i : Fin (2 * m + 2)) :
    subVec m x y i 0 * cramerCoef (subRows m x y i) (elim1 m) ⟨m + 1, by omega⟩ +
      (-1) ^ m * subVec m x y i ⟨m + 1, by omega⟩ *
        cramerCoef (subRows m x y i) (elim2 m) ⟨m + 1, by omega⟩ +
      subVec m x y i (Fin.last _) *
        crossVec (KPhi m (x ∘ i.succAbove) (y ∘ i.succAbove)) ⟨m + 1, by omega⟩ = 0 := by
  have h := cramer_three _ (elim3 m) _ (subRows_mulVec_ins m x y i) 0 ⟨m + 2, by omega⟩ (Fin.last _)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]; omega)
    (by
      intro k ha hb hc
      simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk] at ha hb hc
      by_cases hk : (k : ℕ) ≤ m + 1
      · exact ⟨⟨k - 1, by omega⟩, by ext; simp only [elim3]; split_ifs <;> (try simp only [Fin.val_mk]) <;> omega⟩
      · exact ⟨⟨k - 2, by omega⟩, by ext; simp only [elim3]; split_ifs <;> (try simp only [Fin.val_mk]) <;> omega⟩)
  rw [ins_eval _ _ 0 0 (by ext; rw [val_succAbove, if_pos (by simp)]; try simp),
    ins_eval _ _ ⟨m + 2, by omega⟩ ⟨m + 1, by omega⟩ (by ext; rw [val_succAbove, if_neg (by simp)]; try simp),
    ins_eval _ _ (Fin.last _) (Fin.last _) (by ext; rw [val_succAbove, if_neg (by simp; omega)]; try simp),
    cramer3_P0 m hm, cramer3_Q0 m hm, cramer3_Qm m hm, pow_succ] at h
  have hu : ((-1 : R) ^ m) * (-1) ^ m = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
  linear_combination (-(-1 : R) ^ m) * h -
    (subVec m x y i 0 * cramerCoef (subRows m x y i) (elim1 m) ⟨m + 1, by omega⟩ +
      subVec m x y i (Fin.last _) *
        crossVec (KPhi m (x ∘ i.succAbove) (y ∘ i.succAbove)) ⟨m + 1, by omega⟩) * hu

end Pl

/-! ### `StepEven m` for all `m ≥ 1`, and the acceptance test `StepEven 3` -/

theorem stepEven_alg {K : Type*} [Field K] (s w0 w1 wl C1 C2 A v0 v1 v2 vl z zb : K)
    (hv1 : v1 ≠ 0) (hv0 : v0 ≠ 0) (P : w0 * C1 + s * w1 * C2 + wl * A = 0)
    (CL : -(v0 * v1 * C1) + s * (v0 * vl * w1 - v2 * v1 * C2 - v2 * vl * w0) = 0)
    (hA : z * v1 = -vl) (hB : zb * v0 = v2) :
    s * w0 * w0 * z * zb - s * w0 * w1 * z - w0 * (s * C2) * zb + w1 * (s * C2) - wl * -A = 0 := by
  have key : (v1 * v0) * (s * w0 * w0 * z * zb - s * w0 * w1 * z - w0 * (s * C2) * zb +
      w1 * (s * C2) - wl * -A) = 0 := by
    linear_combination (v1 * v0) * P + w0 * CL + w0 * (s * w0 * (zb * v0) - s * w1 * v0) * hA -
      w0 * (s * w0 * vl + s * C2 * v1) * hB
  exact (mul_eq_zero.1 key).resolve_left (mul_ne_zero hv1 hv0)

/-- **`StepEven m` for every `m ≥ 1`.** -/
theorem stepEven_gen (m : ℕ) (hm : 1 ≤ m) : StepEven m := by
  intro c hc hP i
  have hv0 := crossVec_even_P0_ne_zero m c hP
  have F1 := conj_crossVec_odd_P0 m (c ∘ i.succAbove)
  have F3 := conj_crossVec_odd_last m (c ∘ i.succAbove)
  have F2 : conj (crossVec (KP (2 * m + 1) (c ∘ i.succAbove) (fun k => conj ((c ∘ i.succAbove) k)))
      ⟨m + 1, by omega⟩) = (-1) ^ m *
        cramerCoef (subRows m c (fun k => conj (c k)) i) (elim2 m) ⟨m + 1, by omega⟩ :=
    conj_subVec_Q0 m c i
  have hzc := conj_levelPointN_even m c
  have e : (⟨(2 * m + 2) / 2, by omega⟩ : Fin (2 * m + 2 + 1)) = ⟨m + 1, by omega⟩ := by
    ext; exact (by omega : (2 * m + 2) / 2 = m + 1)
  have hA : levelPointN (2 * m + 2) (crossVec (KP (2 * m + 2) c (fun k => conj (c k)))) *
      crossVec (KP (2 * m + 2) c (fun k => conj (c k))) ⟨m + 1, by omega⟩ =
      -crossVec (KP (2 * m + 2) c (fun k => conj (c k))) (Fin.last _) := by
    rw [levelPointN, e, div_mul_cancel₀ _ hP]
  unfold oddCircleEq
  rw [F1, F2, F3, hzc]
  exact stepEven_alg _ _ _ _ _ _ _ _ _ _ _ _ _ hP hv0
    (plucker_odd m hm c (fun k => conj (c k)) i) (stepEven_cleared_gen m hm c (fun k => conj (c k)) i)
    hA (div_mul_cancel₀ _ hv0)

/-- **Acceptance test.** -/
theorem stepEven_three : StepEven 3 := stepEven_gen 3 (by norm_num)

end Clifford.MorleyKernel

/-! # Paper L / J9: unconditional `StepOdd 2`

Everything below is new; the prefix above is `scratch/OddStep.lean` verbatim.
The extra `triP ≠ 0` hypothesis of `stepOdd_two_triP` is removed by a polynomial argument:
`kK_dj_hom` is the Desnanot–Jacobi identity homogenised at the Miquel point (division-free,
any commutative ring); `miquel_clifford_poly` cancels the factor `triP · ∏ xᵢyᵢ` in the domain
`MvPolynomial (Fin 10) ℂ` and evaluates. -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section Hom
variable {R : Type*} [CommRing R]

/-- **Division-free Desnanot–Jacobi.** `kK` homogenised at `(z : w) = (mN : mD)` and
`(Z : W) = (mN' : mD')`, multiplied by the `triP` factor, vanishes identically. -/
theorem kK_dj_hom (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : R) :
    (x₁ * y₁ * x₂ * y₂ * x₃ * y₃ * triP x₁ x₂ x₃ y₁ y₂ y₃) *
      (mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ * k0 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅
        - mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ * k1 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅
        - mN y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ * mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * k2 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅
        + mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * mN y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ *
            k3 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅) = 0 := by
  have h00 := kK_dj x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ 0 0
  have h10 := kK_dj x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ 1 0
  have h01 := kK_dj x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ 0 1
  have h11 := kK_dj x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ 1 1
  rw [kK_expand] at h00 h10 h01 h11
  set N := mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄
  set D := mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄
  set N' := mN y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄
  set D' := mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄
  linear_combination (D - N) * (D' - N') * h00 + N * (D' - N') * h10 + (D - N) * N' * h01
    + N * N' * h11

end Hom

/-- The cleared Clifford-circle value at the Miquel point vanishes for **all** complex
arguments (no non-collinearity hypothesis): polynomial cancellation in `MvPolynomial (Fin 10) ℂ`. -/
theorem miquel_clifford_poly (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : ℂ) :
    mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ * k0 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅
        - mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * mD y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ * k1 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅
        - mN y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ * mD x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * k2 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅
        + mN x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ * mN y₁ y₂ y₃ y₄ x₁ x₂ x₃ x₄ *
            k3 x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ = 0 := by
  let X : Fin 10 → MvPolynomial (Fin 10) ℂ := MvPolynomial.X
  have hP := kK_dj_hom (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7) (X 8) (X 9)
  have hT : X 0 * X 5 * X 1 * X 6 * X 2 * X 7 * triP (X 0) (X 1) (X 2) (X 5) (X 6) (X 7) ≠ 0 := by
    intro h
    have h' := congrArg (MvPolynomial.eval (![1, 2, 3, 0, 0, 1, 4, 9, 0, 0] : Fin 10 → ℂ)) h
    simp [X, triP, det3] at h'
    norm_num at h'
  have hH := (mul_eq_zero.1 hP).resolve_left hT
  have h' := congrArg (MvPolynomial.eval (![x₁, x₂, x₃, x₄, x₅, y₁, y₂, y₃, y₄, y₅] : Fin 10 → ℂ)) hH
  simp only [map_add, map_sub, map_mul, map_zero, map_k0, map_k1, map_k2, map_k3, map_mN, map_mD,
    X, MvPolynomial.eval_X] at h'
  simpa using h'

/-- **`cliffordEq_miquel` without `triP`**: the Miquel point of the first four circles lies on
the Clifford circle as soon as `mD ≠ 0`. -/
theorem cliffordEq_miquel_noT {a b c d e : ℂ}
    (hD : mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0) :
    cliffordEq a b c d e (miquel a b c d) = 0 := by
  have hDb : mD (conj a) (conj b) (conj c) (conj d) a b c d ≠ 0 := by
    rw [← conj_mD]; exact (map_ne_zero _).2 hD
  have H := miquel_clifford_poly a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)
  have e1 := miquel_mul a b c d hD
  have e2 := conj_miquel_mul a b c d hD
  have e1' : mN a b c d (conj a) (conj b) (conj c) (conj d) =
      miquel a b c d * mD a b c d (conj a) (conj b) (conj c) (conj d) := sub_eq_zero.1 e1
  have e2' : mN (conj a) (conj b) (conj c) (conj d) a b c d =
      conj (miquel a b c d) * mD (conj a) (conj b) (conj c) (conj d) a b c d := sub_eq_zero.1 e2
  rw [e1', e2'] at H
  rw [cliffordEq, kK_expand]
  have hDD := mul_ne_zero hD hDb
  refine (mul_eq_zero.1 ?_).resolve_left hDD
  linear_combination H

/-- **`StepOdd 2`** (unconditional: exactly the frozen statement's hypotheses). -/
theorem stepOdd_two : StepOdd 2 := by
  intro c hc i hP
  rw [levelPointN_four_cross _ hP, oddCircleEq_five_cross]
  have hD : mD (c (i.succAbove 0)) (c (i.succAbove 1)) (c (i.succAbove 2)) (c (i.succAbove 3))
      (conj (c (i.succAbove 0))) (conj (c (i.succAbove 1))) (conj (c (i.succAbove 2)))
      (conj (c (i.succAbove 3))) ≠ 0 := by
    have h2 : crossVec (KP 4 (c ∘ i.succAbove) (fun k => conj ((c ∘ i.succAbove) k))) 2 ≠ 0 := hP
    rwa [crossVec_KP4_P2] at h2
  have H := cliffordEq_miquel_noT (e := c i) hD
  simp only [Function.comp_apply]
  refine mul_eq_zero_of_right _ ?_
  fin_cases i
  · rw [cliffordEq, kK_p23451] at H; exact H
  · rw [cliffordEq, kK_p13452, neg_eq_zero] at H; exact H
  · rw [cliffordEq, kK_p12453] at H; exact H
  · rw [cliffordEq, kK_p12354, neg_eq_zero] at H; exact H
  · exact H

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.stepOdd_two

/-! ## J10: the odd-side Cramer kit (even subfamily inside an odd parent)

Indexing: parent `KP (2m+3)` (so `StepOdd (m+1)`), subfamily `KP (2m+2)` on rows `i.succAbove`.
Parent columns: `P₀ … P_{m+1}` (indices `0 … m+1`), `Q₀ … Q_{m+1}` (indices `m+2 … 2m+3`).
Subfamily columns: `P₀ … P_{m+1}` (indices `0 … m+1`), `Q₀ … Q_m` (indices `m+2 … 2m+2`).

**Parity identity.** No column deletion makes the parent rows *equal* to the subfamily matrix
(parent entries have degrees `m+2` (`P`) / `m+1` (`Q`), subfamily entries `m+1` / `m`; deleting one
column always leaves a degree-`(m+2)` column). The correct identity: deleting the **last** column
(`Q_{m+1}`) gives the subfamily matrix with row `r` scaled by `y (i.succAbove r)`
(`KP_sub_eq_odd`); shifting by one column (all but `P_{m+1}`) gives it scaled by `-x` (`subRowsOdd_succ`). -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section OddGen
variable {R : Type*} [CommRing R]

/-- The `2m+2` rows of the odd parent `KP (2m+3)` belonging to the subfamily `c ∘ i.succAbove`. -/
def subRowsOdd (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    Matrix (Fin (2 * m + 2)) (Fin (2 * m + 4)) R :=
  (KP (2 * m + 3) x y).submatrix i.succAbove id

theorem subRowsOdd_mulVec (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    subRowsOdd m x y i *ᵥ crossVec (KP (2 * m + 3) x y) = 0 := by
  funext r
  have := congrFun (mulVec_crossVec (KP (2 * m + 3) x y)) (i.succAbove r)
  simpa [subRowsOdd, mulVec, dotProduct] using this

/-- The subfamily matrix with row `r` scaled by `y (i.succAbove r)`. -/
def subScaled (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    Matrix (Fin (2 * m + 2)) (Fin (2 * m + 3)) R :=
  Matrix.of fun r l => y (i.succAbove r) * KP (2 * m + 2) (x ∘ i.succAbove) (y ∘ i.succAbove) r l

/-- **Parity identity (odd parent, even subfamily).** Dropping row `i` and the last column
`Q_{m+1}` of `KP (2m+3)` gives `KP (2m+2)` of the subfamily, row-scaled by `y`. -/
theorem KP_sub_eq_odd (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    (subRowsOdd m x y i).submatrix id (Fin.last (2 * m + 3)).succAbove = subScaled m x y i := by
  ext k j
  have e : (2 * m + 3) / 2 = m + 1 := by omega
  have e' : (2 * m + 2) / 2 = m + 1 := by omega
  have hj := j.isLt
  simp only [subRowsOdd, subScaled, Matrix.submatrix_apply, Matrix.of_apply, KP, Function.comp_apply,
    e, e', id, Fin.succAbove_last, Fin.coe_castSucc]
  split_ifs with h
  · rw [show 2 * m + 3 - (m + 1) - (j : ℕ) = (2 * m + 2 - (m + 1) - (j : ℕ)) + 1 by omega, pow_succ]
    ring
  · rw [show 2 * m + 3 - (m + 1) - 1 - ((j : ℕ) - (m + 1 + 1)) =
      (2 * m + 2 - (m + 1) - 1 - ((j : ℕ) - (m + 1 + 1))) + 1 by omega, pow_succ]
    ring

theorem crossVec_subScaled (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3))
    (j : Fin (2 * m + 3)) :
    crossVec (subScaled m x y i) j = (∏ r, y (i.succAbove r)) *
      crossVec (KP (2 * m + 2) (x ∘ i.succAbove) (y ∘ i.succAbove)) j := by
  unfold crossVec
  have : (subScaled m x y i).submatrix id j.succAbove = Matrix.of fun r l => y (i.succAbove r) *
      (KP (2 * m + 2) (x ∘ i.succAbove) (y ∘ i.succAbove)).submatrix id j.succAbove r l := by
    ext r l; rfl
  rw [this, det_mul_column]; ring

theorem subRowsOdd_entry (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3))
    (r : Fin (2 * m + 2)) (l : Fin (2 * m + 3)) :
    subRowsOdd m x y i r ((Fin.last (2 * m + 3)).succAbove l) = subScaled m x y i r l := by
  rw [← KP_sub_eq_odd]; rfl

/-- Eliminated columns: `P₁ … P_{m+1}, Q₁ … Q_m` (kept: `P₀, Q₀, Q_{m+1}`). -/
def elimO (m : ℕ) : Fin (2 * m + 1) → Fin (2 * m + 4) :=
  fun e => if (e : ℕ) ≤ m then ⟨e + 1, by omega⟩ else ⟨e + 2, by omega⟩

macro "fin_idxO" : tactic => `(tactic| first | done | (
  ext
  try simp only [Fin.succAbove_zero, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc,
    val_succAbove, Fin.val_last, Fin.val_zero, Fin.val_mk, elimO, id,
    apply_ite Fin.val, Fin.val_mk] at *
  all_goals ((try split_ifs) <;> (try simp only [Fin.val_mk, Fin.val_zero] at *) <;> omega)))

/-- **Odd row relation (raw Cramer form).** -/
theorem rowRelOdd (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    crossVec (KP (2 * m + 3) x y) 0 * cramerCoef (subRowsOdd m x y i) (elimO m) 0 +
    crossVec (KP (2 * m + 3) x y) ⟨m + 2, by omega⟩ *
      cramerCoef (subRowsOdd m x y i) (elimO m) ⟨m + 2, by omega⟩ +
    crossVec (KP (2 * m + 3) x y) (Fin.last _) *
      cramerCoef (subRowsOdd m x y i) (elimO m) (Fin.last _) = 0 := by
  refine cramer_three _ _ _ (subRowsOdd_mulVec m x y i) _ _ _ ?_ ?_ ?_ ?_
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk]; omega
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk]; omega
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk]; omega
  · intro k ha hb hc
    simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, Fin.val_mk] at ha hb hc
    by_cases hk : (k : ℕ) ≤ m + 1
    · exact ⟨⟨k - 1, by omega⟩, by ext; simp only [elimO]; split_ifs <;> (try simp only [Fin.val_mk]) <;> omega⟩
    · exact ⟨⟨k - 2, by omega⟩, by ext; simp only [elimO]; split_ifs <;> (try simp only [Fin.val_mk]) <;> omega⟩

/-- Coefficient of `P₀(v)`: `(-1)^m (∏ y) · Q₀(w)`. -/
theorem cramerO_P0 (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    cramerCoef (subRowsOdd m x y i) (elimO m) 0 =
      (-1) ^ (0 : ℕ) * (-1) ^ (m + 2) * crossVec (subScaled m x y i) ⟨m + 2, by omega⟩ := by
  refine cramerCoef_eq_crossVec _ _ _ _ ⟨m + 2, by omega⟩ 0 (fun r => ?_) (fun r e => ?_)
  · rw [← subRowsOdd_entry]; congr 1 <;> fin_idxO
  · rw [← subRowsOdd_entry]; congr 1 <;> fin_idxO

/-- Coefficient of `Q₀(v)`: `(-1)^(m+1) (∏ y) · P₀(w)`. -/
theorem cramerO_Q0 (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    cramerCoef (subRowsOdd m x y i) (elimO m) ⟨m + 2, by omega⟩ =
      (-1) ^ (m + 1) * (-1) ^ (0 : ℕ) * crossVec (subScaled m x y i) 0 := by
  refine cramerCoef_eq_crossVec _ _ _ _ 0 ⟨m + 1, by omega⟩ (fun r => ?_) (fun r e => ?_)
  · rw [← subRowsOdd_entry]; congr 1 <;> fin_idxO
  · rw [← subRowsOdd_entry]; congr 1 <;> fin_idxO

end OddGen

end Clifford.MorleyKernel

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section OddGen2
variable {R : Type*} [CommRing R]

/-- The even subfamily vector `w = crossVec (KP (2m+2) (x∘i.succAbove) (y∘i.succAbove))`. -/
abbrev subVecOdd (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) : Fin (2 * m + 3) → R :=
  crossVec (KP (2 * m + 2) (x ∘ i.succAbove) (y ∘ i.succAbove))

/-- **Odd row relation, general `m`, in coordinates** (`StepOdd (m+1)` indexing).
`v` = parent `crossVec (KP (2m+3))`, `w` = subfamily vector, `Πy = ∏ᵣ y (i.succAbove r)`,
`C_L` = Cramer coefficient of the parent column `Q_{m+1}`:
`(-1)^m Πy (P₀(v)·Q₀(w) − Q₀(v)·P₀(w)) + Q_{m+1}(v)·C_L = 0`. -/
theorem stepOdd_cleared_gen (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    (-1) ^ m * (∏ r, y (i.succAbove r)) *
        (crossVec (KP (2 * m + 3) x y) 0 * subVecOdd m x y i ⟨m + 2, by omega⟩ -
          crossVec (KP (2 * m + 3) x y) ⟨m + 2, by omega⟩ * subVecOdd m x y i 0) +
      crossVec (KP (2 * m + 3) x y) (Fin.last _) *
        cramerCoef (subRowsOdd m x y i) (elimO m) (Fin.last _) = 0 := by
  have h := rowRelOdd m x y i
  rw [cramerO_P0, cramerO_Q0, crossVec_subScaled, crossVec_subScaled] at h
  simp only [pow_succ, pow_zero] at h
  linear_combination h

end OddGen2

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.KP_sub_eq_odd
#print axioms Clifford.MorleyKernel.cramerO_P0
#print axioms Clifford.MorleyKernel.cramerO_Q0
#print axioms Clifford.MorleyKernel.stepOdd_cleared_gen

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section OddGen3
variable {R : Type*} [CommRing R]

/-- Shifted columns: parent column `l.succ` on subfamily rows = `(-x) ×` subfamily column `l`,
for every `l ≠ P_{m+1}`. -/
theorem subRowsOdd_succ (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3))
    (r : Fin (2 * m + 2)) (l : Fin (2 * m + 3)) (hl : (l : ℕ) ≠ m + 1) :
    subRowsOdd m x y i r l.succ =
      -x (i.succAbove r) * KP (2 * m + 2) (x ∘ i.succAbove) (y ∘ i.succAbove) r l := by
  have e : (2 * m + 3) / 2 = m + 1 := by omega
  have e' : (2 * m + 2) / 2 = m + 1 := by omega
  have hj := l.isLt
  simp only [subRowsOdd, Matrix.submatrix_apply, KP, Function.comp_apply, e, e', id, Fin.val_succ]
  split_ifs with h1 h2 h2
  · rw [show 2 * m + 3 - (m + 1) - ((l : ℕ) + 1) = 2 * m + 2 - (m + 1) - (l : ℕ) by omega, pow_succ]
    ring
  · exfalso; omega
  · exfalso; omega
  · rw [show (l : ℕ) + 1 - (m + 1 + 1) = ((l : ℕ) - (m + 1 + 1)) + 1 by omega,
      show 2 * m + 3 - (m + 1) - 1 - (((l : ℕ) - (m + 1 + 1)) + 1) =
        2 * m + 2 - (m + 1) - 1 - ((l : ℕ) - (m + 1 + 1)) by omega, pow_succ]
    ring

/-- The subfamily matrix with row `r` scaled by `-x (i.succAbove r)`. -/
def subScaledX (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    Matrix (Fin (2 * m + 2)) (Fin (2 * m + 3)) R :=
  Matrix.of fun r l => -x (i.succAbove r) * KP (2 * m + 2) (x ∘ i.succAbove) (y ∘ i.succAbove) r l

theorem crossVec_subScaledX (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3))
    (j : Fin (2 * m + 3)) :
    crossVec (subScaledX m x y i) j = (∏ r, -x (i.succAbove r)) *
      crossVec (KP (2 * m + 2) (x ∘ i.succAbove) (y ∘ i.succAbove)) j := by
  unfold crossVec
  have : (subScaledX m x y i).submatrix id j.succAbove = Matrix.of fun r l => -x (i.succAbove r) *
      (KP (2 * m + 2) (x ∘ i.succAbove) (y ∘ i.succAbove)).submatrix id j.succAbove r l := by
    ext r l; rfl
  rw [this, det_mul_column]; ring

/-- Coefficient of `Q_{m+1}(v)`: `C_L = (-1)^(2m+1) (-1)^(m+1) (∏ -x) · P_{m+1}(w)`. -/
theorem cramerO_QL (m : ℕ) (x y : Fin (2 * m + 3) → R) (i : Fin (2 * m + 3)) :
    cramerCoef (subRowsOdd m x y i) (elimO m) (Fin.last _) =
      (-1) ^ (2 * m + 1) * (-1) ^ (m + 1) *
        crossVec (subScaledX m x y i) ⟨m + 1, by omega⟩ := by
  refine cramerCoef_eq_crossVec _ _ _ _ ⟨m + 1, by omega⟩ (Fin.last _) (fun r => ?_) (fun r e => ?_)
  · have h := subRowsOdd_succ m x y i r (Fin.last _) (by simp only [Fin.val_last]; omega)
    have e1 : (Fin.last (2 * m + 3)) = (Fin.last (2 * m + 2)).succ := by ext; simp
    have e2 : (⟨m + 1, by omega⟩ : Fin (2 * m + 3)).succAbove (Fin.last (2 * m + 1)) =
        Fin.last (2 * m + 2) := by fin_idxO
    simp only [subScaledX, Matrix.of_apply]; rw [e1, e2]; exact h
  · have hv := val_succAbove (⟨m + 1, by omega⟩ : Fin (2 * m + 3)) ((Fin.last (2 * m + 1)).succAbove e)
    have hv2 : (((Fin.last (2 * m + 1)).succAbove e : Fin _) : ℕ) = e := by simp
    have hne : (((⟨m + 1, by omega⟩ : Fin (2 * m + 3)).succAbove
        ((Fin.last (2 * m + 1)).succAbove e) : Fin _) : ℕ) ≠ m + 1 := by
      rw [hv, hv2]; simp only [Fin.val_mk]; split_ifs <;> omega
    have h := subRowsOdd_succ m x y i r _ hne
    simp only [subScaledX, Matrix.of_apply]
    rw [← h]; congr 1
    ext; simp only [Fin.val_succ, hv, hv2, elimO, Fin.val_mk]
    split_ifs <;> simp only [Fin.val_mk] at * <;> omega

end OddGen3

/-- Field-level finish of the odd step. -/
theorem stepOdd_alg {K : Type*} [Field K] (s t P Pb A B L a b l w0 wP wq wL z zb : K)
    (hs : s * s = 1) (ht : t * t = 1) (hP : P ≠ 0) (hPb : Pb ≠ 0) (h0 : w0 ≠ 0) (hwP : wP ≠ 0)
    (E1 : s * Pb * (A * wq - B * w0) + L * (t * P * wP) = 0)
    (E2 : s * P * (a * -wL - b * wP) + l * (t * Pb * w0) = 0)
    (hz : z * wP = -wL) (hzb : zb * w0 = wq) :
    a * A * z * zb - a * B * z - A * b * zb + B * b - L * l = 0 := by
  have h1 : s * P * wP * (a * z - b) = -(l * (t * Pb * w0)) := by
    linear_combination E2 + s * P * a * hz
  have h2 : s * Pb * w0 * (A * zb - B) = -(L * (t * P * wP)) := by
    linear_combination E1 + s * Pb * A * hzb
  have key : (s * P * wP * (a * z - b)) * (s * Pb * w0 * (A * zb - B)) =
      (l * (t * Pb * w0)) * (L * (t * P * wP)) := by rw [h1, h2]; ring
  have H : (P * Pb * wP * w0) * (a * A * z * zb - a * B * z - A * b * zb + B * b - L * l) = 0 := by
    linear_combination key - (P * Pb * wP * w0 * (a * z - b) * (A * zb - B)) * hs +
      (l * L * P * Pb * wP * w0) * ht
  exact (mul_eq_zero.1 H).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero hP hPb) hwP) h0)

/-- **The odd step in coordinates, general `m`** (this is `StepOdd (m+1)` with `oddCircleEq`
unfolded; parent `KP (2m+3)`, subfamily `KP (2m+2)`). -/
theorem stepOdd_core (m : ℕ) (c : Fin (2 * m + 3) → ℂ) (hc : ∀ k, c k ≠ 0) (i : Fin (2 * m + 3))
    (hP : crossVec (KP (2 * m + 2) (c ∘ i.succAbove) (fun k => conj ((c ∘ i.succAbove) k)))
      ⟨m + 1, by omega⟩ ≠ 0) :
    let v := crossVec (KP (2 * m + 3) c (fun k => conj (c k)))
    let z := levelPointN (2 * m + 2)
      (crossVec (KP (2 * m + 2) (c ∘ i.succAbove) (fun k => conj ((c ∘ i.succAbove) k))))
    conj (v 0) * v 0 * z * conj z - conj (v 0) * v ⟨m + 2, by omega⟩ * z -
      v 0 * conj (v ⟨m + 2, by omega⟩) * conj z +
      v ⟨m + 2, by omega⟩ * conj (v ⟨m + 2, by omega⟩) - v (Fin.last _) * conj (v (Fin.last _)) = 0 := by
  intro v z
  have hvd : crossVec (KP (2 * m + 3) c (fun k => conj (c k))) = v := rfl
  have E := stepOdd_cleared_gen m c (fun k => conj (c k)) i
  have CL := cramerO_QL m c (fun k => conj (c k)) i
  rw [crossVec_subScaledX] at CL
  rw [CL, hvd] at E
  simp only [subVecOdd] at E
  have hcomp : ((fun k => conj (c k)) ∘ i.succAbove) = fun k => conj ((c ∘ i.succAbove) k) := rfl
  rw [hcomp] at E
  set w := crossVec (KP (2 * m + 2) (c ∘ i.succAbove) (fun k => conj ((c ∘ i.succAbove) k))) with hw
  have hw0 : w 0 ≠ 0 := crossVec_even_P0_ne_zero m (c ∘ i.succAbove) hP
  have cP : conj (w ⟨m + 1, by omega⟩) = w 0 := conj_crossVec_even m (c ∘ i.succAbove)
  have cL : conj (w (Fin.last _)) = -w ⟨m + 2, by omega⟩ := conj_crossVec_even_Q m (c ∘ i.succAbove)
  have c0 : conj (w 0) = w ⟨m + 1, by omega⟩ := by rw [← cP, Complex.conj_conj]
  have c2 : conj (w ⟨m + 2, by omega⟩) = -w (Fin.last _) := by
    rw [← neg_neg (w ⟨m + 2, by omega⟩), ← cL, map_neg, Complex.conj_conj]
  have e : (⟨(2 * m + 2) / 2, by omega⟩ : Fin (2 * m + 2 + 1)) = ⟨m + 1, by omega⟩ := by
    ext; exact (by omega : (2 * m + 2) / 2 = m + 1)
  have hz : z * w ⟨m + 1, by omega⟩ = -w (Fin.last _) := by
    show levelPointN (2 * m + 2) w * _ = _
    rw [levelPointN, e, div_mul_cancel₀ _ hP]
  have hzb : conj z * w 0 = w ⟨m + 2, by omega⟩ := by
    have : conj z = w ⟨m + 2, by omega⟩ / w 0 := conj_levelPointN_even m (c ∘ i.succAbove)
    rw [this, div_mul_cancel₀ _ hw0]
  set Pb := ∏ r, conj (c (i.succAbove r)) with hPb
  set P := ∏ r, -c (i.succAbove r) with hPdef
  have h1 : (-1 : ℂ) ^ (2 * m + 2) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
  have hPc : conj P = Pb := by
    rw [hPdef, hPb, map_prod]; simp only [map_neg]
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin, h1, one_mul]
  have hPbc : conj Pb = P := by rw [← hPc, Complex.conj_conj]
  have hPne : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun r _ => neg_ne_zero.2 (hc _)
  have hPbne : Pb ≠ 0 := Finset.prod_ne_zero_iff.2 fun r _ => (map_ne_zero _).2 (hc _)
  have Ec := congrArg conj E
  simp only [map_add, map_mul, map_sub, map_pow, map_neg, map_one, map_zero, hPc, hPbc, c0, cP,
    cL, c2] at Ec
  set s : ℂ := (-1) ^ m
  set t : ℂ := (-1) ^ (2 * m + 1) * (-1) ^ (m + 1)
  have hs : s * s = 1 := by rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
  have ht : t * t = 1 := by
    simp only [t, ← pow_add]
    exact Even.neg_one_pow ⟨_, rfl⟩
  refine stepOdd_alg s t P Pb (v 0) (v ⟨m + 2, by omega⟩) (v (Fin.last _))
    (conj (v 0)) (conj (v ⟨m + 2, by omega⟩)) (conj (v (Fin.last _)))
    (w 0) (w ⟨m + 1, by omega⟩) (w ⟨m + 2, by omega⟩) (w (Fin.last _)) z (conj z)
    hs ht hPne hPbne hw0 hP ?_ ?_ hz hzb
  · linear_combination E
  · linear_combination Ec

/-- **`StepOdd (m+1)` for every `m`** (i.e. `StepOdd n` for all `n ≥ 1`). -/
theorem stepOdd_gen (m : ℕ) : StepOdd (m + 1) := by
  intro c hc i hP
  exact stepOdd_core m c hc i hP

/-- **Acceptance test.** -/
theorem stepOdd_three : StepOdd 3 := stepOdd_gen 2

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.cramerO_QL
#print axioms Clifford.MorleyKernel.stepOdd_core
#print axioms Clifford.MorleyKernel.stepOdd_gen
#print axioms Clifford.MorleyKernel.stepOdd_three

/-! ## Kernel circle is a generalized circle (Paper L / J11) -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate

/-- Scalar completed square: `|a|²|z|² - ā b z - a b̄ z̄ + |b|² - |c|² = |ā z - b̄|² - |c|²`. -/
theorem kernelCircle_scalar (a b c z : ℂ) :
    conj a * a * z * conj z - conj a * b * z - a * conj b * conj z + b * conj b - c * conj c =
      ((‖conj a * z - conj b‖ ^ 2 - ‖c‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  simp only [map_sub, map_mul, Complex.conj_conj]
  ring

/-- **Completed square, product form** (no hypothesis). -/
theorem kernelCircle_eq (m : ℕ) (v : Fin (2 * m + 2) → ℂ) (z : ℂ) :
    oddCircleEq m v z =
      ((‖conj (v 0) * z - conj (v ⟨m + 1, by omega⟩)‖ ^ 2 - ‖v (Fin.last _)‖ ^ 2 : ℝ) : ℂ) := by
  unfold oddCircleEq
  exact kernelCircle_scalar _ _ _ _

/-- **Completed square, metric form** (`v 0 ≠ 0`): centre `conj Q / conj P`, radius `‖QL‖/‖P‖`. -/
theorem kernelCircle_eq_dist (m : ℕ) (v : Fin (2 * m + 2) → ℂ) (hv0 : v 0 ≠ 0) (z : ℂ) :
    oddCircleEq m v z =
      ((‖v 0‖ ^ 2 * (dist z (conj (v ⟨m + 1, by omega⟩) / conj (v 0)) ^ 2 -
        (‖v (Fin.last _)‖ / ‖v 0‖) ^ 2) : ℝ) : ℂ) := by
  rw [kernelCircle_eq]
  congr 1
  have hc : conj (v 0) ≠ 0 := (map_ne_zero _).2 hv0
  have hn : ‖v 0‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  have h1 : conj (v 0) * z - conj (v ⟨m + 1, by omega⟩) =
      conj (v 0) * (z - conj (v ⟨m + 1, by omega⟩) / conj (v 0)) := by
    field_simp
  rw [h1, norm_mul, Complex.norm_conj, Complex.dist_eq]
  field_simp

/-- The zero set of the kernel circle is a metric sphere. -/
theorem kernelCircle_zeroSet (m : ℕ) (v : Fin (2 * m + 2) → ℂ) (hv0 : v 0 ≠ 0) :
    {z : ℂ | oddCircleEq m v z = 0} =
      Metric.sphere (conj (v ⟨m + 1, by omega⟩) / conj (v 0)) (‖v (Fin.last _)‖ / ‖v 0‖) := by
  ext z
  simp only [Set.mem_setOf_eq, Metric.mem_sphere]
  rw [kernelCircle_eq_dist m v hv0, Complex.ofReal_eq_zero]
  have hn : 0 < ‖v 0‖ := norm_pos_iff.2 hv0
  have hd := dist_nonneg (x := z) (y := conj (v ⟨m + 1, by omega⟩) / conj (v 0))
  have hr : 0 ≤ ‖v (Fin.last _)‖ / ‖v 0‖ := div_nonneg (norm_nonneg _) hn.le
  constructor
  · intro h
    have h2 : dist z (conj (v ⟨m + 1, by omega⟩) / conj (v 0)) ^ 2 =
        (‖v (Fin.last _)‖ / ‖v 0‖) ^ 2 := by
      have := (mul_eq_zero.1 h).resolve_left (by positivity)
      linarith
    exact (pow_left_inj₀ hd hr two_ne_zero).1 h2
  · intro h
    rw [h]; ring

/-- **Target A.** The kernel circle is a generalized circle on the sphere. -/
theorem kernelCircle_isGCircleS (m : ℕ) (v : Fin (2 * m + 2) → ℂ) (hv0 : v 0 ≠ 0) :
    Clifford.IsGCircleS (((↑) : ℂ → OnePoint ℂ) '' {z : ℂ | oddCircleEq m v z = 0}) := by
  left
  exact ⟨_, _, by rw [kernelCircle_zeroSet m v hv0]⟩

/-- **Target B** (with the non-degeneracy hypotheses `StepOdd` / Target A need). -/
theorem hodd_levelPoint (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (hd : ∀ j, d j ≠ 0)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0)
    (hPi : ∀ i : Fin (2 * k + 5),
      crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)))
        ⟨k + 2, by omega⟩ ≠ 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * k + 5),
        (levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
          (fun r => conj ((d ∘ i.succAbove) r)))) : OnePoint ℂ) ∈ Y := by
  refine ⟨((↑) : ℂ → OnePoint ℂ) ''
    {z : ℂ | oddCircleEq (k + 2) (crossVec (KP (2 * k + 5) d (fun j => conj (d j)))) z = 0},
    kernelCircle_isGCircleS (k + 2) _ hP0, fun i => ⟨_, ?_, rfl⟩⟩
  exact stepOdd_gen (k + 1) d hd i (hPi i)

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.kernelCircle_eq
#print axioms Clifford.MorleyKernel.kernelCircle_eq_dist
#print axioms Clifford.MorleyKernel.kernelCircle_isGCircleS
#print axioms Clifford.MorleyKernel.hodd_levelPoint

/-! ## The point `E` as the numbered level point; the `n = 4` base case (Paper L / J12) -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate

/-- The point `E` of `cliffordChainS_all_of`: the level point `-Q_last / P_{n/2}` read off the
polynomial cross vector of the `n` circles, pushed to the Riemann sphere. -/
noncomputable def Ept (n : ℕ) (c : Fin n → ℂ) : OnePoint ℂ :=
  ((levelPointN n (crossVec (KP n c (fun j => conj (c j)))) : ℂ) : OnePoint ℂ)

/-- Under `GenPosN` the `P₂` coordinate of four circles is nonzero (it is `mD`). -/
theorem crossVec_KP4_P2_ne_zero (c : Fin 4 → ℂ) (h : GenPosN c) :
    crossVec (KP 4 c (fun k => conj (c k))) ⟨2, by omega⟩ ≠ 0 := by
  have e : (⟨2, by omega⟩ : Fin 5) = 2 := rfl
  rw [e, crossVec_KP4_P2]
  exact h.pos4.mD_ne_zero

/-- At `n = 4` the level point is the Miquel point. -/
theorem Ept_four (c : Fin 4 → ℂ) (h : GenPosN c) :
    Ept 4 c = ((miquel (c 0) (c 1) (c 2) (c 3) : ℂ) : OnePoint ℂ) := by
  unfold Ept
  rw [levelPointN_four_cross c (crossVec_KP4_P2_ne_zero c h)]

/-- **Target A.** The `h4` hypothesis of `cliffordChainS_all_of` for `E := Ept`. -/
theorem h4_pt (c : Fin 4 → ℂ) (h : GenPosN c) : ChainS 4 c {Ept 4 c} := by
  rw [Ept_four c h]
  exact chain4_ofS c h.pos4

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.crossVec_KP4_P2_ne_zero
#print axioms Clifford.MorleyKernel.Ept_four
#print axioms Clifford.MorleyKernel.h4_pt

/-! ## The even payload (Paper L / J12, Target B) -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate

/-- **Target B.** The `heven` payload for `E := Ept`, one removed index `i` at a time. The witness
is the kernel circle of the `(2k+5)`-subfamily `c ∘ i.succAbove`: `stepEven_gen` puts the parent's
level point on it, `stepOdd_gen` puts each level point of the double subfamilies on it.
Non-degeneracy owed to the parent level:
* `hPc`  — the middle coordinate `P_{k+3}` of the parent's cross vector (needed by `StepEven`);
* `hP0`  — the `P₀` coordinate of the subfamily's cross vector (makes the kernel circle a circle);
* `hPij` — the middle coordinate `P_{k+2}` of every double subfamily (needed by `StepOdd`). -/
theorem heven_levelPoint (k : ℕ) (c : Fin (2 * k + 6) → ℂ) (hc : ∀ j, c j ≠ 0)
    (hPc : crossVec (KP (2 * k + 6) c (fun j => conj (c j))) ⟨k + 3, by omega⟩ ≠ 0)
    (i : Fin (2 * k + 6))
    (hP0 : crossVec (KP (2 * k + 5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 ≠ 0)
    (hPij : ∀ j : Fin (2 * k + 5),
      crossVec (KP (2 * k + 4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k + 2, by omega⟩ ≠ 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧ Ept (2 * k + 6) c ∈ Y ∧
      ∀ j : Fin (2 * k + 5), Ept (2 * k + 4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y := by
  refine ⟨((↑) : ℂ → OnePoint ℂ) ''
    {z : ℂ | oddCircleEq (k + 2) (crossVec (KP (2 * k + 5) (c ∘ i.succAbove)
      (fun r => conj ((c ∘ i.succAbove) r)))) z = 0},
    kernelCircle_isGCircleS (k + 2) _ hP0, ⟨_, ?_, rfl⟩, fun j => ⟨_, ?_, rfl⟩⟩
  · exact stepEven_gen (k + 2) (by omega) c hc hPc i
  · exact stepOdd_gen (k + 1) (c ∘ i.succAbove) (fun r => hc _) j (hPij j)

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.heven_levelPoint

/-! ## J13 — the degenerate case `P₀ = 0`

Five explicit Gaussian-rational centres `c5` in general position whose parent kernel coordinate
`P₀ = crossVec (KP 5 c5 c̄) 0` vanishes (so the kernel circle is not a real circle), and the
five subfamily level points are nevertheless exactly collinear: they lie on the line branch of
`IsGCircleS`. All checks are exact rational arithmetic, discharged by `norm_num` (kernel-checked). -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- The five centres (on the radial cubic `z²z̄ - z z̄² - z̄² + 7/2 z z̄ - z² = 0`). -/
noncomputable def c5 : Fin 5 → ℂ
  | 0 => ⟨-203/100,      609/400⟩
  | 1 => ⟨-1659/676,    2765/2704⟩
  | 2 => ⟨-2667/1156,    1778/1445⟩
  | 3 => ⟨-6483/2500,  15127/20000⟩
  | 4 => ⟨-6051/3364,   10085/5887⟩

theorem j13_mk_add (a b c d : ℝ) : (⟨a, b⟩ : ℂ) + ⟨c, d⟩ = ⟨a + c, b + d⟩ := rfl
theorem j13_mk_sub (a b c d : ℝ) : (⟨a, b⟩ : ℂ) - ⟨c, d⟩ = ⟨a - c, b - d⟩ := rfl
theorem j13_mk_neg (a b : ℝ) : -(⟨a, b⟩ : ℂ) = ⟨-a, -b⟩ := rfl
theorem j13_mk_conj (a b : ℝ) : conj (⟨a, b⟩ : ℂ) = ⟨a, -b⟩ := rfl
theorem j13_one : (1 : ℂ) = ⟨1, 0⟩ := rfl
theorem j13_zero : (0 : ℂ) = ⟨0, 0⟩ := rfl
theorem j13_mk_eq_zero (a b : ℝ) : ((⟨a, b⟩ : ℂ) = 0) ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl
theorem j13_ofReal (t : ℝ) : ((t : ℝ) : ℂ) = ⟨t, 0⟩ := rfl
theorem j13_mk_eq (a b c d : ℝ) : ((⟨a, b⟩ : ℂ) = ⟨c, d⟩) ↔ a = c ∧ b = d := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- `c5` is in general position: 10 transversal pairs, 10 general triples (exact). -/
theorem c5_genPosN : GenPosN c5 := by
  refine ⟨fun i j hij => ?_, fun i j k hij hjk => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij <;>
      simp only [Transversal, c5, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
      norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [Fin.lt_def] at hij hjk <;>
      simp only [GenTriple, triP, cycP, det3, c5, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Fin.isValue] <;>
      norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- The real kernel vector `(1, -1, 1, -7/2, 1)` of the columns `1 … 5` of `KP 5 c5 c̄`. -/
theorem KP5_c5_sub_mulVec :
    (KP 5 c5 (fun j => conj (c5 j))).submatrix id (Fin.succAbove 0) *ᵥ ![1, -1, 1, ⟨-7/2, 0⟩, 1] = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_five, submatrix_apply, id]
  fin_cases k <;>
    simp [KP, Fin.succAbove, c5] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- `P₀ = 0` for `c5` (exact). -/
theorem c5_P0_zero : crossVec (KP 5 c5 (fun j => conj (c5 j))) 0 = 0 := by
  have h := Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, by
    intro h0; have := congrFun h0 0; norm_num at this, KP5_c5_sub_mulVec⟩
  show (-1 : ℂ) ^ ((0 : Fin 6) : ℕ) * _ = 0
  rw [h, mul_zero]

/-- **Target A.** General position does not exclude `P₀ = 0`. -/
theorem genpos_p0_zero :
    GenPosN c5 ∧ crossVec (KP 5 c5 (fun j => conj (c5 j))) 0 = 0 :=
  ⟨c5_genPosN, c5_P0_zero⟩

/-- The five subfamily level points. -/
noncomputable def z5 (i : Fin 5) : ℂ :=
  levelPointN 4 (crossVec (KP 4 (c5 ∘ i.succAbove) (fun r => conj ((c5 ∘ i.succAbove) r))))

/-- The direction `z5 1 - z5 0`. -/
noncomputable def d5 : ℂ := ⟨1338280704/1510120625, -2094646272/1510120625⟩

/-- The line parameters. -/
noncomputable def t5 : Fin 5 → ℝ := ![0, 1, 75231/109888, 2200/1717, -4561/6464]

theorem z5_eq_div (i : Fin 5) :
    z5 i = mN (c5 (i.succAbove 0)) (c5 (i.succAbove 1)) (c5 (i.succAbove 2)) (c5 (i.succAbove 3))
        (conj (c5 (i.succAbove 0))) (conj (c5 (i.succAbove 1))) (conj (c5 (i.succAbove 2)))
        (conj (c5 (i.succAbove 3))) /
      mD (c5 (i.succAbove 0)) (c5 (i.succAbove 1)) (c5 (i.succAbove 2)) (c5 (i.succAbove 3))
        (conj (c5 (i.succAbove 0))) (conj (c5 (i.succAbove 1))) (conj (c5 (i.succAbove 2)))
        (conj (c5 (i.succAbove 3))) := by
  have e2 : (⟨4 / 2, by omega⟩ : Fin 5) = 2 := rfl
  have e4 : (Fin.last 4 : Fin 5) = 4 := rfl
  rw [z5, levelPointN, e2, e4, crossVec_KP4_P2, crossVec_KP4_Q1, neg_neg]
  rfl

theorem z5_0 : z5 0 = ⟨-7761586179/2053764050, 8291450736/1026882025⟩ := by
  have s0 : ((0 : Fin 5).succAbove 0) = 1 := rfl
  have s1 : ((0 : Fin 5).succAbove 1) = 2 := rfl
  have s2 : ((0 : Fin 5).succAbove 2) = 3 := rfl
  have s3 : ((0 : Fin 5).succAbove 3) = 4 := rfl
  have hD : mD (c5 1) (c5 2) (c5 3) (c5 4) (conj (c5 1)) (conj (c5 2))
      (conj (c5 3)) (conj (c5 4)) = ⟨-15328839556350826871211/930857218884944000000000, 5109794837980110143019/116357152360618000000000⟩ := by
    simp only [mD, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  have hN : mN (c5 1) (c5 2) (c5 3) (c5 4) (conj (c5 1)) (conj (c5 2))
      (conj (c5 3)) (conj (c5 4)) = ⟨-544274485165115136240039/1861714437769888000000000, -69564653736513414378669/232714304721236000000000⟩ := by
    simp only [mN, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  rw [z5_eq_div, s0, s1, s2, s3, hD, hN, div_eq_iff (by rw [ne_eq, j13_zero, j13_mk_eq]; norm_num)]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem z5_1 : z5 1 = ⟨-878923731/303811250, 1015841904/151905625⟩ := by
  have s0 : ((1 : Fin 5).succAbove 0) = 0 := rfl
  have s1 : ((1 : Fin 5).succAbove 1) = 2 := rfl
  have s2 : ((1 : Fin 5).succAbove 2) = 3 := rfl
  have s3 : ((1 : Fin 5).succAbove 3) = 4 := rfl
  have hD : mD (c5 0) (c5 2) (c5 3) (c5 4) (conj (c5 0)) (conj (c5 2))
      (conj (c5 3)) (conj (c5 4)) = ⟨407973016489575537/8263666000000000000, -73359753498125523/1032958250000000000⟩ := by
    simp only [mD, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  have hN : mN (c5 0) (c5 2) (c5 3) (c5 4) (conj (c5 0)) (conj (c5 2))
      (conj (c5 3)) (conj (c5 4)) = ⟨27443796795798760377/82636660000000000000, 27663006177793159173/51647912500000000000⟩ := by
    simp only [mN, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  rw [z5_eq_div, s0, s1, s2, s3, hD, hN, div_eq_iff (by rw [ne_eq, j13_zero, j13_mk_eq]; norm_num)]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem z5_2 : z5 2 = ⟨-563628387/177661250, 632899008/88830625⟩ := by
  have s0 : ((2 : Fin 5).succAbove 0) = 0 := rfl
  have s1 : ((2 : Fin 5).succAbove 1) = 1 := rfl
  have s2 : ((2 : Fin 5).succAbove 2) = 3 := rfl
  have s3 : ((2 : Fin 5).succAbove 3) = 4 := rfl
  have hD : mD (c5 0) (c5 1) (c5 3) (c5 4) (conj (c5 0)) (conj (c5 1))
      (conj (c5 3)) (conj (c5 4)) = ⟨133736311334862621/2786296916000000000, -951206751182594313/11145187664000000000⟩ := by
    simp only [mD, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  have hN : mN (c5 0) (c5 1) (c5 3) (c5 4) (conj (c5 0)) (conj (c5 1))
      (conj (c5 3)) (conj (c5 4)) = ⟨63500432191089769953/139314845800000000000, 68290623706174849287/111451876640000000000⟩ := by
    simp only [mN, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  rw [z5_eq_div, s0, s1, s2, s3, hD, hN, div_eq_iff (by rw [ne_eq, j13_zero, j13_mk_eq]; norm_num)]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem z5_3 : z5 3 = ⟨-12775371/4832386, 15215088/2416193⟩ := by
  have s0 : ((3 : Fin 5).succAbove 0) = 0 := rfl
  have s1 : ((3 : Fin 5).succAbove 1) = 1 := rfl
  have s2 : ((3 : Fin 5).succAbove 2) = 2 := rfl
  have s3 : ((3 : Fin 5).succAbove 3) = 4 := rfl
  have hD : mD (c5 0) (c5 1) (c5 2) (c5 4) (conj (c5 0)) (conj (c5 1))
      (conj (c5 2)) (conj (c5 4)) = ⟨-6211944865410669/421202361486400000, 1776145616237223/105300590371600000⟩ := by
    simp only [mD, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  have hN : mN (c5 0) (c5 1) (c5 2) (c5 4) (conj (c5 0)) (conj (c5 1))
      (conj (c5 2)) (conj (c5 4)) = ⟨-56631980362389201/842404722972800000, -28949907183176133/210601180743200000⟩ := by
    simp only [mN, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  rw [z5_eq_div, s0, s1, s2, s3, hD, hN, div_eq_iff (by rw [ne_eq, j13_zero, j13_mk_eq]; norm_num)]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem z5_4 : z5 4 = ⟨-268900779/61051250, 276351936/30525625⟩ := by
  have s0 : ((4 : Fin 5).succAbove 0) = 0 := rfl
  have s1 : ((4 : Fin 5).succAbove 1) = 1 := rfl
  have s2 : ((4 : Fin 5).succAbove 2) = 2 := rfl
  have s3 : ((4 : Fin 5).succAbove 3) = 3 := rfl
  have hD : mD (c5 0) (c5 1) (c5 2) (c5 3) (conj (c5 0)) (conj (c5 1))
      (conj (c5 2)) (conj (c5 3)) = ⟨143028594000595611/45873909250000000000, -4650596404928457291/366991274000000000000⟩ := by
    simp only [mD, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  have hN : mN (c5 0) (c5 1) (c5 2) (c5 3) (conj (c5 0)) (conj (c5 1))
      (conj (c5 2)) (conj (c5 3)) = ⟨46328261856738378363/458739092500000000000, 1542121297914967278201/18349563700000000000000⟩ := by
    simp only [mN, det4, det3, c5]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  rw [z5_eq_div, s0, s1, s2, s3, hD, hN, div_eq_iff (by rw [ne_eq, j13_zero, j13_mk_eq]; norm_num)]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem d5_eq : d5 = z5 1 - z5 0 := by
  rw [z5_0, z5_1, d5]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem d5_ne_zero : d5 ≠ 0 := by
  rw [d5, ne_eq, j13_zero, j13_mk_eq]; norm_num

/-- **Target B.** For the degenerate family `c5` (`P₀ = 0`) the five subfamily level points are
exactly collinear: `z5 i = z5 0 + t5 i * d5`. -/
theorem p0_levelpts_collinear :
    ∀ i : Fin 5, z5 i = z5 0 + ((t5 i : ℝ) : ℂ) * d5 := by
  intro i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, z5_0, z5_1, z5_2, z5_3, z5_4,
      t5, d5, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, j13_ofReal] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- The same statement in the brief's literal form (no auxiliary `z5`). -/
theorem p0_levelpts_collinear' :
    ∀ i : Fin 5,
      levelPointN 4 (crossVec (KP 4 (c5 ∘ i.succAbove) (fun r => conj ((c5 ∘ i.succAbove) r)))) =
        levelPointN 4 (crossVec (KP 4 (c5 ∘ (0 : Fin 5).succAbove)
          (fun r => conj ((c5 ∘ (0 : Fin 5).succAbove) r)))) + ((t5 i : ℝ) : ℂ) * d5 :=
  p0_levelpts_collinear

/-- **Packaging.** The five level points lie on one generalized circle of the sphere — the *line*
branch of `IsGCircleS` (`Or.inr`, `lineS (z5 0) d5`). -/
theorem p0_levelpts_gcircleS :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧ ∀ i, ((z5 i : ℂ) : OnePoint ℂ) ∈ Y := by
  refine ⟨Clifford.lineS (z5 0) d5, Or.inr ⟨z5 0, d5, d5_ne_zero, rfl⟩, fun i => ?_⟩
  refine Set.mem_insert_of_mem _ ⟨z5 i, ⟨t5 i, ?_⟩, rfl⟩
  rw [Complex.real_smul]
  exact p0_levelpts_collinear i

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.j13_mk_add
#print axioms Clifford.MorleyKernel.j13_mk_sub
#print axioms Clifford.MorleyKernel.j13_mk_neg
#print axioms Clifford.MorleyKernel.j13_mk_conj
#print axioms Clifford.MorleyKernel.j13_one
#print axioms Clifford.MorleyKernel.j13_zero
#print axioms Clifford.MorleyKernel.j13_mk_eq_zero
#print axioms Clifford.MorleyKernel.j13_ofReal
#print axioms Clifford.MorleyKernel.j13_mk_eq
#print axioms Clifford.MorleyKernel.c5_genPosN
#print axioms Clifford.MorleyKernel.KP5_c5_sub_mulVec
#print axioms Clifford.MorleyKernel.c5_P0_zero
#print axioms Clifford.MorleyKernel.genpos_p0_zero
#print axioms Clifford.MorleyKernel.z5_eq_div
#print axioms Clifford.MorleyKernel.z5_0
#print axioms Clifford.MorleyKernel.z5_1
#print axioms Clifford.MorleyKernel.z5_2
#print axioms Clifford.MorleyKernel.z5_3
#print axioms Clifford.MorleyKernel.z5_4
#print axioms Clifford.MorleyKernel.d5_eq
#print axioms Clifford.MorleyKernel.d5_ne_zero
#print axioms Clifford.MorleyKernel.p0_levelpts_collinear
#print axioms Clifford.MorleyKernel.p0_levelpts_collinear'
#print axioms Clifford.MorleyKernel.p0_levelpts_gcircleS
#check @Clifford.MorleyKernel.genpos_p0_zero
#check @Clifford.MorleyKernel.p0_levelpts_collinear
#check @Clifford.MorleyKernel.p0_levelpts_collinear'
#check @Clifford.MorleyKernel.p0_levelpts_gcircleS

/-! ## The projective level point; the exact `n = 6` middle-coordinate witness (Paper L / J14) -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- Six centres on `x y² + x² y − y² + 3xy − x² = 0` (`x = z`, `y = z̄`). -/
noncomputable def c6 : Fin 6 → ℂ
  | 0 => ⟨-89/50,     -178/75⟩
  | 1 => ⟨-745/338,   -894/169⟩
  | 2 => ⟨-1189/578,  -17835/4624⟩
  | 3 => ⟨-2929/1250, -35148/4375⟩
  | 4 => ⟨-2605/1682, -10941/6728⟩
  | 5 => ⟨-8081/3362, -161620/15129⟩

/-- `c6` is in general position: 15 transversal pairs, 20 general triples (exact). -/
theorem c6_genPosN : GenPosN c6 := by
  refine ⟨fun i j hij => ?_, fun i j k hij hjk => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij <;>
      simp only [Transversal, c6, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
      norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [Fin.lt_def] at hij hjk <;>
      simp only [GenTriple, triP, cycP, det3, c6, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Fin.isValue] <;>
      norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- The real kernel vector `(0, -1, 1, 1, 3, 1)` of `KP 6 c6 c̄` with column 3 dropped
(columns `y³, −xy², x²y, −y², xy, −x²`). -/
theorem KP6_c6_sub_mulVec :
    (KP 6 c6 (fun j => conj (c6 j))).submatrix id (Fin.succAbove (⟨3, by omega⟩ : Fin 7)) *ᵥ
      ![0, -1, 1, 1, ⟨3, 0⟩, 1] = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_six, submatrix_apply, id]
  fin_cases k <;>
    simp [KP, Fin.succAbove, c6] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- The middle coordinate `P₃` vanishes for `c6` (exact). -/
theorem c6_P3_zero : crossVec (KP 6 c6 (fun j => conj (c6 j))) ⟨3, by omega⟩ = 0 := by
  have h := Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, by
    intro h0; have := congrFun h0 1; norm_num at this, KP6_c6_sub_mulVec⟩
  show (-1 : ℂ) ^ (3 : ℕ) * _ = 0
  rw [h, mul_zero]

/-- **Target A.** General position does not exclude `P_{n/2} = 0` at `n = 6`. -/
theorem genpos_mid_zero :
    GenPosN c6 ∧ crossVec (KP 6 c6 (fun j => conj (c6 j))) ⟨3, by omega⟩ = 0 :=
  ⟨c6_genPosN, c6_P3_zero⟩

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.c6_genPosN
#print axioms Clifford.MorleyKernel.KP6_c6_sub_mulVec
#print axioms Clifford.MorleyKernel.c6_P3_zero
#print axioms Clifford.MorleyKernel.genpos_mid_zero
#check @Clifford.MorleyKernel.genpos_mid_zero

/-! ## The projective level point `EptInf` (Paper L / J14, Target B) -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate

/-- The projective level point `[-v_last : v_{n/2}]`, `v = crossVec (KP n c c̄)`, on the Riemann
sphere: a vanishing middle coordinate is sent to `∞`. -/
noncomputable def EptInf (n : ℕ) (c : Fin n → ℂ) : OnePoint ℂ :=
  if crossVec (KP n c (fun j => conj (c j))) ⟨n / 2, by omega⟩ = 0 then OnePoint.infty
  else ((levelPointN n (crossVec (KP n c (fun j => conj (c j)))) : ℂ) : OnePoint ℂ)

theorem EptInf_eq_infty (n : ℕ) (c : Fin n → ℂ)
    (h : crossVec (KP n c (fun j => conj (c j))) ⟨n / 2, by omega⟩ = 0) :
    EptInf n c = OnePoint.infty := if_pos h

theorem EptInf_eq_coe (n : ℕ) (c : Fin n → ℂ)
    (h : crossVec (KP n c (fun j => conj (c j))) ⟨n / 2, by omega⟩ ≠ 0) :
    EptInf n c = Ept n c := if_neg h

/-- At the `n = 6` witness `c6` the projective level point is `∞`. -/
theorem EptInf_c6 : EptInf 6 c6 = OnePoint.infty :=
  EptInf_eq_infty 6 c6 c6_P3_zero

/-- **Target B.** The `h4` hypothesis of `cliffordChainS_all_of` for `E := EptInf`. -/
theorem h4_pt_inf (c : Fin 4 → ℂ) (h : GenPosN c) : ChainS 4 c {EptInf 4 c} := by
  rw [EptInf_eq_coe 4 c (crossVec_KP4_P2_ne_zero c h)]
  exact h4_pt c h

/-- Under `GenPosN` (with `n ≥ 2`) no centre is `0`. -/
theorem hc_of_genPos {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ) (h : GenPosN c) (j : Fin n) :
    c j ≠ 0 := by
  intro h0
  obtain ⟨i, hij⟩ : ∃ i : Fin n, i ≠ j := by
    by_cases hj : (j : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
  have := h.1 i j hij
  simp [Transversal, h0] at this

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.EptInf_eq_infty
#print axioms Clifford.MorleyKernel.EptInf_eq_coe
#print axioms Clifford.MorleyKernel.EptInf_c6
#print axioms Clifford.MorleyKernel.h4_pt_inf
#print axioms Clifford.MorleyKernel.hc_of_genPos
#check @Clifford.MorleyKernel.EptInf
#check @Clifford.MorleyKernel.EptInf_eq_coe
#check @Clifford.MorleyKernel.h4_pt_inf
#check @Clifford.MorleyKernel.hc_of_genPos

/-! ## J15 — `P₀ = 0` for arbitrary centres (Paper L / J15) -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- With `v 0 = 0` the kernel-circle equation is constant in `z`. -/
theorem oddCircleEq_of_P0_zero (m : ℕ) (v : Fin (2 * m + 2) → ℂ) (h : v 0 = 0) (z : ℂ) :
    oddCircleEq m v z = v ⟨m + 1, by omega⟩ * conj (v ⟨m + 1, by omega⟩) -
      v (Fin.last _) * conj (v (Fin.last _)) := by
  simp only [oddCircleEq, h, map_zero, zero_mul, mul_zero, sub_zero, zero_add]

/-- Plücker at `P₀ = 0`: `|w_{m+1}|² = |w_last|²` for the cross vector of `2m+1` centres. -/
theorem norm_Q0_eq_QL_sub (m : ℕ) (hm : 1 ≤ m) (x : Fin (2 * m + 2) → ℂ) (i : Fin (2 * m + 2))
    (h0 : crossVec (KP (2 * m + 1) (x ∘ i.succAbove) (fun k => conj ((x ∘ i.succAbove) k))) 0 = 0) :
    crossVec (KP (2 * m + 1) (x ∘ i.succAbove) (fun k => conj ((x ∘ i.succAbove) k))) ⟨m + 1, by omega⟩ *
        conj (crossVec (KP (2 * m + 1) (x ∘ i.succAbove) (fun k => conj ((x ∘ i.succAbove) k))) ⟨m + 1, by omega⟩) -
      crossVec (KP (2 * m + 1) (x ∘ i.succAbove) (fun k => conj ((x ∘ i.succAbove) k))) (Fin.last _) *
        conj (crossVec (KP (2 * m + 1) (x ∘ i.succAbove) (fun k => conj ((x ∘ i.succAbove) k))) (Fin.last _)) = 0 := by
  have P := plucker_odd m hm x (fun k => conj (x k)) i
  have C2 := conj_subVec_Q0 m x i
  have CL := conj_crossVec_odd_last m (x ∘ i.succAbove)
  have e : ((fun k => conj (x k)) ∘ i.succAbove) = fun k => conj ((x ∘ i.succAbove) k) := rfl
  simp only [subVec, e] at P C2
  rw [C2, CL]
  rw [h0, zero_mul, zero_add] at P
  linear_combination P


/-- **Target A (all `k`).** If `P₀ = 0`, every child level point satisfies the kernel-circle
equation — because with `P₀ = 0` that equation is the constant `‖Q₀‖² - ‖Q_last‖²`, which the odd
Plücker relation forces to be `0`. (So the identity holds for *every* `z`.) -/
theorem kernel_eq_zero_of_P0 (k : ℕ) (d : Fin (2 * k + 5) → ℂ)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 = 0) (z : ℂ) :
    oddCircleEq (k + 2) (crossVec (KP (2 * k + 5) d (fun j => conj (d j)))) z = 0 := by
  have hx : ((Fin.cons (0 : ℂ) d : Fin (2 * (k + 2) + 2) → ℂ) ∘ (0 : Fin (2 * (k + 2) + 2)).succAbove) = d := by
    funext j; simp
  have H := norm_Q0_eq_QL_sub (k + 2) (by omega) (Fin.cons (0 : ℂ) d) 0
  rw [hx] at H
  rw [oddCircleEq_of_P0_zero (k + 2) _ hP0]
  exact H hP0

theorem child_levelPt_kernel_line (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (hd : ∀ j, d j ≠ 0)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 = 0) :
    ∀ i : Fin (2 * k + 5),
      oddCircleEq (k + 2) (crossVec (KP (2 * k + 5) d (fun j => conj (d j))))
        (levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
          (fun r => conj ((d ∘ i.succAbove) r))))) = 0 :=
  fun _ => kernel_eq_zero_of_P0 k d hP0 _

/-- The `k = 0` instance (five arbitrary centres). -/
theorem child_levelPt_kernel_line_five (d : Fin 5 → ℂ) (hd : ∀ j, d j ≠ 0)
    (hP0 : crossVec (KP 5 d (fun j => conj (d j))) 0 = 0) :
    ∀ i : Fin 5,
      oddCircleEq 2 (crossVec (KP 5 d (fun j => conj (d j))))
        (levelPointN 4 (crossVec (KP 4 (d ∘ i.succAbove)
          (fun r => conj ((d ∘ i.succAbove) r))))) = 0 :=
  child_levelPt_kernel_line 0 d hd hP0


/-! ### Target B as stated is false: a counterexample with `P₀ = 0` and nonzero centres

`dX` has `P₀ = k3 = 0`, but its first four centres have `mD = 0` (they are the inverses of four
tangent lines of one parabola), so the child level point for `i = 4` is `-Q₁/P₂ = x/0 = 0` by the
division convention. The child points `z₀, z₁, z₂, z₄` are not concyclic (`cD = 2/45 ≠ 0`). -/

noncomputable def dX : Fin 5 → ℂ
  | 0 => ⟨-1, 0⟩
  | 1 => ⟨-1/2, 1/2⟩
  | 2 => ⟨-1/5, 2/5⟩
  | 3 => ⟨-1/2, -1/2⟩
  | 4 => ⟨1, 2⟩

theorem dX_ne_zero : ∀ j, dX j ≠ 0 := by
  intro j; fin_cases j <;> simp only [dX, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, ne_eq, j13_mk_eq_zero] <;> norm_num

theorem dX_P0 : crossVec (KP 5 dX (fun j => conj (dX j))) 0 = 0 := by
  rw [crossVec_KP5_P0]
  simp only [k3, det5, det4, det3, dX]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- The level point of four circles as `mN / mD`, no hypothesis (`x / 0 = 0`). -/
theorem levelPointN_four_div (d : Fin 4 → ℂ) :
    levelPointN 4 (crossVec (KP 4 d (fun k => conj (d k)))) =
      mN (d 0) (d 1) (d 2) (d 3) (conj (d 0)) (conj (d 1)) (conj (d 2)) (conj (d 3)) /
        mD (d 0) (d 1) (d 2) (d 3) (conj (d 0)) (conj (d 1)) (conj (d 2)) (conj (d 3)) := by
  have e2 : (⟨4 / 2, by omega⟩ : Fin 5) = 2 := rfl
  have e4 : (Fin.last 4 : Fin 5) = 4 := rfl
  rw [levelPointN, e2, e4, crossVec_KP4_P2, crossVec_KP4_Q1, neg_neg]

theorem dX_z0 : levelPointN 4 (crossVec (KP 4 (dX ∘ (0 : Fin 5).succAbove)
    (fun r => conj ((dX ∘ (0 : Fin 5).succAbove) r)))) = ⟨-1/5, 2/5⟩ := by
  rw [levelPointN_four_div]
  simp only [Function.comp_apply]
  have s0 : ((0 : Fin 5).succAbove 0) = 1 := rfl
  have s1 : ((0 : Fin 5).succAbove 1) = 2 := rfl
  have s2 : ((0 : Fin 5).succAbove 2) = 3 := rfl
  have s3 : ((0 : Fin 5).succAbove 3) = 4 := rfl
  rw [s0, s1, s2, s3, div_eq_iff (by
    simp only [mD, det4, det3, dX]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero])]
  simp only [mN, mD, det4, det3, dX]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem dX_z1 : levelPointN 4 (crossVec (KP 4 (dX ∘ (1 : Fin 5).succAbove)
    (fun r => conj ((dX ∘ (1 : Fin 5).succAbove) r)))) = ⟨-7/15, 3/5⟩ := by
  rw [levelPointN_four_div]
  simp only [Function.comp_apply]
  have s0 : ((1 : Fin 5).succAbove 0) = 0 := rfl
  have s1 : ((1 : Fin 5).succAbove 1) = 2 := rfl
  have s2 : ((1 : Fin 5).succAbove 2) = 3 := rfl
  have s3 : ((1 : Fin 5).succAbove 3) = 4 := rfl
  rw [s0, s1, s2, s3, div_eq_iff (by
    simp only [mD, det4, det3, dX]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero])]
  simp only [mN, mD, det4, det3, dX]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem dX_z2 : levelPointN 4 (crossVec (KP 4 (dX ∘ (2 : Fin 5).succAbove)
    (fun r => conj ((dX ∘ (2 : Fin 5).succAbove) r)))) = ⟨-1, 1⟩ := by
  rw [levelPointN_four_div]
  simp only [Function.comp_apply]
  have s0 : ((2 : Fin 5).succAbove 0) = 0 := rfl
  have s1 : ((2 : Fin 5).succAbove 1) = 1 := rfl
  have s2 : ((2 : Fin 5).succAbove 2) = 3 := rfl
  have s3 : ((2 : Fin 5).succAbove 3) = 4 := rfl
  rw [s0, s1, s2, s3, div_eq_iff (by
    simp only [mD, det4, det3, dX]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero])]
  simp only [mN, mD, det4, det3, dX]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- The degenerate child: `mD = 0` for the first four centres. -/
theorem dX_mD4 : mD (dX 0) (dX 1) (dX 2) (dX 3) (conj (dX 0)) (conj (dX 1)) (conj (dX 2))
    (conj (dX 3)) = 0 := by
  simp only [mD, det4, det3, dX]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem dX_z4 : levelPointN 4 (crossVec (KP 4 (dX ∘ (4 : Fin 5).succAbove)
    (fun r => conj ((dX ∘ (4 : Fin 5).succAbove) r)))) = 0 := by
  rw [levelPointN_four_div]
  simp only [Function.comp_apply]
  have s0 : ((4 : Fin 5).succAbove 0) = 0 := rfl
  have s1 : ((4 : Fin 5).succAbove 1) = 1 := rfl
  have s2 : ((4 : Fin 5).succAbove 2) = 2 := rfl
  have s3 : ((4 : Fin 5).succAbove 3) = 3 := rfl
  rw [s0, s1, s2, s3, dX_mD4, div_zero]

theorem dX_cD : cD ⟨-1/5, 2/5⟩ ⟨-7/15, 3/5⟩ ⟨-1, 1⟩ 0 ≠ 0 := by
  simp only [cD, det4, det3, j13_zero]
  norm_num

/-- **Target B as stated is false**: its `k = 0` instance fails at `dX`. -/
theorem p0_children_gcircleS_false :
    ¬ ∀ (d : Fin (2 * 0 + 5) → ℂ), (∀ j, d j ≠ 0) →
      crossVec (KP (2 * 0 + 5) d (fun j => conj (d j))) 0 = 0 →
      ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
        ∀ i : Fin (2 * 0 + 5), (↑(levelPointN (2 * 0 + 4) (crossVec (KP (2 * 0 + 4) (d ∘ i.succAbove)
          (fun r => conj ((d ∘ i.succAbove) r))))) : OnePoint ℂ) ∈ Y := by
  intro H
  obtain ⟨Y, hY, hm⟩ := H dX dX_ne_zero dX_P0
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have h4 := hm 4
  rw [dX_z0] at h0
  rw [dX_z1] at h1
  rw [dX_z2] at h2
  rw [dX_z4] at h4
  exact dX_cD (Clifford.cD_eq_zeroS hY h0 h1 h2 h4)


/-! ### The corrected `k = 0` packaging: under `GenPosN` the five child level points lie on one
generalized circle (no `P₀` hypothesis needed; for `P₀ = 0` this is the line / one-point branch
of `clifford_two_clean`). -/

theorem levelPt_child_five (d : Fin 5 → ℂ) (h : GenPosN d) (i : Fin 5) :
    levelPointN 4 (crossVec (KP 4 (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)))) =
      miquel (d (i.succAbove 0)) (d (i.succAbove 1)) (d (i.succAbove 2)) (d (i.succAbove 3)) :=
  levelPointN_four_cross _ (crossVec_KP4_P2_ne_zero _ (h.comp_succAbove i))

theorem hodd_five (d : Fin 5 → ℂ) (h : GenPosN d) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin 5, (↑(levelPointN 4 (crossVec (KP 4 (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))))) : OnePoint ℂ) ∈ Y := by
  obtain ⟨Y, hY, hs⟩ := Clifford.exists_gcircleS (Clifford.clifford_two_clean h.pos5)
  refine ⟨Y, hY, fun i => hs ⟨_, ?_, rfl⟩⟩
  rw [levelPt_child_five d h i]
  fin_cases i <;> simp [Fin.succAbove, Fin.lt_def]

/-- **Target B, corrected (`k = 0`)**: with `GenPosN` in place of `∀ j, d j ≠ 0` the exact
`hodd` shape holds (the `P₀ = 0` hypothesis is then not needed). -/
theorem p0_children_gcircleS_genPos (d : Fin (2 * 0 + 5) → ℂ) (h : GenPosN d)
    (_hP0 : crossVec (KP (2 * 0 + 5) d (fun j => conj (d j))) 0 = 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * 0 + 5), (↑(levelPointN (2 * 0 + 4) (crossVec (KP (2 * 0 + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))))) : OnePoint ℂ) ∈ Y :=
  hodd_five d h

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.oddCircleEq_of_P0_zero
#print axioms Clifford.MorleyKernel.norm_Q0_eq_QL_sub
#print axioms Clifford.MorleyKernel.kernel_eq_zero_of_P0
#print axioms Clifford.MorleyKernel.child_levelPt_kernel_line
#print axioms Clifford.MorleyKernel.child_levelPt_kernel_line_five
#print axioms Clifford.MorleyKernel.dX_ne_zero
#print axioms Clifford.MorleyKernel.dX_P0
#print axioms Clifford.MorleyKernel.levelPointN_four_div
#print axioms Clifford.MorleyKernel.dX_z0
#print axioms Clifford.MorleyKernel.dX_z1
#print axioms Clifford.MorleyKernel.dX_z2
#print axioms Clifford.MorleyKernel.dX_mD4
#print axioms Clifford.MorleyKernel.dX_z4
#print axioms Clifford.MorleyKernel.dX_cD
#print axioms Clifford.MorleyKernel.p0_children_gcircleS_false
#print axioms Clifford.MorleyKernel.levelPt_child_five
#print axioms Clifford.MorleyKernel.hodd_five
#print axioms Clifford.MorleyKernel.p0_children_gcircleS_genPos
#check @Clifford.MorleyKernel.kernel_eq_zero_of_P0
#check @Clifford.MorleyKernel.child_levelPt_kernel_line
#check @Clifford.MorleyKernel.child_levelPt_kernel_line_five
#check @Clifford.MorleyKernel.p0_children_gcircleS_false
#check @Clifford.MorleyKernel.hodd_five
#check @Clifford.MorleyKernel.p0_children_gcircleS_genPos

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-! ## J17 Target A: seven exact centres with `P₀ = 0`, seven collinear child level points.

The centres lie on the real curve `z = -w B(w)/A(w)` (`|w| = 1`, `w = (1+it)/(1-it)`), with
`A = 1/w² + w²`, `B = (2-2i)/w³ + 1/w + w + (2+2i) w³`, `t = 1, 4, 3, 1/3, 0, -1/2, -2`;
on that curve the parent column-0 minor has the explicit kernel vector `ker7` below. -/

noncomputable def d7 : Fin 7 → ℂ
  | 0 => ⟨0, 2⟩
  | 1 => ⟨-226515/46529, 120808/46529⟩
  | 2 => ⟨-984/175, 738/175⟩
  | 3 => ⟨888/175, 666/175⟩
  | 4 => ⟨-3, 0⟩
  | 5 => ⟨-213/175, 284/175⟩
  | 6 => ⟨-741/175, -988/175⟩

/-- `d7` is in general position: 21 transversal pairs, 35 general triples (exact). -/
theorem d7_genPosN : GenPosN d7 := by
  refine ⟨fun i j hij => ?_, fun i j k hij hjk => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij <;>
      simp only [Transversal, d7, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
      norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [Fin.lt_def] at hij hjk <;>
      simp only [GenTriple, triP, cycP, det3, d7, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Fin.isValue] <;>
      norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- A nonzero kernel vector of the parent matrix with column `0` dropped. -/
noncomputable def ker7 : Fin 7 → ℂ := ![⟨-1/4, 1/4⟩, ⟨0, 0⟩, ⟨-1/4, 1/4⟩, ⟨0, 1⟩, ⟨1/4, -1/4⟩, ⟨-1/4, 1/4⟩, ⟨1, 0⟩]

theorem KP7_d7_sub_mulVec :
    (KP 7 d7 (fun j => conj (d7 j))).submatrix id (Fin.succAbove 0) *ᵥ ker7 = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_seven, submatrix_apply, id]
  fin_cases k <;>
    simp [KP, Fin.succAbove, d7, ker7] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- `P₀ = 0` for `d7` (exact). -/
theorem d7_P0 : crossVec (KP 7 d7 (fun j => conj (d7 j))) 0 = 0 := by
  have h := Matrix.exists_mulVec_eq_zero_iff.1 ⟨ker7, by
    intro h0; have := congrFun h0 6; simp [ker7, Complex.ext_iff] at this, KP7_d7_sub_mulVec⟩
  show (-1 : ℂ) ^ ((0 : Fin 8) : ℕ) * _ = 0
  rw [h, mul_zero]

/-- From an explicit kernel vector `w` with `w 3 = 1` and a left inverse of the column-3-dropped
minor: the middle coordinate is nonzero and the level point is `-w 6`. -/
theorem levelPointN_six_of_cert (A : Matrix (Fin 6) (Fin 7) ℂ) (w : Fin 7 → ℂ)
    (Binv : Matrix (Fin 6) (Fin 6) ℂ) (hw : A *ᵥ w = 0) (hw3 : w 3 = 1)
    (hB : Binv * A.submatrix id (Fin.succAbove 3) = 1) :
    crossVec A ⟨3, by omega⟩ ≠ 0 ∧ levelPointN 6 (crossVec A) = -w 6 := by
  have hdet : (A.submatrix id (Fin.succAbove 3)).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hB
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have h3 : crossVec A ⟨3, by omega⟩ ≠ 0 := by
    show (-1 : ℂ) ^ (3 : ℕ) * _ ≠ 0
    exact mul_ne_zero (by norm_num) hdet
  refine ⟨h3, ?_⟩
  have hk := ker_eq_span_crossVec A ⟨3, by omega⟩ h3
  have hmem : w ∈ LinearMap.ker A.mulVecLin := by simpa using hw
  rw [hk, Submodule.mem_span_singleton] at hmem
  obtain ⟨s, hs⟩ := hmem
  have e3 := congrFun hs 3
  have e6 := congrFun hs 6
  simp only [Pi.smul_apply, smul_eq_mul] at e3 e6
  have e : (⟨6 / 2, by omega⟩ : Fin 7) = 3 := rfl
  have el : (Fin.last 6 : Fin 7) = 6 := rfl
  rw [levelPointN, e, el]
  have h3' : crossVec A 3 ≠ 0 := h3
  rw [hw3] at e3
  rw [← e6, div_eq_iff h3']
  linear_combination crossVec A 6 * e3

/-- Child `0`: the matrix, a kernel vector and a left inverse of the `P₃`-minor. -/
noncomputable def A7_0 : Matrix (Fin 6) (Fin 7) ℂ := !![⟨-1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨-51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨-228040201/13446881, -54729648240/2164947841⟩, ⟨228040201/7491169, 0⟩, ⟨-228040201/13446881, 54729648240/2164947841⟩;
    ⟨655025184/5359375, -1741771512/5359375⟩, ⟨59547744/214375, 44660808/214375⟩, ⟨-59547744/214375, 44660808/214375⟩, ⟨-655025184/5359375, -1741771512/5359375⟩, ⟨-60516/4375, -1452384/30625⟩, ⟨60516/1225, 0⟩, ⟨-60516/4375, 1452384/30625⟩;
    ⟨-481406112/5359375, -1280102616/5359375⟩, ⟨-43764192/214375, 32823144/214375⟩, ⟨43764192/214375, 32823144/214375⟩, ⟨481406112/5359375, -1280102616/5359375⟩, ⟨-49284/4375, 1182816/30625⟩, ⟨49284/1225, 0⟩, ⟨-49284/4375, -1182816/30625⟩;
    ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-9, 0⟩, ⟨9, 0⟩, ⟨-9, 0⟩;
    ⟨41875587/5359375, -15748084/5359375⟩, ⟨1073733/214375, 1431644/214375⟩, ⟨-1073733/214375, 1431644/214375⟩, ⟨-41875587/5359375, -15748084/5359375⟩, ⟨5041/4375, -120984/30625⟩, ⟨5041/1225, 0⟩, ⟨5041/4375, 120984/30625⟩;
    ⟨1763099091/5359375, 663045812/5359375⟩, ⟨45207669/214375, -60276892/214375⟩, ⟨-45207669/214375, -60276892/214375⟩, ⟨-1763099091/5359375, 663045812/5359375⟩, ⟨61009/4375, 1464216/30625⟩, ⟨61009/1225, 0⟩, ⟨61009/4375, -1464216/30625⟩]

noncomputable def w7_0 : Fin 7 → ℂ := ![⟨-240/289, -161/289⟩, ⟨593227/541875, -67032/180625⟩, ⟨-126872/180625, -497483/541875⟩, ⟨1, 0⟩, ⟨3821762/541875, -499271/541875⟩, ⟨820249/541875, 249641/541875⟩, ⟨2895641/541875, 2543698/541875⟩]

noncomputable def B7_0 : Matrix (Fin 6) (Fin 6) ℂ := !![⟨-31121125214375/7212754665971712, 102255125704375/7212754665971712⟩, ⟨5359375/3625150464, -17609375/3625150464⟩, ⟨-765625/2498107392, 2515625/2498107392⟩, ⟨4375/663552, -14375/663552⟩, ⟨5359375/1114988544, -17609375/1114988544⟩, ⟨-765625/4498071552, 2515625/4498071552⟩;
    ⟨-1742783012005/225398583311616, 348556602401/84524468741856⟩, ⟨728875/169928928, -728875/226571904⟩, ⟨-111475/117098784, -111475/156131712⟩, ⟨539/62208, 0⟩, ⟨-265825/34843392, 265825/26132544⟩, ⟨42875/140564736, 42875/105423552⟩;
    ⟨-4431648230527/1967114908901376, 130139653896455/7212754665971712⟩, ⟨-3147025/3625150464, -86853725/10875451392⟩, ⟨6125/25233408, 2058875/7494322176⟩, ⟨4375/663552, -42341/1990656⟩, ⟨62726125/3344965632, -5947375/1114988544⟩, ⟨-9431275/13494214656, 75425/78913536⟩;
    ⟨-44508544106593/1967114908901376, -593947563891353/21638263997915136⟩, ⟨118965875/10875451392, 56037625/10875451392⟩, ⟨-75775/681302016, -47922175/7494322176⟩, ⟨-38629/1990656, 121129/1990656⟩, ⟨153814675/3344965632, 415570225/3344965632⟩, ⟨37464875/13494214656, -59770375/13494214656⟩;
    ⟨37523185258475/21638263997915136, -253685185947487/21638263997915136⟩, ⟨-44172275/10875451392, 43687175/10875451392⟩, ⟨41455925/7494322176, -6241025/7494322176⟩, ⟨38629/1990656, 35663/1990656⟩, ⟨458528525/3344965632, 43687175/3344965632⟩, ⟨50550325/13494214656, -328475/710221824⟩;
    ⟨112882545377581/5409565999478784, -370899791954909/5409565999478784⟩, ⟨-10776325/2718862848, 75434275/2718862848⟩, ⟨5579875/1873580544, -797125/1873580544⟩, ⟨-42733/497664, 42733/497664⟩, ⟨-2064125/836241408, -14448875/836241408⟩, ⟨15154475/3373553664, 2164925/3373553664⟩]

theorem A7_0_eq : KP 6 (d7 ∘ ((0 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((0 : Fin 7)).succAbove) r)) = A7_0 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [KP, Fin.succAbove, Fin.lt_def, d7, A7_0] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem A7_0_w : A7_0 *ᵥ w7_0 = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_seven]
  fin_cases k <;>
    simp [A7_0, w7_0] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem B7_0_inv : B7_0 * A7_0.submatrix id (Fin.succAbove 3) = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Fin.sum_univ_six, submatrix_apply, id]
  fin_cases k <;> fin_cases l <;>
    simp [A7_0, B7_0, Fin.succAbove, Fin.lt_def, Matrix.one_apply] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero] <;> rfl

theorem d7_child_0 :
    crossVec (KP 6 (d7 ∘ ((0 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((0 : Fin 7)).succAbove) r))) ⟨3, by omega⟩ ≠ 0 ∧
    levelPointN 6 (crossVec (KP 6 (d7 ∘ ((0 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((0 : Fin 7)).succAbove) r)))) = ⟨-2895641/541875, -2543698/541875⟩ := by
  rw [A7_0_eq]
  obtain ⟨h1, h2⟩ := levelPointN_six_of_cert A7_0 w7_0 B7_0 A7_0_w (by simp [w7_0]; rfl) B7_0_inv
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [w7_0, Matrix.cons_val]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- Child `1`: the matrix, a kernel vector and a left inverse of the `P₃`-minor. -/
noncomputable def A7_1 : Matrix (Fin 6) (Fin 7) ℂ := !![⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩;
    ⟨655025184/5359375, -1741771512/5359375⟩, ⟨59547744/214375, 44660808/214375⟩, ⟨-59547744/214375, 44660808/214375⟩, ⟨-655025184/5359375, -1741771512/5359375⟩, ⟨-60516/4375, -1452384/30625⟩, ⟨60516/1225, 0⟩, ⟨-60516/4375, 1452384/30625⟩;
    ⟨-481406112/5359375, -1280102616/5359375⟩, ⟨-43764192/214375, 32823144/214375⟩, ⟨43764192/214375, 32823144/214375⟩, ⟨481406112/5359375, -1280102616/5359375⟩, ⟨-49284/4375, 1182816/30625⟩, ⟨49284/1225, 0⟩, ⟨-49284/4375, -1182816/30625⟩;
    ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-9, 0⟩, ⟨9, 0⟩, ⟨-9, 0⟩;
    ⟨41875587/5359375, -15748084/5359375⟩, ⟨1073733/214375, 1431644/214375⟩, ⟨-1073733/214375, 1431644/214375⟩, ⟨-41875587/5359375, -15748084/5359375⟩, ⟨5041/4375, -120984/30625⟩, ⟨5041/1225, 0⟩, ⟨5041/4375, 120984/30625⟩;
    ⟨1763099091/5359375, 663045812/5359375⟩, ⟨45207669/214375, -60276892/214375⟩, ⟨-45207669/214375, -60276892/214375⟩, ⟨-1763099091/5359375, 663045812/5359375⟩, ⟨61009/4375, 1464216/30625⟩, ⟨61009/1225, 0⟩, ⟨61009/4375, -1464216/30625⟩]

noncomputable def w7_1 : Fin 7 → ℂ := ![⟨0, 1⟩, ⟨1483/1875, 392/625⟩, ⟨392/625, 1483/1875⟩, ⟨1, 0⟩, ⟨5318/1875, -2489/1875⟩, ⟨1261/1875, -1261/1875⟩, ⟨2489/1875, -5318/1875⟩]

noncomputable def B7_1 : Matrix (Fin 6) (Fin 6) ℂ := !![⟨-625/36864, -625/36864⟩, ⟨765625/1115430912, 765625/1115430912⟩, ⟨765625/908402688, 765625/908402688⟩, ⟨-625/82944, -625/82944⟩, ⟨765625/92915712, 765625/92915712⟩, ⟨765625/1124517888, 765625/1124517888⟩;
    ⟨0, -49/3456⟩, ⟨42875/26142912, -42875/34857216⟩, ⟨-8575/21290688, -8575/28387584⟩, ⟨-49/15552, 0⟩, ⟨-94325/5807232, 94325/4355424⟩, ⟨42875/70282368, 42875/52711776⟩;
    ⟨-2659/110592, -625/36864⟩, ⟨-743575/1115430912, -3739925/3346292736⟩, ⟨483875/302800896, -447125/2725208064⟩, ⟨-625/82944, -307/248832⟩, ⟨7784875/278747136, 2137625/92915712⟩, ⟨1199275/3373553664, 346675/374839296⟩;
    ⟨6239/110592, -1261/110592⟩, ⟨3019625/3346292736, -12684875/3346292736⟩, ⟨-3565975/2725208064, -10568075/2725208064⟩, ⟨-7193/248832, 3443/248832⟩, ⟨-1850975/278747136, 27651925/278747136⟩, ⟨4734625/3373553664, -9744875/3373553664⟩;
    ⟨1705/110592, 1261/110592⟩, ⟨-13691825/3346292736, -1544725/3346292736⟩, ⟨12650575/2725208064, -1544725/2725208064⟩, ⟨7193/248832, 1261/248832⟩, ⟨36660575/278747136, -1544725/278747136⟩, ⟨10318175/3373553664, -118825/259504128⟩;
    ⟨2267/27648, 2267/27648⟩, ⟨-111475/836573184, 780325/836573184⟩, ⟨-1757875/681302016, 251125/681302016⟩, ⟨-1091/62208, 1091/62208⟩, ⟨-1329125/69686784, -9303875/69686784⟩, ⟨317275/843388416, 45325/843388416⟩]

theorem A7_1_eq : KP 6 (d7 ∘ ((1 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((1 : Fin 7)).succAbove) r)) = A7_1 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [KP, Fin.succAbove, Fin.lt_def, d7, A7_1] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem A7_1_w : A7_1 *ᵥ w7_1 = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_seven]
  fin_cases k <;>
    simp [A7_1, w7_1] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem B7_1_inv : B7_1 * A7_1.submatrix id (Fin.succAbove 3) = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Fin.sum_univ_six, submatrix_apply, id]
  fin_cases k <;> fin_cases l <;>
    simp [A7_1, B7_1, Fin.succAbove, Fin.lt_def, Matrix.one_apply] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero] <;> rfl

theorem d7_child_1 :
    crossVec (KP 6 (d7 ∘ ((1 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((1 : Fin 7)).succAbove) r))) ⟨3, by omega⟩ ≠ 0 ∧
    levelPointN 6 (crossVec (KP 6 (d7 ∘ ((1 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((1 : Fin 7)).succAbove) r)))) = ⟨-2489/1875, 5318/1875⟩ := by
  rw [A7_1_eq]
  obtain ⟨h1, h2⟩ := levelPointN_six_of_cert A7_1 w7_1 B7_1 A7_1_w (by simp [w7_1]; rfl) B7_1_inv
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [w7_1, Matrix.cons_val]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- Child `2`: the matrix, a kernel vector and a left inverse of the `P₃`-minor. -/
noncomputable def A7_2 : Matrix (Fin 6) (Fin 7) ℂ := !![⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩;
    ⟨-1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨-51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨-228040201/13446881, -54729648240/2164947841⟩, ⟨228040201/7491169, 0⟩, ⟨-228040201/13446881, 54729648240/2164947841⟩;
    ⟨-481406112/5359375, -1280102616/5359375⟩, ⟨-43764192/214375, 32823144/214375⟩, ⟨43764192/214375, 32823144/214375⟩, ⟨481406112/5359375, -1280102616/5359375⟩, ⟨-49284/4375, 1182816/30625⟩, ⟨49284/1225, 0⟩, ⟨-49284/4375, -1182816/30625⟩;
    ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-9, 0⟩, ⟨9, 0⟩, ⟨-9, 0⟩;
    ⟨41875587/5359375, -15748084/5359375⟩, ⟨1073733/214375, 1431644/214375⟩, ⟨-1073733/214375, 1431644/214375⟩, ⟨-41875587/5359375, -15748084/5359375⟩, ⟨5041/4375, -120984/30625⟩, ⟨5041/1225, 0⟩, ⟨5041/4375, 120984/30625⟩;
    ⟨1763099091/5359375, 663045812/5359375⟩, ⟨45207669/214375, -60276892/214375⟩, ⟨-45207669/214375, -60276892/214375⟩, ⟨-1763099091/5359375, 663045812/5359375⟩, ⟨61009/4375, 1464216/30625⟩, ⟨61009/1225, 0⟩, ⟨61009/4375, -1464216/30625⟩]

noncomputable def w7_2 : Fin 7 → ℂ := ![⟨-2184/7225, 6887/7225⟩, ⟨108889/180625, 674744/541875⟩, ⟨544432/541875, 171783/180625⟩, ⟨1, 0⟩, ⟨1794874/541875, -106007/541875⟩, ⟨974753/541875, -713479/541875⟩, ⟨643609/541875, -1678862/541875⟩]

noncomputable def B7_2 : Matrix (Fin 6) (Fin 6) ℂ := !![⟨-355/27648, -485/27648⟩, ⟨2525257017395/1664481845993472, 3449999023765/1664481845993472⟩, ⟨310625/416351232, 424375/416351232⟩, ⟨-1775/221184, -2425/221184⟩, ⟨214375/47112192, 20794375/3344965632⟩, ⟨7765625/13494214656, 10609375/13494214656⟩;
    ⟨0, -119/5184⟩, ⟨248969001715/52015057687296, -49793800343/19505646632736⟩, ⟨-1225/19516464, -1225/26021952⟩, ⟨-217/20736, 0⟩, ⟨-2255225/104530176, 2255225/78397632⟩, ⟨336875/421694208, 336875/316270656⟩;
    ⟨-12269/414720, -485/27648⟩, ⟨-32230815622019/24967227689902080, -590412204067/184942427332608⟩, ⟨27475/15420416, -451675/1249053696⟩, ⟨-1775/221184, 2245/663552⟩, ⟨321708275/10034896896, 29935325/1114988544⟩, ⟨21336875/40482643968, 11099375/13494214656⟩;
    ⟨18973/414720, -10049/414720⟩, ⟨97218838469683/24967227689902080, -238377149042039/24967227689902080⟩, ⟨-626675/1249053696, -4894225/1249053696⟩, ⟨-26275/663552, 15079/663552⟩, ⟨-58147075/10034896896, 1164767975/10034896896⟩, ⟨80373125/40482643968, -111330625/40482643968⟩;
    ⟨1379/414720, 10049/414720⟩, ⟨-262477348408051/24967227689902080, -71482557092401/24967227689902080⟩, ⟨5616275/1249053696, -1758575/1249053696⟩, ⟨26275/663552, 10049/663552⟩, ⟨1496277475/10034896896, -86170175/10034896896⟩, ⟨126686875/40482643968, -3381875/3114049536⟩;
    ⟨8797/103680, 8797/103680⟩, ⟨-4531235831213/6241806922475520, 14888346302557/6241806922475520⟩, ⟨-866075/312263424, 123725/312263424⟩, ⟨-2515/165888, 2515/165888⟩, ⟨-49297675/2508724224, -345083725/2508724224⟩, ⟨2358125/10120660992, 336875/10120660992⟩]

theorem A7_2_eq : KP 6 (d7 ∘ ((2 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((2 : Fin 7)).succAbove) r)) = A7_2 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [KP, Fin.succAbove, Fin.lt_def, d7, A7_2] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem A7_2_w : A7_2 *ᵥ w7_2 = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_seven]
  fin_cases k <;>
    simp [A7_2, w7_2] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem B7_2_inv : B7_2 * A7_2.submatrix id (Fin.succAbove 3) = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Fin.sum_univ_six, submatrix_apply, id]
  fin_cases k <;> fin_cases l <;>
    simp [A7_2, B7_2, Fin.succAbove, Fin.lt_def, Matrix.one_apply] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero] <;> rfl

theorem d7_child_2 :
    crossVec (KP 6 (d7 ∘ ((2 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((2 : Fin 7)).succAbove) r))) ⟨3, by omega⟩ ≠ 0 ∧
    levelPointN 6 (crossVec (KP 6 (d7 ∘ ((2 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((2 : Fin 7)).succAbove) r)))) = ⟨-643609/541875, 1678862/541875⟩ := by
  rw [A7_2_eq]
  obtain ⟨h1, h2⟩ := levelPointN_six_of_cert A7_2 w7_2 B7_2 A7_2_w (by simp [w7_2]; rfl) B7_2_inv
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [w7_2, Matrix.cons_val]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- Child `3`: the matrix, a kernel vector and a left inverse of the `P₃`-minor. -/
noncomputable def A7_3 : Matrix (Fin 6) (Fin 7) ℂ := !![⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩;
    ⟨-1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨-51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨-228040201/13446881, -54729648240/2164947841⟩, ⟨228040201/7491169, 0⟩, ⟨-228040201/13446881, 54729648240/2164947841⟩;
    ⟨655025184/5359375, -1741771512/5359375⟩, ⟨59547744/214375, 44660808/214375⟩, ⟨-59547744/214375, 44660808/214375⟩, ⟨-655025184/5359375, -1741771512/5359375⟩, ⟨-60516/4375, -1452384/30625⟩, ⟨60516/1225, 0⟩, ⟨-60516/4375, 1452384/30625⟩;
    ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-9, 0⟩, ⟨9, 0⟩, ⟨-9, 0⟩;
    ⟨41875587/5359375, -15748084/5359375⟩, ⟨1073733/214375, 1431644/214375⟩, ⟨-1073733/214375, 1431644/214375⟩, ⟨-41875587/5359375, -15748084/5359375⟩, ⟨5041/4375, -120984/30625⟩, ⟨5041/1225, 0⟩, ⟨5041/4375, 120984/30625⟩;
    ⟨1763099091/5359375, 663045812/5359375⟩, ⟨45207669/214375, -60276892/214375⟩, ⟨-45207669/214375, -60276892/214375⟩, ⟨-1763099091/5359375, 663045812/5359375⟩, ⟨61009/4375, 1464216/30625⟩, ⟨61009/1225, 0⟩, ⟨61009/4375, -1464216/30625⟩]

noncomputable def w7_3 : Fin 7 → ℂ := ![⟨5544/7225, -4633/7225⟩, ⟨102617/180625, 736568/541875⟩, ⟨-13888/31875, -14953/10625⟩, ⟨1, 0⟩, ⟨-1098038/541875, 1383241/541875⟩, ⟨-1378543/541875, -3799399/541875⟩, ⟨1729561/541875, 357298/541875⟩]

noncomputable def B7_3 : Matrix (Fin 6) (Fin 6) ℂ := !![⟨-565/27648, 205/27648⟩, ⟨-28133497193795/1967114908901376, 10207729070315/1967114908901376⟩, ⟨3460625/604191744, -30625/14736384⟩, ⟨2825/221184, -1025/221184⟩, ⟨86515625/3344965632, -31390625/3344965632⟩, ⟨3460625/13494214656, -1255625/13494214656⟩;
    ⟨0, -637/25920⟩, ⟨348556602401/61472340903168, -348556602401/115260639193440⟩, ⟨-8575/28321488, 8575/37761984⟩, ⟨-245/20736, 0⟩, ⟨-2358125/104530176, 2358125/78397632⟩, ⟨351575/421694208, 351575/316270656⟩;
    ⟨-127/82944, 205/27648⟩, ⟨-39785246474057/5901344726704128, 4232473029155/218568323211264⟩, ⟨442225/604191744, -15840475/1812575232⟩, ⟨2825/221184, -13267/663552⟩, ⟨245826875/10034896896, -11606875/1114988544⟩, ⟨-32973325/40482643968, 9583175/13494214656⟩;
    ⟨43243/414720, -33623/414720⟩, ⟨1531806679951709/29506723633520640, 172137167785751/29506723633520640⟩, ⟨-34117475/1812575232, -5381425/1812575232⟩, ⟨-57707/663552, -17281/663552⟩, ⟨-880376875/10034896896, 1270049375/10034896896⟩, ⟨61922525/40482643968, 5643575/40482643968⟩;
    ⟨34133/414720, 33623/414720⟩, ⟨-547084484368541/29506723633520640, 1674216948932689/29506723633520640⟩, ⟨-809725/1812575232, -41188175/1812575232⟩, ⟨57707/663552, -33623/663552⟩, ⟨1200836875/10034896896, -1029704375/10034896896⟩, ⟨-14529725/40482643968, -41188175/40482643968⟩;
    ⟨911/20736, 911/20736⟩, ⟨14290820698441/1475336181676032, -46955553723449/1475336181676032⟩, ⟨-866075/453143808, 6062525/453143808⟩, ⟨-8171/165888, 8171/165888⟩, ⟨-28511875/2508724224, -199583125/2508724224⟩, ⟨23143925/10120660992, 3306275/10120660992⟩]

theorem A7_3_eq : KP 6 (d7 ∘ ((3 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((3 : Fin 7)).succAbove) r)) = A7_3 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [KP, Fin.succAbove, Fin.lt_def, d7, A7_3] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem A7_3_w : A7_3 *ᵥ w7_3 = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_seven]
  fin_cases k <;>
    simp [A7_3, w7_3] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem B7_3_inv : B7_3 * A7_3.submatrix id (Fin.succAbove 3) = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Fin.sum_univ_six, submatrix_apply, id]
  fin_cases k <;> fin_cases l <;>
    simp [A7_3, B7_3, Fin.succAbove, Fin.lt_def, Matrix.one_apply] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero] <;> rfl

theorem d7_child_3 :
    crossVec (KP 6 (d7 ∘ ((3 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((3 : Fin 7)).succAbove) r))) ⟨3, by omega⟩ ≠ 0 ∧
    levelPointN 6 (crossVec (KP 6 (d7 ∘ ((3 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((3 : Fin 7)).succAbove) r)))) = ⟨-1729561/541875, -357298/541875⟩ := by
  rw [A7_3_eq]
  obtain ⟨h1, h2⟩ := levelPointN_six_of_cert A7_3 w7_3 B7_3 A7_3_w (by simp [w7_3]; rfl) B7_3_inv
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [w7_3, Matrix.cons_val]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- Child `4`: the matrix, a kernel vector and a left inverse of the `P₃`-minor. -/
noncomputable def A7_4 : Matrix (Fin 6) (Fin 7) ℂ := !![⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩;
    ⟨-1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨-51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨-228040201/13446881, -54729648240/2164947841⟩, ⟨228040201/7491169, 0⟩, ⟨-228040201/13446881, 54729648240/2164947841⟩;
    ⟨655025184/5359375, -1741771512/5359375⟩, ⟨59547744/214375, 44660808/214375⟩, ⟨-59547744/214375, 44660808/214375⟩, ⟨-655025184/5359375, -1741771512/5359375⟩, ⟨-60516/4375, -1452384/30625⟩, ⟨60516/1225, 0⟩, ⟨-60516/4375, 1452384/30625⟩;
    ⟨-481406112/5359375, -1280102616/5359375⟩, ⟨-43764192/214375, 32823144/214375⟩, ⟨43764192/214375, 32823144/214375⟩, ⟨481406112/5359375, -1280102616/5359375⟩, ⟨-49284/4375, 1182816/30625⟩, ⟨49284/1225, 0⟩, ⟨-49284/4375, -1182816/30625⟩;
    ⟨41875587/5359375, -15748084/5359375⟩, ⟨1073733/214375, 1431644/214375⟩, ⟨-1073733/214375, 1431644/214375⟩, ⟨-41875587/5359375, -15748084/5359375⟩, ⟨5041/4375, -120984/30625⟩, ⟨5041/1225, 0⟩, ⟨5041/4375, 120984/30625⟩;
    ⟨1763099091/5359375, 663045812/5359375⟩, ⟨45207669/214375, -60276892/214375⟩, ⟨-45207669/214375, -60276892/214375⟩, ⟨-1763099091/5359375, 663045812/5359375⟩, ⟨61009/4375, 1464216/30625⟩, ⟨61009/1225, 0⟩, ⟨61009/4375, -1464216/30625⟩]

noncomputable def w7_4 : Fin 7 → ℂ := ![⟨240/289, 161/289⟩, ⟨157497/180625, 195608/541875⟩, ⟨501352/541875, 33593/180625⟩, ⟨1, 0⟩, ⟨1306198/541875, -2235641/541875⟩, ⟨-270403/541875, 888467/541875⟩, ⟨160729/541875, -2584262/541875⟩]

noncomputable def B7_4 : Matrix (Fin 6) (Fin 6) ℂ := !![⟨-2875/110592, -875/110592⟩, ⟨-20451025140875/2704782999739392, -6224225042875/2704782999739392⟩, ⟨17609375/4833533952, 5359375/4833533952⟩, ⟨2515625/3330809856, 765625/3330809856⟩, ⟨17609375/836241408, 5359375/836241408⟩, ⟨2515625/3373553664, 765625/3373553664⟩;
    ⟨0, -539/51840⟩, ⟨-348556602401/169048937483712, 348556602401/316966757781960⟩, ⟨265825/113285952, -265825/151047936⟩, ⟨-42875/78065856, -42875/104087808⟩, ⟨-728875/52265088, 728875/39198816⟩, ⟨8575/16219008, 8575/12164256⟩;
    ⟨-42341/1658880, -875/110592⟩, ⟨-217534886898469/40571744996090880, 49793800343/27321040401408⟩, ⟨5947375/4833533952, -30569875/14500601856⟩, ⟨1433075/1110269952, -439775/908402688⟩, ⟨86853725/2508724224, 4621925/278747136⟩, ⟨158375/778512384, 2137625/3373553664⟩;
    ⟨121129/1658880, 38629/1658880⟩, ⟨-571568807337199/40571744996090880, 776705037950261/40571744996090880⟩, ⟨73332175/14500601856, -170447725/14500601856⟩, ⟨-31322375/9992429568, -42392875/9992429568⟩, ⟨2468375/2508724224, 153069875/2508724224⟩, ⟨1831025/10120660992, -35689675/10120660992⟩;
    ⟨35663/1658880, -38629/1658880⟩, ⟨839260277981167/40571744996090880, -274783530492821/40571744996090880⟩, ⟨-165677575/14500601856, 47320525/14500601856⟩, ⟨58046975/9992429568, 6760075/9992429568⟩, ⟨264718825/2508724224, 47320525/2508724224⟩, ⟨36741775/10120660992, 6760075/10120660992⟩;
    ⟨42733/414720, 42733/414720⟩, ⟨-54325036174213/10142936249022720, 178496547429557/10142936249022720⟩, ⟨3080875/3625150464, -21566125/3625150464⟩, ⟨-10009475/2498107392, 1429925/2498107392⟩, ⟨-14635075/627181056, -102445525/627181056⟩, ⟨-1721125/2530165248, -245875/2530165248⟩]

theorem A7_4_eq : KP 6 (d7 ∘ ((4 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((4 : Fin 7)).succAbove) r)) = A7_4 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [KP, Fin.succAbove, Fin.lt_def, d7, A7_4] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem A7_4_w : A7_4 *ᵥ w7_4 = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_seven]
  fin_cases k <;>
    simp [A7_4, w7_4] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem B7_4_inv : B7_4 * A7_4.submatrix id (Fin.succAbove 3) = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Fin.sum_univ_six, submatrix_apply, id]
  fin_cases k <;> fin_cases l <;>
    simp [A7_4, B7_4, Fin.succAbove, Fin.lt_def, Matrix.one_apply] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero] <;> rfl

theorem d7_child_4 :
    crossVec (KP 6 (d7 ∘ ((4 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((4 : Fin 7)).succAbove) r))) ⟨3, by omega⟩ ≠ 0 ∧
    levelPointN 6 (crossVec (KP 6 (d7 ∘ ((4 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((4 : Fin 7)).succAbove) r)))) = ⟨-160729/541875, 2584262/541875⟩ := by
  rw [A7_4_eq]
  obtain ⟨h1, h2⟩ := levelPointN_six_of_cert A7_4 w7_4 B7_4 A7_4_w (by simp [w7_4]; rfl) B7_4_inv
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [w7_4, Matrix.cons_val]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- Child `5`: the matrix, a kernel vector and a left inverse of the `P₃`-minor. -/
noncomputable def A7_5 : Matrix (Fin 6) (Fin 7) ℂ := !![⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩;
    ⟨-1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨-51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨-228040201/13446881, -54729648240/2164947841⟩, ⟨228040201/7491169, 0⟩, ⟨-228040201/13446881, 54729648240/2164947841⟩;
    ⟨655025184/5359375, -1741771512/5359375⟩, ⟨59547744/214375, 44660808/214375⟩, ⟨-59547744/214375, 44660808/214375⟩, ⟨-655025184/5359375, -1741771512/5359375⟩, ⟨-60516/4375, -1452384/30625⟩, ⟨60516/1225, 0⟩, ⟨-60516/4375, 1452384/30625⟩;
    ⟨-481406112/5359375, -1280102616/5359375⟩, ⟨-43764192/214375, 32823144/214375⟩, ⟨43764192/214375, 32823144/214375⟩, ⟨481406112/5359375, -1280102616/5359375⟩, ⟨-49284/4375, 1182816/30625⟩, ⟨49284/1225, 0⟩, ⟨-49284/4375, -1182816/30625⟩;
    ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-9, 0⟩, ⟨9, 0⟩, ⟨-9, 0⟩;
    ⟨1763099091/5359375, 663045812/5359375⟩, ⟨45207669/214375, -60276892/214375⟩, ⟨-45207669/214375, -60276892/214375⟩, ⟨-1763099091/5359375, 663045812/5359375⟩, ⟨61009/4375, 1464216/30625⟩, ⟨61009/1225, 0⟩, ⟨61009/4375, -1464216/30625⟩]

noncomputable def w7_5 : Fin 7 → ℂ := ![⟨-5544/7225, 4633/7225⟩, ⟨739051/541875, -226744/180625⟩, ⟨-334432/180625, -48053/541875⟩, ⟨1, 0⟩, ⟨450062/541875, -4481609/541875⟩, ⟨-4430843/541875, 1607651/541875⟩, ⟨3219161/541875, 3150298/541875⟩]

noncomputable def B7_5 : Matrix (Fin 6) (Fin 6) ℂ := !![⟨-205/36864, -565/36864⟩, ⟨1458247010045/601062888830976, 4019071027685/601062888830976⟩, ⟨-214375/353673216, -24224375/14500601856⟩, ⟨4484375/9992429568, 12359375/9992429568⟩, ⟨-1025/165888, -2825/165888⟩, ⟨179375/562258944, 494375/562258944⟩;
    ⟨0, 217/17280⟩, ⟨-49793800343/3415130050176, 49793800343/6403368844080⟩, ⟨2255225/339857856, -2255225/453143808⟩, ⟨-30625/21290688, -30625/28387584⟩, ⟨595/31104, 0⟩, ⟨1225/35141184, 1225/26355888⟩;
    ⟨1289/110592, -565/36864⟩, ⟨17121953917943/1803188666492928, 11986079082565/601062888830976⟩, ⟨-77800975/14500601856, -348719525/43501805568⟩, ⟨1658125/3330809856, 35118125/29977288704⟩, ⟨-1025/165888, -15419/497664⟩, ⟨-1186675/1686776832, 308525/187419648⟩;
    ⟨60799/552960, 39211/552960⟩, ⟨-264326832420791/9015943332464640, 479080379900101/9015943332464640⟩, ⟨381956225/43501805568, -1101896075/43501805568⟩, ⟨-181435625/29977288704, -125768125/29977288704⟩, ⟨19751/497664, -15317/497664⟩, ⟨-246925/129752064, -6912325/1686776832⟩;
    ⟨64169/552960, -39211/552960⟩, ⟨668595584005559/9015943332464640, 278923529321339/9015943332464640⟩, ⟨-1460554025/43501805568, -336234325/43501805568⟩, ⟨147100625/29977288704, 171548125/29977288704⟩, ⟨-19751/497664, -39211/497664⟩, ⟨3277225/1686776832, 6861925/1686776832⟩;
    ⟨-337/27648, -337/27648⟩, ⟨10805254674431/450797166623232, -35502979644559/450797166623232⟩, ⟨-49297675/10875451392, 345083725/10875451392⟩, ⟨28511875/7494322176, -4073125/7494322176⟩, ⟨-11947/124416, 11947/124416⟩, ⟨2152325/421694208, 307475/421694208⟩]

theorem A7_5_eq : KP 6 (d7 ∘ ((5 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((5 : Fin 7)).succAbove) r)) = A7_5 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [KP, Fin.succAbove, Fin.lt_def, d7, A7_5] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem A7_5_w : A7_5 *ᵥ w7_5 = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_seven]
  fin_cases k <;>
    simp [A7_5, w7_5] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem B7_5_inv : B7_5 * A7_5.submatrix id (Fin.succAbove 3) = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Fin.sum_univ_six, submatrix_apply, id]
  fin_cases k <;> fin_cases l <;>
    simp [A7_5, B7_5, Fin.succAbove, Fin.lt_def, Matrix.one_apply] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero] <;> rfl

theorem d7_child_5 :
    crossVec (KP 6 (d7 ∘ ((5 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((5 : Fin 7)).succAbove) r))) ⟨3, by omega⟩ ≠ 0 ∧
    levelPointN 6 (crossVec (KP 6 (d7 ∘ ((5 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((5 : Fin 7)).succAbove) r)))) = ⟨-3219161/541875, -3150298/541875⟩ := by
  rw [A7_5_eq]
  obtain ⟨h1, h2⟩ := levelPointN_six_of_cert A7_5 w7_5 B7_5 A7_5_w (by simp [w7_5]; rfl) B7_5_inv
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [w7_5, Matrix.cons_val]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- Child `6`: the matrix, a kernel vector and a left inverse of the `P₃`-minor. -/
noncomputable def A7_6 : Matrix (Fin 6) (Fin 7) ℂ := !![⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨0, 8⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩;
    ⟨-1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨-51654526129515/348556602401, 27549080602408/348556602401⟩, ⟨1704599362273995/100732858093889, -16832488248071288/100732858093889⟩, ⟨-228040201/13446881, -54729648240/2164947841⟩, ⟨228040201/7491169, 0⟩, ⟨-228040201/13446881, 54729648240/2164947841⟩;
    ⟨655025184/5359375, -1741771512/5359375⟩, ⟨59547744/214375, 44660808/214375⟩, ⟨-59547744/214375, 44660808/214375⟩, ⟨-655025184/5359375, -1741771512/5359375⟩, ⟨-60516/4375, -1452384/30625⟩, ⟨60516/1225, 0⟩, ⟨-60516/4375, 1452384/30625⟩;
    ⟨-481406112/5359375, -1280102616/5359375⟩, ⟨-43764192/214375, 32823144/214375⟩, ⟨43764192/214375, 32823144/214375⟩, ⟨481406112/5359375, -1280102616/5359375⟩, ⟨-49284/4375, 1182816/30625⟩, ⟨49284/1225, 0⟩, ⟨-49284/4375, -1182816/30625⟩;
    ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-27, 0⟩, ⟨27, 0⟩, ⟨-9, 0⟩, ⟨9, 0⟩, ⟨-9, 0⟩;
    ⟨41875587/5359375, -15748084/5359375⟩, ⟨1073733/214375, 1431644/214375⟩, ⟨-1073733/214375, 1431644/214375⟩, ⟨-41875587/5359375, -15748084/5359375⟩, ⟨5041/4375, -120984/30625⟩, ⟨5041/1225, 0⟩, ⟨5041/4375, 120984/30625⟩]

noncomputable def w7_6 : Fin 7 → ℂ := ![⟨2184/7225, -6887/7225⟩, ⟨757867/541875, -247352/180625⟩, ⟨312144/180625, -498101/541875⟩, ⟨1, 0⟩, ⟨-1977826/541875, -81257/541875⟩, ⟨-2055947/541875, -2808829/541875⟩, ⟨520409/541875, -1909862/541875⟩]

noncomputable def B7_6 : Matrix (Fin 6) (Fin 6) ℂ := !![⟨-485/36864, 355/36864⟩, ⟨-24149993166355/1803188666492928, 17676799121765/1803188666492928⟩, ⟨74265625/14500601856, -54359375/14500601856⟩, ⟨-2970625/9992429568, 2174375/9992429568⟩, ⟨2425/165888, -1775/165888⟩, ⟨2970625/139373568, -30625/1963008⟩;
    ⟨0, 49/3456⟩, ⟨-1742783012005/112699291655808, 348556602401/42262234370928⟩, ⟨2358125/339857856, -2358125/453143808⟩, ⟨-351575/234197568, -351575/312263424⟩, ⟨637/31104, 0⟩, ⟨8575/8710848, -8575/6533136⟩;
    ⟨-17467/552960, 355/36864⟩, ⟨-451480387709981/27047829997393920, 6522987844933/1803188666492928⟩, ⟨77695625/14500601856, -149358125/43501805568⟩, ⟨2622725/3330809856, -36832075/29977288704⟩, ⟨2425/165888, 2515/497664⟩, ⟨20985475/418120704, 844025/139373568⟩;
    ⟨75239/552960, -28957/552960⟩, ⟨1230852950678617/27047829997393920, 852619243273189/27047829997393920⟩, ⟨-779314375/43501805568, -562611875/43501805568⟩, ⟨-61025825/29977288704, 322175/810196992⟩, ⟨-31375/497664, -26147/497664⟩, ⟨-40159175/418120704, 35119525/418120704⟩;
    ⟨50497/552960, 28957/552960⟩, ⟨-49793800343/189145664317440, 1441879076532251/27047829997393920⟩, ⟨-23673125/3346292736, -886808125/43501805568⟩, ⟨2316475/2725208064, 35472325/29977288704⟩, ⟨31375/497664, -28957/497664⟩, ⟨39688775/418120704, -35472325/418120704⟩;
    ⟨12371/138240, 12371/138240⟩, ⟨-12896594288837/6761957499348480, 42374524091893/6761957499348480⟩, ⟨2358125/10875451392, -16506875/10875451392⟩, ⟨-23143925/7494322176, 3306275/7494322176⟩, ⟨-1405/124416, 1405/124416⟩, ⟨-2152325/104530176, -15066275/104530176⟩]

theorem A7_6_eq : KP 6 (d7 ∘ ((6 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((6 : Fin 7)).succAbove) r)) = A7_6 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [KP, Fin.succAbove, Fin.lt_def, d7, A7_6] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem A7_6_w : A7_6 *ᵥ w7_6 = 0 := by
  funext k
  simp only [mulVec, dotProduct, Fin.sum_univ_seven]
  fin_cases k <;>
    simp [A7_6, w7_6] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

theorem B7_6_inv : B7_6 * A7_6.submatrix id (Fin.succAbove 3) = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Fin.sum_univ_six, submatrix_apply, id]
  fin_cases k <;> fin_cases l <;>
    simp [A7_6, B7_6, Fin.succAbove, Fin.lt_def, Matrix.one_apply] <;>
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero] <;> rfl

theorem d7_child_6 :
    crossVec (KP 6 (d7 ∘ ((6 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((6 : Fin 7)).succAbove) r))) ⟨3, by omega⟩ ≠ 0 ∧
    levelPointN 6 (crossVec (KP 6 (d7 ∘ ((6 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((6 : Fin 7)).succAbove) r)))) = ⟨-520409/541875, 1909862/541875⟩ := by
  rw [A7_6_eq]
  obtain ⟨h1, h2⟩ := levelPointN_six_of_cert A7_6 w7_6 B7_6 A7_6_w (by simp [w7_6]; rfl) B7_6_inv
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [w7_6, Matrix.cons_val]
  norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

noncomputable def p7 : ℂ := ⟨-2895641/541875, -2543698/541875⟩
noncomputable def u7 : ℂ := ⟨145088/36125, 54408/7225⟩
noncomputable def t7 : Fin 7 → ℝ := ![0, 1, 35188/34005, 3644/6801, 42733/34005, -337/2267, 12371/11335]

/-- Each child's middle coordinate `P₃` is nonzero. -/
theorem d7_children_P3 : ∀ i : Fin 7,
    crossVec (KP 6 (d7 ∘ i.succAbove) (fun r => conj ((d7 ∘ i.succAbove) r))) ⟨3, by omega⟩ ≠ 0 := by
  intro i
  fin_cases i
  · exact (d7_child_0).1
  · exact (d7_child_1).1
  · exact (d7_child_2).1
  · exact (d7_child_3).1
  · exact (d7_child_4).1
  · exact (d7_child_5).1
  · exact (d7_child_6).1

theorem u7_ne_zero : u7 ≠ 0 := by
  rw [u7, ne_eq, j13_zero, j13_mk_eq]; norm_num

/-- **Target A.** The seven child level points of `d7` are exactly collinear. -/
theorem d7_children_collinear : ∃ (p u : ℂ), u ≠ 0 ∧ ∀ i : Fin 7,
    levelPointN 6 (crossVec (KP 6 (d7 ∘ i.succAbove) (fun r => conj ((d7 ∘ i.succAbove) r)))) =
      p + ((t7 i : ℝ) : ℂ) * u := by
  refine ⟨p7, u7, u7_ne_zero, fun i => ?_⟩
  fin_cases i
  · show levelPointN 6 (crossVec (KP 6 (d7 ∘ ((0 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((0 : Fin 7)).succAbove) r)))) = p7 + ((t7 0 : ℝ) : ℂ) * u7
    rw [(d7_child_0).2]
    simp only [p7, u7, t7, Matrix.cons_val, j13_ofReal]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  · show levelPointN 6 (crossVec (KP 6 (d7 ∘ ((1 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((1 : Fin 7)).succAbove) r)))) = p7 + ((t7 1 : ℝ) : ℂ) * u7
    rw [(d7_child_1).2]
    simp only [p7, u7, t7, Matrix.cons_val, j13_ofReal]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  · show levelPointN 6 (crossVec (KP 6 (d7 ∘ ((2 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((2 : Fin 7)).succAbove) r)))) = p7 + ((t7 2 : ℝ) : ℂ) * u7
    rw [(d7_child_2).2]
    simp only [p7, u7, t7, Matrix.cons_val, j13_ofReal]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  · show levelPointN 6 (crossVec (KP 6 (d7 ∘ ((3 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((3 : Fin 7)).succAbove) r)))) = p7 + ((t7 3 : ℝ) : ℂ) * u7
    rw [(d7_child_3).2]
    simp only [p7, u7, t7, Matrix.cons_val, j13_ofReal]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  · show levelPointN 6 (crossVec (KP 6 (d7 ∘ ((4 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((4 : Fin 7)).succAbove) r)))) = p7 + ((t7 4 : ℝ) : ℂ) * u7
    rw [(d7_child_4).2]
    simp only [p7, u7, t7, Matrix.cons_val, j13_ofReal]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  · show levelPointN 6 (crossVec (KP 6 (d7 ∘ ((5 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((5 : Fin 7)).succAbove) r)))) = p7 + ((t7 5 : ℝ) : ℂ) * u7
    rw [(d7_child_5).2]
    simp only [p7, u7, t7, Matrix.cons_val, j13_ofReal]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]
  · show levelPointN 6 (crossVec (KP 6 (d7 ∘ ((6 : Fin 7)).succAbove) (fun r => conj ((d7 ∘ ((6 : Fin 7)).succAbove) r)))) = p7 + ((t7 6 : ℝ) : ℂ) * u7
    rw [(d7_child_6).2]
    simp only [p7, u7, t7, Matrix.cons_val, j13_ofReal]
    norm_num [j13_mk_add, j13_mk_sub, j13_mk_neg, j13_mk_conj, Complex.mk_mul_mk, pow_succ, pow_zero, j13_one, j13_zero, j13_mk_eq, j13_mk_eq_zero]

/-- Packaging: the seven child level points lie on one generalized circle (the line branch). -/
theorem d7_children_gcircleS :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧ ∀ i : Fin 7,
      (↑(levelPointN 6 (crossVec (KP 6 (d7 ∘ i.succAbove)
        (fun r => conj ((d7 ∘ i.succAbove) r))))) : OnePoint ℂ) ∈ Y := by
  obtain ⟨p, u, hu, h⟩ := d7_children_collinear
  refine ⟨Clifford.lineS p u, Or.inr ⟨p, u, hu, rfl⟩, fun i => ?_⟩
  refine Set.mem_insert_of_mem _ ⟨_, ⟨t7 i, ?_⟩, rfl⟩
  rw [Complex.real_smul]
  exact h i

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.d7_genPosN
#print axioms Clifford.MorleyKernel.KP7_d7_sub_mulVec
#print axioms Clifford.MorleyKernel.d7_P0
#print axioms Clifford.MorleyKernel.levelPointN_six_of_cert
#print axioms Clifford.MorleyKernel.A7_0_eq
#print axioms Clifford.MorleyKernel.A7_0_w
#print axioms Clifford.MorleyKernel.B7_0_inv
#print axioms Clifford.MorleyKernel.d7_child_0
#print axioms Clifford.MorleyKernel.A7_1_eq
#print axioms Clifford.MorleyKernel.A7_1_w
#print axioms Clifford.MorleyKernel.B7_1_inv
#print axioms Clifford.MorleyKernel.d7_child_1
#print axioms Clifford.MorleyKernel.A7_2_eq
#print axioms Clifford.MorleyKernel.A7_2_w
#print axioms Clifford.MorleyKernel.B7_2_inv
#print axioms Clifford.MorleyKernel.d7_child_2
#print axioms Clifford.MorleyKernel.A7_3_eq
#print axioms Clifford.MorleyKernel.A7_3_w
#print axioms Clifford.MorleyKernel.B7_3_inv
#print axioms Clifford.MorleyKernel.d7_child_3
#print axioms Clifford.MorleyKernel.A7_4_eq
#print axioms Clifford.MorleyKernel.A7_4_w
#print axioms Clifford.MorleyKernel.B7_4_inv
#print axioms Clifford.MorleyKernel.d7_child_4
#print axioms Clifford.MorleyKernel.A7_5_eq
#print axioms Clifford.MorleyKernel.A7_5_w
#print axioms Clifford.MorleyKernel.B7_5_inv
#print axioms Clifford.MorleyKernel.d7_child_5
#print axioms Clifford.MorleyKernel.A7_6_eq
#print axioms Clifford.MorleyKernel.A7_6_w
#print axioms Clifford.MorleyKernel.B7_6_inv
#print axioms Clifford.MorleyKernel.d7_child_6
#print axioms Clifford.MorleyKernel.d7_children_P3
#print axioms Clifford.MorleyKernel.u7_ne_zero
#print axioms Clifford.MorleyKernel.d7_children_collinear
#print axioms Clifford.MorleyKernel.d7_children_gcircleS
#check @Clifford.MorleyKernel.d7_genPosN
#check @Clifford.MorleyKernel.d7_P0
#check @Clifford.MorleyKernel.d7_children_P3
#check @Clifford.MorleyKernel.d7_children_collinear
#check @Clifford.MorleyKernel.d7_children_gcircleS

/-! ## J19 — the seven-centre parent row relation and `hodd_one_P0_line` (Paper L / J19)

`symB.py` identity: for a child vector `w` (seven coordinates of `KP 6`) and the removed centre
`(xi, yi)`, the merged seven-column parent matrix `M7g` applied to `u7v xi yi w` gives, row by row,
`(yi·x − xi·y)·g + yi·x³·(z w₃ + w₆) + xi·y³·(Z w₀ − w₄)`, where `g` is the `KP 6` row form.
At a child level point (`z = −w₆/w₃`, `Z = conj z = w₄/w₀`) every row vanishes, so the merged
determinant vanishes; expanded in its two affine columns it is
`E₀ + z·Q₀(v) + Z·G + z Z·(−P₀(v))`, i.e. with `P₀ = 0` a real line through every child point. -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section J19
variable {R : Type*} [CommRing R]

/-- The `KP 6` row form at the point `(x, y)` applied to `w`. -/
def g7 (x y : R) (w : Fin 7 → R) : R :=
  y ^ 3 * w 0 - x * y ^ 2 * w 1 + x ^ 2 * y * w 2 - x ^ 3 * w 3 - y ^ 2 * w 4 + x * y * w 5 - x ^ 2 * w 6

/-- The coefficient vector `u` of `symB.py`. -/
def u7v (xi yi : R) (w : Fin 7 → R) : Fin 7 → R :=
  ![-xi * w 0, -yi * w 0 - xi * w 1, -yi * w 1 - xi * w 2, -yi * w 2 - xi * w 3,
    -yi * w 4 - xi * w 5, -yi * w 5 - xi * w 6, yi * w 3]

/-- The seven-column parent matrix with free first and last columns `a`, `b`
(`symB.py`: `a = y⁴ − Z y³`, `b = z x³ − x⁴`). -/
def M7g (x y a b : Fin 7 → R) : Matrix (Fin 7) (Fin 7) R :=
  Matrix.of fun k j => ![a k, -x k * y k ^ 3, x k ^ 2 * y k ^ 2, -x k ^ 3 * y k, x k * y k ^ 2,
    -x k ^ 2 * y k, b k] j

/-- **`symB.py`, scalar form** (one row; pure polynomial identity). -/
theorem rowRel7_scalar (x y xi yi z Z : R) (w : Fin 7 → R) :
    (y ^ 4 - Z * y ^ 3) * (-xi * w 0) + (-x * y ^ 3) * (-yi * w 0 - xi * w 1) +
      (x ^ 2 * y ^ 2) * (-yi * w 1 - xi * w 2) + (-x ^ 3 * y) * (-yi * w 2 - xi * w 3) +
      (x * y ^ 2) * (-yi * w 4 - xi * w 5) + (-x ^ 2 * y) * (-yi * w 5 - xi * w 6) +
      (z * x ^ 3 - x ^ 4) * (yi * w 3) - (yi * x - xi * y) * g7 x y w =
    yi * x ^ 3 * (z * w 3 + w 6) + xi * y ^ 3 * (Z * w 0 - w 4) := by
  unfold g7; ring

/-- **`symB.py`, matrix form** (general in the seven centres). -/
theorem M7g_mulVec (x y : Fin 7 → R) (xi yi z Z : R) (w : Fin 7 → R) (k : Fin 7) :
    (M7g x y (fun k => y k ^ 4 - Z * y k ^ 3) (fun k => z * x k ^ 3 - x k ^ 4) *ᵥ u7v xi yi w) k =
      (yi * x k - xi * y k) * g7 (x k) (y k) w +
        yi * x k ^ 3 * (z * w 3 + w 6) + xi * y k ^ 3 * (Z * w 0 - w 4) := by
  have h := rowRel7_scalar (x k) (y k) xi yi z Z w
  simp only [M7g, u7v, mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two] at h ⊢
  linear_combination h

/-- Linearity of `det M7g` in the first column. -/
theorem det_M7g_left (x y a a' b : Fin 7 → R) (s : R) :
    (M7g x y (fun k => a k + s * a' k) b).det = (M7g x y a b).det + s * (M7g x y a' b).det := by
  have e1 : M7g x y (fun k => a k + s * a' k) b = updateCol (M7g x y a b) 0 (a + s • a') := by
    ext k j; fin_cases j <;> simp [M7g, updateCol_apply]
  have e2 : updateCol (M7g x y a b) 0 a = M7g x y a b := by
    ext k j; fin_cases j <;> simp [M7g, updateCol_apply]
  have e3 : updateCol (M7g x y a b) 0 a' = M7g x y a' b := by
    ext k j; fin_cases j <;> simp [M7g, updateCol_apply]
  rw [e1, det_updateCol_add, det_updateCol_smul, e2, e3]

/-- Linearity of `det M7g` in the last column. -/
theorem det_M7g_right (x y a b b' : Fin 7 → R) (s : R) :
    (M7g x y a (fun k => b k + s * b' k)).det = (M7g x y a b).det + s * (M7g x y a b').det := by
  have e1 : M7g x y a (fun k => b k + s * b' k) = updateCol (M7g x y a b) 6 (b + s • b') := by
    ext k j; fin_cases j <;> simp [M7g, updateCol_apply]
  have e2 : updateCol (M7g x y a b) 6 b = M7g x y a b := by
    ext k j; fin_cases j <;> simp [M7g, updateCol_apply]
  have e3 : updateCol (M7g x y a b) 6 b' = M7g x y a b' := by
    ext k j; fin_cases j <;> simp [M7g, updateCol_apply]
  rw [e1, det_updateCol_add, det_updateCol_smul, e2, e3]

/-- **Bilinear expansion** of the merged determinant:
`det = E₀ + z·D + Z·G + z Z·F` (`D = Q₀(v)`, `F = −P₀(v)` below). -/
theorem det_M7_expand (x y : Fin 7 → R) (z Z : R) :
    (M7g x y (fun k => y k ^ 4 - Z * y k ^ 3) (fun k => z * x k ^ 3 - x k ^ 4)).det =
      (M7g x y (fun k => y k ^ 4) (fun k => -x k ^ 4)).det +
        z * (M7g x y (fun k => y k ^ 4) (fun k => x k ^ 3)).det +
        Z * (M7g x y (fun k => -y k ^ 3) (fun k => -x k ^ 4)).det +
        z * Z * (M7g x y (fun k => -y k ^ 3) (fun k => x k ^ 3)).det := by
  have ea : (fun k => y k ^ 4 - Z * y k ^ 3) = fun k => y k ^ 4 + Z * (-y k ^ 3) := by
    funext k; ring
  have eb : (fun k => z * x k ^ 3 - x k ^ 4) = fun k => -x k ^ 4 + z * x k ^ 3 := by
    funext k; ring
  rw [ea, eb, det_M7g_left, det_M7g_right, det_M7g_right]
  ring

/-- The `z`-coefficient is the parent coordinate `Q₀(v) = crossVec (KP 7) 4`. -/
theorem det_M7_D (x y : Fin 7 → R) :
    (M7g x y (fun k => y k ^ 4) (fun k => x k ^ 3)).det = crossVec (KP 7 x y) 4 := by
  have e : M7g x y (fun k => y k ^ 4) (fun k => x k ^ 3) = (KP 7 x y).submatrix id (Fin.succAbove 4) := by
    ext k j
    fin_cases j <;> simp [M7g, KP, Fin.succAbove, Fin.lt_def] <;> ring
  rw [e]; unfold crossVec; norm_num

/-- The column permutation `[3,0,1,2,4,5,6]`. -/
def sig7 : Equiv.Perm (Fin 7) where
  toFun := ![3, 0, 1, 2, 4, 5, 6]
  invFun := ![1, 2, 3, 0, 4, 5, 6]
  left_inv := by decide
  right_inv := by decide

/-- The `z Z`-coefficient is `± P₀(v)`: a column permutation of the `P₀`-minor. -/
theorem det_M7_F (x y : Fin 7 → R) :
    (M7g x y (fun k => -y k ^ 3) (fun k => x k ^ 3)).det =
      Equiv.Perm.sign sig7 * crossVec (KP 7 x y) 0 := by
  have e : M7g x y (fun k => -y k ^ 3) (fun k => x k ^ 3) =
      ((KP 7 x y).submatrix id (Fin.succAbove 0)).submatrix id sig7 := by
    ext k j
    fin_cases j <;> simp [M7g, KP, sig7, Fin.succAbove, Fin.lt_def] <;> ring
  rw [e, det_permute', crossVec]; simp

end J19

/-- **Target A (consequence).** Every child level point `z` of seven centres satisfies the
merged determinant equation `det M7(z, z̄) = 0` (no hypothesis on `P₀`). -/
theorem child_det_M7 (c : Fin 7 → ℂ) (hc : ∀ j, c j ≠ 0) (i : Fin 7)
    (hPi : crossVec (KP 6 (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) ⟨3, by omega⟩ ≠ 0) :
    let z := levelPointN 6 (crossVec (KP 6 (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))))
    (M7g c (fun k => conj (c k)) (fun k => conj (c k) ^ 4 - conj z * conj (c k) ^ 3)
      (fun k => z * c k ^ 3 - c k ^ 4)).det = 0 := by
  intro z
  set s := c ∘ i.succAbove with hs
  set w := crossVec (KP 6 s (fun r => conj (s r))) with hw
  have hw3 : w 3 ≠ 0 := hPi
  have hw0 : w 0 ≠ 0 := crossVec_even_P0_ne_zero 2 s hPi
  have hz : z * w 3 + w 6 = 0 := by
    show -w (Fin.last 6) / w ⟨6 / 2, by omega⟩ * w 3 + w 6 = 0
    have : (⟨6 / 2, by omega⟩ : Fin 7) = 3 := rfl
    rw [this, div_mul_cancel₀ _ hw3]; simp
  have hZ : conj z * w 0 - w 4 = 0 := by
    have h := conj_levelPointN_even 2 s
    have h' : conj z = w 4 / w 0 := h
    rw [h', div_mul_cancel₀ _ hw0, sub_self]
  have hrow : ∀ r : Fin 6, g7 (s r) (conj (s r)) w = 0 := by
    intro r
    have := KP6_row s (fun k => conj (s k)) r
    unfold g7; exact this
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨u7v (c i) (conj (c i)) w, ?_, ?_⟩
  · intro h0
    have := congrFun h0 0
    simp only [u7v, Matrix.cons_val_zero, Pi.zero_apply, neg_mul, neg_eq_zero, mul_eq_zero] at this
    exact this.elim (hc i) hw0
  · funext k
    rw [M7g_mulVec, hz, hZ, Pi.zero_apply]
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨r, rfl⟩
    · ring
    · have := hrow r
      simp only [hs, Function.comp_apply] at this
      rw [this]; ring

/-- **Target A, the line.** With `P₀ = 0`, every child level point satisfies the real-linear
equation `E₀ + Q₀(v)·z + G·z̄ = 0`. -/
theorem child_line_P0 (c : Fin 7 → ℂ) (hc : ∀ j, c j ≠ 0)
    (hP0 : crossVec (KP 7 c (fun j => conj (c j))) 0 = 0) (i : Fin 7)
    (hPi : crossVec (KP 6 (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) ⟨3, by omega⟩ ≠ 0) :
    let z := levelPointN 6 (crossVec (KP 6 (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))))
    (M7g c (fun k => conj (c k)) (fun k => conj (c k) ^ 4) (fun k => -c k ^ 4)).det +
      crossVec (KP 7 c (fun j => conj (c j))) 4 * z +
      (M7g c (fun k => conj (c k)) (fun k => -conj (c k) ^ 3) (fun k => -c k ^ 4)).det * conj z = 0 := by
  intro z
  have h := child_det_M7 c hc i hPi
  simp only at h
  rw [det_M7_expand, det_M7_D, det_M7_F, hP0] at h
  linear_combination h

/-- A finite family satisfying one real-linear equation `l z + m z̄ + n = 0` with `l ≠ 0` lies on a line. -/
theorem collinear_of_reallin {ι : Type*} (z : ι → ℂ) (i0 : ι) (l m n : ℂ) (hl : l ≠ 0)
    (h : ∀ i, l * z i + m * conj (z i) + n = 0) :
    ∃ p u : ℂ, u ≠ 0 ∧ ∀ i, ∃ t : ℝ, z i = p + (t : ℂ) * u := by
  by_cases hall : ∀ i, z i = z i0
  · exact ⟨z i0, 1, one_ne_zero, fun i => ⟨0, by simp [hall i]⟩⟩
  push Not at hall
  obtain ⟨j, hj⟩ := hall
  refine ⟨z i0, z j - z i0, sub_ne_zero.2 hj, fun i => ?_⟩
  set u := z j - z i0 with hu
  set d := z i - z i0 with hd
  have hu0 : u ≠ 0 := sub_ne_zero.2 hj
  have Ld : l * d + m * conj d = 0 := by
    simp only [hd, map_sub]; linear_combination h i - h i0
  have Lu : l * u + m * conj u = 0 := by
    simp only [hu, map_sub]; linear_combination h j - h i0
  have key : l * (d * conj u - conj d * u) = 0 := by
    linear_combination conj u * Ld - conj d * Lu
  have hr : d * conj u = conj d * u := sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hl)
  have hreal : ((d * conj u).re : ℂ) = d * conj u := by
    apply Complex.conj_eq_iff_re.1
    rw [map_mul, Complex.conj_conj, hr, mul_comm]
  have hn : (Complex.normSq u : ℂ) = u * conj u := (Complex.mul_conj u).symm
  have hn0 : u * conj u ≠ 0 := mul_ne_zero hu0 ((map_ne_zero _).2 hu0)
  refine ⟨(d * conj u).re / Complex.normSq u, ?_⟩
  push_cast
  rw [hreal, hn]
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu0
  have hx : d * conj u / (u * conj u) * u = d := by field_simp
  linear_combination -hx - hd

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.rowRel7_scalar
#print axioms Clifford.MorleyKernel.M7g_mulVec
#print axioms Clifford.MorleyKernel.det_M7g_left
#print axioms Clifford.MorleyKernel.det_M7g_right
#print axioms Clifford.MorleyKernel.det_M7_expand
#print axioms Clifford.MorleyKernel.det_M7_D
#print axioms Clifford.MorleyKernel.det_M7_F
#print axioms Clifford.MorleyKernel.child_det_M7
#print axioms Clifford.MorleyKernel.child_line_P0
#print axioms Clifford.MorleyKernel.collinear_of_reallin

/-! ## J19 Target B — `hodd_one_P0_line`

Case split on the parent coordinate `Q₀(v) = v 4`:
* `v 4 ≠ 0`: `child_line_P0` is a genuine real line `E₀ + v₄ z + G z̄ = 0` through all seven child
  level points (`collinear_of_reallin`);
* `v 4 = 0`: with `P₀ = 0` the odd Plücker relation forces `Q₃ = v 7 = 0`, so the parent matrix
  without its last column is singular; a kernel vector `V` of it is a kernel vector of every
  child `KP 6` (`KP_sub_eq_odd`), hence all seven child level points equal `-V 6 / V 3`. -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- A kernel vector of the parent matrix without its last column kills every child matrix. -/
theorem child_mulVec_of_parent (d : Fin 7 → ℂ) (hd : ∀ j, d j ≠ 0) (V : Fin 7 → ℂ)
    (hV : (KP 7 d (fun j => conj (d j))).submatrix id (Fin.last 7).succAbove *ᵥ V = 0) (i : Fin 7) :
    KP 6 (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)) *ᵥ V = 0 := by
  funext r
  have h := congrFun hV (i.succAbove r)
  have e : ∀ l, (KP 7 d (fun j => conj (d j))) (i.succAbove r) ((Fin.last 7).succAbove l) =
      conj (d (i.succAbove r)) * KP 6 (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)) r l :=
    fun l => subRowsOdd_entry 2 d (fun j => conj (d j)) i r l
  simp only [mulVec, dotProduct, Matrix.submatrix_apply, id, e, Pi.zero_apply] at h ⊢
  simp only [mul_assoc] at h
  rw [← Finset.mul_sum] at h
  exact (mul_eq_zero.1 h).resolve_left ((map_ne_zero _).2 (hd _))

/-- The level point of a rank-6 `6 × 7` matrix read off any nonzero kernel vector. -/
theorem levelPointN_six_of_ker (A : Matrix (Fin 6) (Fin 7) ℂ) (h3 : crossVec A ⟨3, by omega⟩ ≠ 0)
    (V : Fin 7 → ℂ) (hV : A *ᵥ V = 0) (hV0 : V ≠ 0) :
    levelPointN 6 (crossVec A) = -V 6 / V 3 := by
  have hk := ker_eq_span_crossVec A ⟨3, by omega⟩ h3
  have hmem : V ∈ LinearMap.ker A.mulVecLin := by simpa using hV
  rw [hk, Submodule.mem_span_singleton] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hs0 : s ≠ 0 := by rintro rfl; exact hV0 (by rw [← hs, zero_smul])
  have e3 := congrFun hs 3
  have e6 := congrFun hs 6
  simp only [Pi.smul_apply, smul_eq_mul] at e3 e6
  have e : (⟨6 / 2, by omega⟩ : Fin 7) = 3 := rfl
  have el : (Fin.last 6 : Fin 7) = 6 := rfl
  have h3' : crossVec A 3 ≠ 0 := h3
  rw [levelPointN, e, el, ← e3, ← e6, neg_div, neg_div, mul_div_mul_left _ _ hs0]

/-- With `P₀ = 0`: `Q₀ = 0` forces `Q₃ = 0` (odd Plücker, `norm_Q0_eq_QL_sub`). -/
theorem Q3_zero_of_P0_Q0 (d : Fin 7 → ℂ)
    (hP0 : crossVec (KP 7 d (fun j => conj (d j))) 0 = 0)
    (hQ0 : crossVec (KP 7 d (fun j => conj (d j))) 4 = 0) :
    crossVec (KP 7 d (fun j => conj (d j))) 7 = 0 := by
  have h := kernel_eq_zero_of_P0 1 d hP0 0
  rw [oddCircleEq_of_P0_zero _ _ hP0] at h
  have e4 : (⟨1 + 2 + 1, by omega⟩ : Fin (2 * (1 + 2) + 2)) = 4 := rfl
  have e7 : (Fin.last (2 * (1 + 2) + 1)) = 7 := rfl
  rw [e4, e7] at h
  change crossVec (KP 7 d (fun j => conj (d j))) 4 * conj (crossVec (KP 7 d (fun j => conj (d j))) 4) -
    crossVec (KP 7 d (fun j => conj (d j))) 7 * conj (crossVec (KP 7 d (fun j => conj (d j))) 7) = 0 at h
  rw [hQ0, zero_mul, zero_sub, neg_eq_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · exact (map_eq_zero _).1 h

/-- **Degenerate branch.** If `P₀ = Q₀ = 0`, the seven child level points coincide. -/
theorem children_eq_of_P0_Q0 (d : Fin 7 → ℂ) (hd : ∀ j, d j ≠ 0)
    (hP0 : crossVec (KP 7 d (fun j => conj (d j))) 0 = 0)
    (hQ0 : crossVec (KP 7 d (fun j => conj (d j))) 4 = 0)
    (hPi : ∀ i : Fin 7, crossVec (KP 6 (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r))) ⟨3, by omega⟩ ≠ 0) :
    ∃ p : ℂ, ∀ i : Fin 7,
      levelPointN 6 (crossVec (KP 6 (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)))) = p := by
  have h7 := Q3_zero_of_P0_Q0 d hP0 hQ0
  have hdet : ((KP 7 d (fun j => conj (d j))).submatrix id (Fin.last 7).succAbove).det = 0 := by
    have : crossVec (KP 7 d (fun j => conj (d j))) (Fin.last 7) = 0 := h7
    unfold crossVec at this
    simpa using this
  obtain ⟨V, hV0, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  exact ⟨-V 6 / V 3, fun i => levelPointN_six_of_ker _ (hPi i) V
    (child_mulVec_of_parent d hd V hV i) hV0⟩

/-- **Target B.** Seven centres in general position with `P₀ = 0`: the seven child level points
lie on one generalized circle — a line (`lineS`). -/
theorem hodd_one_P0_line (d : Fin 7 → ℂ) (h : GenPosN d)
    (hP0 : crossVec (KP 7 d (fun j => conj (d j))) 0 = 0)
    (hPi : ∀ i : Fin 7, crossVec (KP 6 (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r))) ⟨3, by omega⟩ ≠ 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin 7, (↑(levelPointN 6 (crossVec (KP 6 (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))))) : OnePoint ℂ) ∈ Y := by
  have hd : ∀ j, d j ≠ 0 := hc_of_genPos (by norm_num) d h
  by_cases hQ0 : crossVec (KP 7 d (fun j => conj (d j))) 4 = 0
  · obtain ⟨p, hp⟩ := children_eq_of_P0_Q0 d hd hP0 hQ0 hPi
    refine ⟨Clifford.lineS p 1, Or.inr ⟨p, 1, one_ne_zero, rfl⟩, fun i => ?_⟩
    refine Set.mem_insert_of_mem _ ⟨_, ⟨0, ?_⟩, rfl⟩
    rw [hp i]; simp
  · obtain ⟨p, u, hu, ht⟩ := collinear_of_reallin
      (fun i : Fin 7 => levelPointN 6 (crossVec (KP 6 (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))))) 0
      (crossVec (KP 7 d (fun j => conj (d j))) 4)
      (M7g d (fun k => conj (d k)) (fun k => -conj (d k) ^ 3) (fun k => -d k ^ 4)).det
      (M7g d (fun k => conj (d k)) (fun k => conj (d k) ^ 4) (fun k => -d k ^ 4)).det hQ0
      (fun i => by
        have hl := child_line_P0 d hd hP0 i (hPi i)
        simp only at hl
        linear_combination hl)
    refine ⟨Clifford.lineS p u, Or.inr ⟨p, u, hu, rfl⟩, fun i => ?_⟩
    obtain ⟨t, htt⟩ := ht i
    refine Set.mem_insert_of_mem _ ⟨_, ⟨t, ?_⟩, rfl⟩
    rw [Complex.real_smul]
    exact htt

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.child_mulVec_of_parent
#print axioms Clifford.MorleyKernel.levelPointN_six_of_ker
#print axioms Clifford.MorleyKernel.Q3_zero_of_P0_Q0
#print axioms Clifford.MorleyKernel.children_eq_of_P0_Q0
#print axioms Clifford.MorleyKernel.hodd_one_P0_line

namespace Clifford.MorleyKernel
open Complex ComplexConjugate

/-- Cross-check: the general theorem re-derives J17's `d7_children_gcircleS`. -/
theorem d7_children_gcircleS' :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧ ∀ i : Fin 7,
      (↑(levelPointN 6 (crossVec (KP 6 (d7 ∘ i.succAbove)
        (fun r => conj ((d7 ∘ i.succAbove) r))))) : OnePoint ℂ) ∈ Y :=
  hodd_one_P0_line d7 d7_genPosN d7_P0 d7_children_P3

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.d7_children_gcircleS'
#check @Clifford.MorleyKernel.rowRel7_scalar
#check @Clifford.MorleyKernel.M7g_mulVec
#check @Clifford.MorleyKernel.det_M7_expand
#check @Clifford.MorleyKernel.det_M7_D
#check @Clifford.MorleyKernel.det_M7_F
#check @Clifford.MorleyKernel.child_det_M7
#check @Clifford.MorleyKernel.child_line_P0
#check @Clifford.MorleyKernel.collinear_of_reallin
#check @Clifford.MorleyKernel.children_eq_of_P0_Q0
#check @Clifford.MorleyKernel.hodd_one_P0_line
#check @Clifford.MorleyKernel.d7_children_gcircleS'


namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section J21
variable {R : Type*} [CommRing R]

def kpe (n : ℕ) (x y : R) (j : ℕ) : R :=
  if j ≤ n / 2 then (-x) ^ j * y ^ (n - n / 2 - j)
    else -((-x) ^ (j - (n / 2 + 1)) * y ^ (n - n / 2 - 1 - (j - (n / 2 + 1))))

theorem KP_eq_kpe (n : ℕ) (x y : Fin n → R) (r : Fin n) (j : Fin (n + 1)) :
    KP n x y r j = kpe n (x r) (y r) j := rfl

def extN {N : ℕ} (w : Fin N → R) (j : ℕ) : R := if h : j < N then w ⟨j, h⟩ else 0

theorem extN_fin {N : ℕ} (w : Fin N → R) (j : Fin N) : extN w j = w j := by
  simp [extN, j.isLt]

def gN (k : ℕ) (x y : R) (w : Fin (2 * k + 5) → R) : R :=
  ∑ j : Fin (2 * k + 5), kpe (2 * k + 4) x y j * w j

def colN (k : ℕ) (x y a b : R) (j : ℕ) : R :=
  if j = 0 then a else if j = 2 * k + 4 then b
    else kpe (2 * k + 5) x y (if j ≤ k + 2 then j else j + 1)

def uNat (k : ℕ) (xi yi : R) (W : ℕ → R) (j : ℕ) : R :=
  if j = 0 then -xi * W 0
    else if j ≤ k + 2 then -yi * W (j - 1) - xi * W j
    else if j = 2 * k + 4 then yi * W (k + 2)
    else -yi * W j - xi * W (j + 1)

def uN (k : ℕ) (xi yi : R) (w : Fin (2 * k + 5) → R) : Fin (2 * k + 5) → R :=
  fun j => uNat k xi yi (extN w) j

def MN (k : ℕ) (x y a b : Fin (2 * k + 5) → R) : Matrix (Fin (2 * k + 5)) (Fin (2 * k + 5)) R :=
  Matrix.of fun r j => colN k (x r) (y r) (a r) (b r) j

theorem rowRelN (k : ℕ) (x y xi yi z Z : R) (w : Fin (2 * k + 5) → R) :
    ∑ j : Fin (2 * k + 5), colN k x y (y ^ (k + 3) - Z * y ^ (k + 2))
        (z * -(-x) ^ (k + 2) - (-x) ^ (k + 3)) j * uN k xi yi w j
      - (yi * x - xi * y) * gN k x y w =
    -yi * (-x) ^ (k + 2) * (z * w ⟨k + 2, by omega⟩ + w ⟨2 * k + 4, by omega⟩) +
      xi * y ^ (k + 2) * (Z * w 0 - w ⟨k + 3, by omega⟩) := by
  set W := extN w with hW
  have hw0 : w 0 = W 0 := (extN_fin w 0).symm
  have hwa : w ⟨k + 2, by omega⟩ = W (k + 2) := (extN_fin w _).symm
  have hwb : w ⟨2 * k + 4, by omega⟩ = W (2 * k + 4) := (extN_fin w _).symm
  have hwc : w ⟨k + 3, by omega⟩ = W (k + 3) := (extN_fin w _).symm
  rw [hw0, hwa, hwb, hwc]
  set A := y ^ (k + 3) - Z * y ^ (k + 2) with hA
  set B := z * -(-x) ^ (k + 2) - (-x) ^ (k + 3) with hB
  have hS : ∑ j : Fin (2 * k + 5), colN k x y A B j * uN k xi yi w j =
      ∑ j ∈ Finset.range (2 * k + 5), colN k x y A B j * uNat k xi yi W j :=
    Fin.sum_univ_eq_sum_range (fun j => colN k x y A B j * uNat k xi yi W j) _
  have hG : gN k x y w = ∑ j ∈ Finset.range (2 * k + 5), kpe (2 * k + 4) x y j * W j := by
    rw [gN, ← Fin.sum_univ_eq_sum_range (fun j => kpe (2 * k + 4) x y j * W j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hW, extN_fin]
  rw [hS, hG]
  set F : ℕ → R := fun j => colN k x y A B j * uNat k xi yi W j with hF
  set G : ℕ → R := fun j => kpe (2 * k + 4) x y j * W j with hGd
  set p : ℕ → R := fun t => (-x) ^ t * y ^ (k + 2 - t) with hp
  set q : ℕ → R := fun t => (-x) ^ t * y ^ (k + 1 - t) with hq
  have e1 : 2 * k + 5 = (k + 3) + (k + 2) := by omega
  have h4 : (2 * k + 4) / 2 = k + 2 := by omega
  have h5 : (2 * k + 5) / 2 = k + 2 := by omega
  have hG1 : ∑ j ∈ Finset.range (2 * k + 5), G j =
      ∑ t ∈ Finset.range (k + 3), p t * W t - ∑ t ∈ Finset.range (k + 2), q t * W (k + 3 + t) := by
    rw [e1, Finset.sum_range_add, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun t ht => ?_
      have ht := Finset.mem_range.1 ht
      simp only [hGd, kpe, h4, hp, if_pos (show t ≤ k + 2 by omega)]
      rw [show 2 * k + 4 - (k + 2) - t = k + 2 - t by omega]
    · refine Finset.sum_congr rfl fun t ht => ?_
      have ht := Finset.mem_range.1 ht
      simp only [hGd, kpe, h4, hq, if_neg (show ¬ (k + 3 + t ≤ k + 2) by omega)]
      rw [show k + 3 + t - (k + 2 + 1) = t by omega, show 2 * k + 4 - (k + 2) - 1 - t = k + 1 - t by omega]
      ring
  have A0 : F 0 = A * (-xi * W 0) := by simp [hF, colN, uNat]
  have AL : F (k + 3 + (k + 1)) = B * (yi * W (k + 2)) := by
    rw [show k + 3 + (k + 1) = 2 * k + 4 by omega]
    simp only [hF, colN, uNat, if_neg (show 2 * k + 4 ≠ 0 by omega), if_true,
      if_neg (show ¬ (2 * k + 4 ≤ k + 2) by omega)]
  have A1 : ∀ t ∈ Finset.range (k + 2),
      F (t + 1) = (-x) ^ (t + 1) * y ^ (k + 2 - t) * (-yi * W t - xi * W (t + 1)) := by
    intro t ht
    have ht := Finset.mem_range.1 ht
    simp only [hF, colN, uNat, kpe, h5, if_neg (show t + 1 ≠ 0 by omega),
      if_neg (show t + 1 ≠ 2 * k + 4 by omega), if_pos (show t + 1 ≤ k + 2 by omega),
      Nat.add_sub_cancel]
    rw [show 2 * k + 5 - (k + 2) - (t + 1) = k + 2 - t by omega]
  have A2 : ∀ t ∈ Finset.range (k + 1),
      F (k + 3 + t) = (-((-x) ^ (t + 1) * y ^ (k + 1 - t))) *
          (-yi * W (k + 3 + t) - xi * W (k + 3 + t + 1)) := by
    intro t ht
    have ht := Finset.mem_range.1 ht
    simp only [hF, colN, uNat, kpe, h5, if_neg (show k + 3 + t ≠ 0 by omega),
      if_neg (show k + 3 + t ≠ 2 * k + 4 by omega), if_neg (show ¬ (k + 3 + t ≤ k + 2) by omega),
      if_neg (show ¬ (k + 3 + t + 1 ≤ k + 2) by omega)]
    rw [show k + 3 + t + 1 - (k + 2 + 1) = t + 1 by omega,
      show 2 * k + 5 - (k + 2) - 1 - (t + 1) = k + 1 - t by omega]
  have B1 := Finset.sum_range_succ' F (k + 2)
  have B2 := Finset.sum_range_succ (fun t => F (k + 3 + t)) (k + 1)
  rw [e1, Finset.sum_range_add, B1, B2, A0, AL, Finset.sum_congr rfl A1, Finset.sum_congr rfl A2, ← e1, hG1]
  have T1 : ∑ t ∈ Finset.range (k + 2), (-x) ^ (t + 1) * y ^ (k + 2 - t) * (-yi * W t - xi * W (t + 1)) =
      yi * x * ∑ t ∈ Finset.range (k + 2), p t * W t -
        xi * y * ∑ t ∈ Finset.range (k + 2), p (t + 1) * W (t + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht := Finset.mem_range.1 ht
    simp only [hp]
    rw [show k + 2 - t = (k + 2 - (t + 1)) + 1 by omega]
    ring
  have T2 : ∑ t ∈ Finset.range (k + 1), (-((-x) ^ (t + 1) * y ^ (k + 1 - t))) *
        (-yi * W (k + 3 + t) - xi * W (k + 3 + t + 1)) =
      -(yi * x) * ∑ t ∈ Finset.range (k + 1), q t * W (k + 3 + t) +
        xi * y * ∑ t ∈ Finset.range (k + 1), q (t + 1) * W (k + 3 + (t + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht := Finset.mem_range.1 ht
    simp only [hq]
    rw [show k + 1 - t = (k + 1 - (t + 1)) + 1 by omega, show k + 3 + t + 1 = k + 3 + (t + 1) by omega]
    ring
  rw [T1, T2]
  have P1 := Finset.sum_range_succ (fun t => p t * W t) (k + 2)
  have P2 := Finset.sum_range_succ' (fun t => p t * W t) (k + 2)
  have Q1 := Finset.sum_range_succ (fun t => q t * W (k + 3 + t)) (k + 1)
  have Q2 := Finset.sum_range_succ' (fun t => q t * W (k + 3 + t)) (k + 1)
  have pL : p (k + 2) = (-x) ^ (k + 2) := by simp [hp]
  have p0 : p 0 = y ^ (k + 2) := by simp [hp]
  have qL : q (k + 1) = (-x) ^ (k + 1) := by simp [hq]
  have q0 : q 0 = y ^ (k + 1) := by simp [hq]
  simp only [pL, p0, qL, q0, add_zero, show k + 3 + (k + 1) = 2 * k + 4 by omega] at P1 P2 Q1 Q2
  rw [hA, hB]
  linear_combination (-(yi * x)) * P1 + xi * y * P2 + yi * x * Q1 - xi * y * Q2


/-- **Matrix form of the row relation** (general `k`, general in the `2k+5` centres). -/
theorem MN_mulVec (k : ℕ) (x y : Fin (2 * k + 5) → R) (xi yi z Z : R) (w : Fin (2 * k + 5) → R)
    (r : Fin (2 * k + 5)) :
    (MN k x y (fun r => y r ^ (k + 3) - Z * y r ^ (k + 2))
        (fun r => z * -(-x r) ^ (k + 2) - (-x r) ^ (k + 3)) *ᵥ uN k xi yi w) r =
      (yi * x r - xi * y r) * gN k (x r) (y r) w +
        (-yi * (-x r) ^ (k + 2) * (z * w ⟨k + 2, by omega⟩ + w ⟨2 * k + 4, by omega⟩) +
          xi * y r ^ (k + 2) * (Z * w 0 - w ⟨k + 3, by omega⟩)) := by
  have h := rowRelN k (x r) (y r) xi yi z Z w
  simp only [MN, mulVec, dotProduct, Matrix.of_apply]
  linear_combination h

theorem MN_col_zero (k : ℕ) (x y a b : Fin (2 * k + 5) → R) (r : Fin (2 * k + 5)) :
    MN k x y a b r 0 = a r := by simp [MN, colN]

theorem MN_col_last (k : ℕ) (x y a b : Fin (2 * k + 5) → R) (r : Fin (2 * k + 5)) :
    MN k x y a b r (Fin.last _) = b r := by
  simp only [MN, colN, Matrix.of_apply, Fin.val_last, if_neg (show 2 * k + 4 ≠ 0 by omega), if_true]

theorem MN_col_mid (k : ℕ) (x y a b a' b' : Fin (2 * k + 5) → R) (r : Fin (2 * k + 5))
    (j : Fin (2 * k + 5)) (h0 : (j : ℕ) ≠ 0) (hL : (j : ℕ) ≠ 2 * k + 4) :
    MN k x y a b r j = MN k x y a' b' r j := by
  simp only [MN, colN, Matrix.of_apply, if_neg h0, if_neg hL]

/-- Linearity of `det MN` in the first column. -/
theorem det_MN_left (k : ℕ) (x y a a' b : Fin (2 * k + 5) → R) (s : R) :
    (MN k x y (fun r => a r + s * a' r) b).det = (MN k x y a b).det + s * (MN k x y a' b).det := by
  have key : ∀ a₁ : Fin (2 * k + 5) → R, updateCol (MN k x y a b) 0 a₁ = MN k x y a₁ b := by
    intro a₁; ext r j
    by_cases h0 : (j : ℕ) = 0
    · have : j = 0 := Fin.ext h0
      subst this; rw [updateCol_self, MN_col_zero]
    · rw [updateCol_ne (fun e => h0 (by rw [e]; rfl))]
      by_cases hL : (j : ℕ) = 2 * k + 4
      · have : j = Fin.last _ := Fin.ext hL
        subst this; rw [MN_col_last, MN_col_last]
      · exact MN_col_mid k x y a b a₁ b r j h0 hL
  have : (fun r => a r + s * a' r) = a + s • a' := by funext r; simp
  rw [this, ← key (a + s • a'), det_updateCol_add, det_updateCol_smul, key, key]

/-- Linearity of `det MN` in the last column. -/
theorem det_MN_right (k : ℕ) (x y a b b' : Fin (2 * k + 5) → R) (s : R) :
    (MN k x y a (fun r => b r + s * b' r)).det = (MN k x y a b).det + s * (MN k x y a b').det := by
  have key : ∀ b₁ : Fin (2 * k + 5) → R, updateCol (MN k x y a b) (Fin.last _) b₁ = MN k x y a b₁ := by
    intro b₁; ext r j
    by_cases hL : (j : ℕ) = 2 * k + 4
    · have : j = Fin.last _ := Fin.ext hL
      subst this; rw [updateCol_self, MN_col_last]
    · rw [updateCol_ne (fun e => hL (by rw [e]; rfl))]
      by_cases h0 : (j : ℕ) = 0
      · have : j = 0 := Fin.ext h0
        subst this; rw [MN_col_zero, MN_col_zero]
      · exact MN_col_mid k x y a b a b₁ r j h0 hL
  have : (fun r => b r + s * b' r) = b + s • b' := by funext r; simp
  rw [this, ← key (b + s • b'), det_updateCol_add, det_updateCol_smul, key, key]

/-- **Bilinear expansion** at general `k`: `det = E₀ + z·D + Z·G + z Z·F`. -/
theorem det_MN_expand (k : ℕ) (x y : Fin (2 * k + 5) → R) (z Z : R) :
    (MN k x y (fun r => y r ^ (k + 3) - Z * y r ^ (k + 2))
        (fun r => z * -(-x r) ^ (k + 2) - (-x r) ^ (k + 3))).det =
      (MN k x y (fun r => y r ^ (k + 3)) (fun r => -(-x r) ^ (k + 3))).det +
        z * (MN k x y (fun r => y r ^ (k + 3)) (fun r => -(-x r) ^ (k + 2))).det +
        Z * (MN k x y (fun r => -y r ^ (k + 2)) (fun r => -(-x r) ^ (k + 3))).det +
        z * Z * (MN k x y (fun r => -y r ^ (k + 2)) (fun r => -(-x r) ^ (k + 2))).det := by
  have ea : (fun r => y r ^ (k + 3) - Z * y r ^ (k + 2)) =
      fun r => y r ^ (k + 3) + Z * (-y r ^ (k + 2)) := by funext r; ring
  have eb : (fun r => z * -(-x r) ^ (k + 2) - (-x r) ^ (k + 3)) =
      fun r => -(-x r) ^ (k + 3) + z * (-(-x r) ^ (k + 2)) := by funext r; ring
  rw [ea, eb, det_MN_left, det_MN_right, det_MN_right]
  ring

theorem kpe_P0 (k : ℕ) (x y : R) : kpe (2 * k + 5) x y 0 = y ^ (k + 3) := by
  simp only [kpe, Nat.zero_le, if_true, pow_zero, one_mul, Nat.sub_zero]
  congr 1; omega

theorem kpe_Q0 (k : ℕ) (x y : R) : kpe (2 * k + 5) x y (k + 3) = -y ^ (k + 2) := by
  have h5 : (2 * k + 5) / 2 = k + 2 := by omega
  simp only [kpe, h5, if_neg (show ¬ (k + 3 ≤ k + 2) by omega), Nat.sub_self, pow_zero, one_mul]
  congr 2; omega

theorem kpe_QL (k : ℕ) (x y : R) : kpe (2 * k + 5) x y (2 * k + 5) = -(-x) ^ (k + 2) := by
  have h5 : (2 * k + 5) / 2 = k + 2 := by omega
  simp only [kpe, h5, if_neg (show ¬ (2 * k + 5 ≤ k + 2) by omega)]
  rw [show 2 * k + 5 - (k + 2 + 1) = k + 2 by omega,
    show 2 * k + 5 - (k + 2) - 1 - (k + 2) = 0 by omega, pow_zero, mul_one]

/-- The `z`-coefficient is the parent coordinate `Q₀(v) = crossVec (KP (2k+5)) ⟨k+3⟩`, up to the
explicit sign `(-1)^(k+3)` (`= +1` at `k = 1`, recovering `det_M7_D`). -/
theorem det_MN_D (k : ℕ) (x y : Fin (2 * k + 5) → R) :
    (MN k x y (fun r => y r ^ (k + 3)) (fun r => -(-x r) ^ (k + 2))).det =
      (-1) ^ (k + 3) * crossVec (KP (2 * k + 5) x y) ⟨k + 3, by omega⟩ := by
  have e : MN k x y (fun r => y r ^ (k + 3)) (fun r => -(-x r) ^ (k + 2)) =
      (KP (2 * k + 5) x y).submatrix id (Fin.succAbove ⟨k + 3, by omega⟩) := by
    ext r j
    simp only [Matrix.submatrix_apply, id, KP_eq_kpe]
    have hv := val_succAbove (⟨k + 3, by omega⟩ : Fin (2 * k + 6)) j
    simp only [Fin.val_mk] at hv
    rw [hv]
    by_cases h0 : (j : ℕ) = 0
    · have : j = 0 := Fin.ext h0
      subst this; rw [MN_col_zero, Fin.val_zero, if_pos (show 0 < k + 3 by omega), kpe_P0]
    · by_cases hL : (j : ℕ) = 2 * k + 4
      · have : j = Fin.last _ := Fin.ext hL
        subst this; rw [MN_col_last, Fin.val_last, if_neg (show ¬ (2 * k + 4 < k + 3) by omega),
          show 2 * k + 4 + 1 = 2 * k + 5 by omega, kpe_QL]
      · simp only [MN, colN, Matrix.of_apply, if_neg h0, if_neg hL]
        congr 1
        by_cases hj : (j : ℕ) ≤ k + 2
        · rw [if_pos hj, if_pos (by omega)]
        · rw [if_neg hj, if_neg (by omega)]
  rw [e, crossVec]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

/-- The column permutation `sigN k = (cycleRange ⟨k+2⟩)⁻¹` (generalises `sig7`):
`0 ↦ k+2`, `j ↦ j-1` for `1 ≤ j ≤ k+2`, `j ↦ j` beyond. -/
def sigN (k : ℕ) : Equiv.Perm (Fin (2 * k + 5)) := (Fin.cycleRange ⟨k + 2, by omega⟩).symm

theorem sign_sigN (k : ℕ) : (Equiv.Perm.sign (sigN k) : ℤ) = (-1) ^ (k + 2) := by
  rw [sigN, Equiv.Perm.sign_symm, Fin.sign_cycleRange]; simp

theorem sigN_one : sigN 1 = sig7 := by
  ext j; fin_cases j <;> rfl

theorem val_cycleRange {n : ℕ} (i j : Fin n) :
    ((Fin.cycleRange i j : Fin n) : ℕ) = if (j : ℕ) < i then (j : ℕ) + 1 else if (j : ℕ) = i then 0 else j := by
  rcases lt_trichotomy j i with h | h | h
  · rw [Fin.coe_cycleRange_of_lt h, if_pos (Fin.lt_def.1 h)]
  · subst h; rw [Fin.coe_cycleRange_of_le le_rfl]; simp
  · have h' := Fin.lt_def.1 h
    rw [Fin.cycleRange_of_gt h, if_neg (by omega), if_neg (by omega)]

/-- The `z Z`-coefficient is `± P₀(v)`, sign `sign (sigN k) = (-1)^(k+2)` (`det_M7_F` at `k = 1`). -/
theorem det_MN_F (k : ℕ) (x y : Fin (2 * k + 5) → R) :
    (MN k x y (fun r => -y r ^ (k + 2)) (fun r => -(-x r) ^ (k + 2))).det =
      Equiv.Perm.sign (sigN k) * crossVec (KP (2 * k + 5) x y) 0 := by
  have e : (MN k x y (fun r => -y r ^ (k + 2)) (fun r => -(-x r) ^ (k + 2))).submatrix id
        (Fin.cycleRange ⟨k + 2, by omega⟩) =
      (KP (2 * k + 5) x y).submatrix id (Fin.succAbove 0) := by
    ext r j
    simp only [Matrix.submatrix_apply, id, KP_eq_kpe, Fin.succAbove_zero, Fin.val_succ]
    have hv := val_cycleRange (⟨k + 2, by omega⟩ : Fin (2 * k + 5)) j
    simp only at hv
    simp only [MN, colN, Matrix.of_apply]
    rw [hv]
    by_cases h1 : (j : ℕ) < k + 2
    · simp only [if_pos h1, if_neg (show (j : ℕ) + 1 ≠ 0 by omega),
        if_neg (show (j : ℕ) + 1 ≠ 2 * k + 4 by omega), if_pos (show (j : ℕ) + 1 ≤ k + 2 by omega)]
    · by_cases h2 : (j : ℕ) = k + 2
      · simp only [if_neg h1, if_pos h2, if_true]
        rw [h2, kpe_Q0]
      · simp only [if_neg h1, if_neg h2]
        by_cases hL : (j : ℕ) = 2 * k + 4
        · simp only [if_neg (show (j : ℕ) ≠ 0 by omega), if_pos hL]
          rw [hL, kpe_QL]
        · simp only [if_neg (show (j : ℕ) ≠ 0 by omega), if_neg hL,
            if_neg (show ¬ ((j : ℕ) ≤ k + 2) by omega)]
  have h := det_permute' (Fin.cycleRange (⟨k + 2, by omega⟩ : Fin (2 * k + 5)))
    (MN k x y (fun r => -y r ^ (k + 2)) (fun r => -(-x r) ^ (k + 2)))
  rw [e] at h
  have hs : ((Equiv.Perm.sign (Fin.cycleRange (⟨k + 2, by omega⟩ : Fin (2 * k + 5))) : ℤ) : R) =
      (-1) ^ (k + 2) := by rw [Fin.sign_cycleRange]; simp
  have hs' : ((Equiv.Perm.sign (sigN k) : ℤ) : R) = (-1) ^ (k + 2) := by
    rw [sign_sigN]; simp
  rw [hs] at h
  rw [hs', crossVec]
  simp only [Fin.val_zero, pow_zero, one_mul]
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp


/-- Consistency: at `k = 1` the merged matrix is J19's `M7g`. -/
theorem MN_one (x y a b : Fin 7 → R) : MN 1 x y a b = M7g x y a b := by
  ext r j; fin_cases j <;> simp [MN, colN, M7g, kpe] <;> ring

/-- Consistency: at `k = 1` the coefficient vector is J19's `u7v`. -/
theorem uN_one (xi yi : R) (w : Fin 7 → R) : uN 1 xi yi w = u7v xi yi w := by
  funext j; fin_cases j <;> simp [uN, uNat, u7v, extN]

end J21
end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.rowRelN
#print axioms Clifford.MorleyKernel.MN_mulVec
#print axioms Clifford.MorleyKernel.det_MN_left
#print axioms Clifford.MorleyKernel.det_MN_right
#print axioms Clifford.MorleyKernel.det_MN_expand
#print axioms Clifford.MorleyKernel.det_MN_D
#print axioms Clifford.MorleyKernel.sign_sigN
#print axioms Clifford.MorleyKernel.sigN_one
#print axioms Clifford.MorleyKernel.det_MN_F
#print axioms Clifford.MorleyKernel.MN_one
#print axioms Clifford.MorleyKernel.uN_one

/-! ## J21 Target B — `hodd_P0_line` at general `k` -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- Row `r` of `KP (2k+4)` applied to its own cross vector, in `gN` form. -/
theorem gN_crossVec (k : ℕ) (x y : Fin (2 * k + 4) → ℂ) (r : Fin (2 * k + 4)) :
    gN k (x r) (y r) (crossVec (KP (2 * k + 4) x y)) = 0 :=
  congrFun (mulVec_crossVec (KP (2 * k + 4) x y)) r

/-- **Every child level point satisfies `det MN(z, z̄) = 0`** (general `k`). -/
theorem child_det_MN (k : ℕ) (c : Fin (2 * k + 5) → ℂ) (hc : ∀ j, c j ≠ 0) (i : Fin (2 * k + 5))
    (hPi : crossVec (KP (2 * k + 4) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r)))
      ⟨k + 2, by omega⟩ ≠ 0) :
    let z := levelPointN (2 * k + 4)
      (crossVec (KP (2 * k + 4) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))))
    (MN k c (fun r => conj (c r)) (fun r => conj (c r) ^ (k + 3) - conj z * conj (c r) ^ (k + 2))
      (fun r => z * -(-c r) ^ (k + 2) - (-c r) ^ (k + 3))).det = 0 := by
  intro z
  set s := c ∘ i.succAbove with hs
  set w := crossVec (KP (2 * k + 4) s (fun r => conj (s r))) with hw
  have hwa : w ⟨k + 2, by omega⟩ ≠ 0 := hPi
  have hw0 : w 0 ≠ 0 := crossVec_even_P0_ne_zero (k + 1) s hPi
  have hz : z * w ⟨k + 2, by omega⟩ + w ⟨2 * k + 4, by omega⟩ = 0 := by
    have e1 : (⟨(2 * k + 4) / 2, by omega⟩ : Fin (2 * k + 4 + 1)) = ⟨k + 2, by omega⟩ := by
      ext; simp only; omega
    have e2 : (Fin.last (2 * k + 4)) = (⟨2 * k + 4, by omega⟩ : Fin (2 * k + 4 + 1)) := rfl
    show -w (Fin.last (2 * k + 4)) / w ⟨(2 * k + 4) / 2, by omega⟩ * w ⟨k + 2, by omega⟩ +
      w ⟨2 * k + 4, by omega⟩ = 0
    rw [e1, div_mul_cancel₀ _ hwa, e2]; ring
  have hZ : conj z * w 0 - w ⟨k + 3, by omega⟩ = 0 := by
    have h := conj_levelPointN_even (k + 1) s
    have h' : conj z = w ⟨k + 3, by omega⟩ / w 0 := h
    rw [h', div_mul_cancel₀ _ hw0, sub_self]
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨uN k (c i) (conj (c i)) w, ?_, ?_⟩
  · intro h0
    have := congrFun h0 0
    simp only [uN, uNat, extN, Fin.val_zero, if_true, Pi.zero_apply, dif_pos (show 0 < 2 * k + 5 by omega),
      neg_mul, neg_eq_zero, mul_eq_zero] at this
    exact this.elim (hc i) hw0
  · funext r
    rw [MN_mulVec, hz, hZ, Pi.zero_apply]
    rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨t, rfl⟩
    · ring
    · have h1 : gN k (s t) (conj (s t)) w = 0 := gN_crossVec k s (fun r => conj (s r)) t
      have h2 : s t = c (i.succAbove t) := rfl
      rw [h2] at h1
      rw [h1]; ring

/-- **With `P₀ = 0`, every child level point lies on the real line**
`E₀ + (-1)^(k+3) Q₀(v)·z + G·z̄ = 0` (general `k`; `child_line_P0` at `k = 1`). -/
theorem child_line_P0N (k : ℕ) (c : Fin (2 * k + 5) → ℂ) (hc : ∀ j, c j ≠ 0)
    (hP0 : crossVec (KP (2 * k + 5) c (fun j => conj (c j))) 0 = 0) (i : Fin (2 * k + 5))
    (hPi : crossVec (KP (2 * k + 4) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r)))
      ⟨k + 2, by omega⟩ ≠ 0) :
    let z := levelPointN (2 * k + 4)
      (crossVec (KP (2 * k + 4) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))))
    (MN k c (fun r => conj (c r)) (fun r => conj (c r) ^ (k + 3)) (fun r => -(-c r) ^ (k + 3))).det +
      (-1) ^ (k + 3) * crossVec (KP (2 * k + 5) c (fun j => conj (c j))) ⟨k + 3, by omega⟩ * z +
      (MN k c (fun r => conj (c r)) (fun r => -conj (c r) ^ (k + 2))
        (fun r => -(-c r) ^ (k + 3))).det * conj z = 0 := by
  intro z
  have h := child_det_MN k c hc i hPi
  simp only at h
  rw [det_MN_expand, det_MN_D, det_MN_F, hP0] at h
  linear_combination h

/-- A kernel vector of the parent `KP (2k+5)` without its last column kills every child (general `k`). -/
theorem child_mulVec_of_parentN (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (hd : ∀ j, d j ≠ 0)
    (V : Fin (2 * k + 5) → ℂ)
    (hV : (KP (2 * k + 5) d (fun j => conj (d j))).submatrix id (Fin.last (2 * k + 5)).succAbove *ᵥ V = 0)
    (i : Fin (2 * k + 5)) :
    KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)) *ᵥ V = 0 := by
  funext r
  have h := congrFun hV (i.succAbove r)
  have e : ∀ l, (KP (2 * k + 5) d (fun j => conj (d j))) (i.succAbove r) ((Fin.last (2 * k + 5)).succAbove l) =
      conj (d (i.succAbove r)) * KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)) r l :=
    fun l => subRowsOdd_entry (k + 1) d (fun j => conj (d j)) i r l
  simp only [mulVec, dotProduct, Matrix.submatrix_apply, id, e, Pi.zero_apply] at h ⊢
  simp only [mul_assoc] at h
  rw [← Finset.mul_sum] at h
  exact (mul_eq_zero.1 h).resolve_left ((map_ne_zero _).2 (hd _))

/-- The level point of a rank-`(2k+4)` matrix read off any nonzero kernel vector (general `k`). -/
theorem levelPointN_of_ker (k : ℕ) (A : Matrix (Fin (2 * k + 4)) (Fin (2 * k + 5)) ℂ)
    (h3 : crossVec A ⟨k + 2, by omega⟩ ≠ 0)
    (V : Fin (2 * k + 5) → ℂ) (hV : A *ᵥ V = 0) (hV0 : V ≠ 0) :
    levelPointN (2 * k + 4) (crossVec A) = -V (Fin.last _) / V ⟨k + 2, by omega⟩ := by
  have hk := ker_eq_span_crossVec A ⟨k + 2, by omega⟩ h3
  have hmem : V ∈ LinearMap.ker A.mulVecLin := by simpa using hV
  rw [hk, Submodule.mem_span_singleton] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hs0 : s ≠ 0 := by rintro rfl; exact hV0 (by rw [← hs, zero_smul])
  have e3 := congrFun hs ⟨k + 2, by omega⟩
  have e6 := congrFun hs (Fin.last _)
  simp only [Pi.smul_apply, smul_eq_mul] at e3 e6
  have e : (⟨(2 * k + 4) / 2, by omega⟩ : Fin (2 * k + 4 + 1)) = ⟨k + 2, by omega⟩ := by
    ext; simp only; omega
  rw [levelPointN, e, ← e3, ← e6, neg_div, neg_div, mul_div_mul_left _ _ hs0]

/-- With `P₀ = 0`: `Q₀ = 0` forces `Q_{k+2} = 0` (odd Plücker via `kernel_eq_zero_of_P0`). -/
theorem QL_zero_of_P0_Q0 (k : ℕ) (d : Fin (2 * k + 5) → ℂ)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 = 0)
    (hQ0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) ⟨k + 3, by omega⟩ = 0) :
    crossVec (KP (2 * k + 5) d (fun j => conj (d j))) (Fin.last _) = 0 := by
  have h := kernel_eq_zero_of_P0 k d hP0 0
  rw [oddCircleEq_of_P0_zero _ _ hP0] at h
  change crossVec (KP (2 * k + 5) d (fun j => conj (d j))) ⟨k + 3, by omega⟩ *
      conj (crossVec (KP (2 * k + 5) d (fun j => conj (d j))) ⟨k + 3, by omega⟩) -
    crossVec (KP (2 * k + 5) d (fun j => conj (d j))) (Fin.last _) *
      conj (crossVec (KP (2 * k + 5) d (fun j => conj (d j))) (Fin.last _)) = 0 at h
  rw [hQ0, zero_mul, zero_sub, neg_eq_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · exact (map_eq_zero _).1 h

/-- **Degenerate branch (general `k`).** If `P₀ = Q₀ = 0`, all `2k+5` child level points coincide. -/
theorem children_eq_of_P0_Q0N (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (hd : ∀ j, d j ≠ 0)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 = 0)
    (hQ0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) ⟨k + 3, by omega⟩ = 0)
    (hPi : ∀ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
      (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ ≠ 0) :
    ∃ p : ℂ, ∀ i : Fin (2 * k + 5),
      levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r)))) = p := by
  have hL := QL_zero_of_P0_Q0 k d hP0 hQ0
  have hdet : ((KP (2 * k + 5) d (fun j => conj (d j))).submatrix id
      (Fin.last (2 * k + 5)).succAbove).det = 0 := by
    unfold crossVec at hL
    exact (mul_eq_zero.1 hL).resolve_left (pow_ne_zero _ (by norm_num))
  obtain ⟨V, hV0, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  exact ⟨-V (Fin.last _) / V ⟨k + 2, by omega⟩, fun i => levelPointN_of_ker k _ (hPi i) V
    (child_mulVec_of_parentN k d hd V hV i) hV0⟩

/-- **Target B (general `k`).** `2k+5` centres in general position with `P₀ = 0`: the `2k+5` child
level points lie on one generalized circle — a line (`lineS`). -/
theorem hodd_P0_line (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (h : GenPosN d)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 = 0)
    (hPi : ∀ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
             (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ ≠ 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * k + 5), (↑(levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))))) : OnePoint ℂ) ∈ Y := by
  have hd : ∀ j, d j ≠ 0 := hc_of_genPos (by omega) d h
  by_cases hQ0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) ⟨k + 3, by omega⟩ = 0
  · obtain ⟨p, hp⟩ := children_eq_of_P0_Q0N k d hd hP0 hQ0 hPi
    refine ⟨Clifford.lineS p 1, Or.inr ⟨p, 1, one_ne_zero, rfl⟩, fun i => ?_⟩
    refine Set.mem_insert_of_mem _ ⟨_, ⟨0, ?_⟩, rfl⟩
    rw [hp i]; simp
  · have hl0 : (-1 : ℂ) ^ (k + 3) * crossVec (KP (2 * k + 5) d (fun j => conj (d j))) ⟨k + 3, by omega⟩ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) hQ0
    obtain ⟨p, u, hu, ht⟩ := collinear_of_reallin
      (fun i : Fin (2 * k + 5) => levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))))) 0
      ((-1 : ℂ) ^ (k + 3) * crossVec (KP (2 * k + 5) d (fun j => conj (d j))) ⟨k + 3, by omega⟩)
      (MN k d (fun r => conj (d r)) (fun r => -conj (d r) ^ (k + 2)) (fun r => -(-d r) ^ (k + 3))).det
      (MN k d (fun r => conj (d r)) (fun r => conj (d r) ^ (k + 3)) (fun r => -(-d r) ^ (k + 3))).det hl0
      (fun i => by
        have hl := child_line_P0N k d hd hP0 i (hPi i)
        simp only at hl
        linear_combination hl)
    refine ⟨Clifford.lineS p u, Or.inr ⟨p, u, hu, rfl⟩, fun i => ?_⟩
    obtain ⟨t, htt⟩ := ht i
    refine Set.mem_insert_of_mem _ ⟨_, ⟨t, ?_⟩, rfl⟩
    rw [Complex.real_smul]
    exact htt

/-- **Mandatory consistency check:** J19's `hodd_one_P0_line`, re-derived as `hodd_P0_line 1`. -/
theorem hodd_one_P0_line' (d : Fin 7 → ℂ) (h : GenPosN d)
    (hP0 : crossVec (KP 7 d (fun j => conj (d j))) 0 = 0)
    (hPi : ∀ i : Fin 7, crossVec (KP 6 (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r))) ⟨3, by omega⟩ ≠ 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin 7, (↑(levelPointN 6 (crossVec (KP 6 (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))))) : OnePoint ℂ) ∈ Y :=
  hodd_P0_line 1 d h hP0 hPi

/-- Second cross-check: J17's seven-centre witness through the general-`k` theorem. -/
theorem d7_children_gcircleS'' :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧ ∀ i : Fin 7,
      (↑(levelPointN 6 (crossVec (KP 6 (d7 ∘ i.succAbove)
        (fun r => conj ((d7 ∘ i.succAbove) r))))) : OnePoint ℂ) ∈ Y :=
  hodd_P0_line 1 d7 d7_genPosN d7_P0 d7_children_P3

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.gN_crossVec
#print axioms Clifford.MorleyKernel.child_det_MN
#print axioms Clifford.MorleyKernel.child_line_P0N
#print axioms Clifford.MorleyKernel.child_mulVec_of_parentN
#print axioms Clifford.MorleyKernel.levelPointN_of_ker
#print axioms Clifford.MorleyKernel.QL_zero_of_P0_Q0
#print axioms Clifford.MorleyKernel.children_eq_of_P0_Q0N
#print axioms Clifford.MorleyKernel.hodd_P0_line
#print axioms Clifford.MorleyKernel.hodd_one_P0_line'
#print axioms Clifford.MorleyKernel.d7_children_gcircleS''
#check @Clifford.MorleyKernel.rowRelN
#check @Clifford.MorleyKernel.MN_mulVec
#check @Clifford.MorleyKernel.det_MN_left
#check @Clifford.MorleyKernel.det_MN_right
#check @Clifford.MorleyKernel.det_MN_expand
#check @Clifford.MorleyKernel.det_MN_D
#check @Clifford.MorleyKernel.det_MN_F
#check @Clifford.MorleyKernel.sign_sigN
#check @Clifford.MorleyKernel.sigN_one
#check @Clifford.MorleyKernel.MN_one
#check @Clifford.MorleyKernel.uN_one
#check @Clifford.MorleyKernel.child_det_MN
#check @Clifford.MorleyKernel.child_line_P0N
#check @Clifford.MorleyKernel.children_eq_of_P0_Q0N
#check @Clifford.MorleyKernel.hodd_P0_line
#check @Clifford.MorleyKernel.hodd_one_P0_line'
#check @Clifford.MorleyKernel.d7_children_gcircleS''

/-! ## J22 — the odd payload `hodd` of `cliffordChainS_all_of` at general `k`, for `E := EptInf`

The `hodd` argument of `Clifford.cliffordChainS_all_of` asks, for `E := EptInf`,
`∃ Y, IsGCircleS Y ∧ ∀ i, EptInf (2k+4) (d ∘ i.succAbove) ∈ Y`.
* `P₀ ≠ 0`: the kernel circle (`kernelCircle_isGCircleS`), children on it by `stepOdd_gen`;
  needs the child middle coordinates `P_{k+2} ≠ 0` (a circle of `ℂ` does not contain `∞`).
* `P₀ = 0`: a line `lineS` (contains `∞`); children with `P_{k+2} ≠ 0` are on the real line of
  `child_line_P0N` / coincide (`P₀ = Q₀ = 0`), children with `P_{k+2} = 0` are `∞`. No child
  hypothesis is needed in this branch. -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

theorem EptInf_child_eq_coe (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (i : Fin (2 * k + 5))
    (hPi : crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)))
      ⟨k + 2, by omega⟩ ≠ 0) :
    EptInf (2 * k + 4) (d ∘ i.succAbove) =
      (↑(levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))))) : OnePoint ℂ) := by
  have e : (⟨(2 * k + 4) / 2, by omega⟩ : Fin (2 * k + 4 + 1)) = ⟨k + 2, by omega⟩ := by
    ext; simp only; omega
  rw [EptInf_eq_coe _ _ (by rw [e]; exact hPi)]
  rfl

theorem EptInf_child_eq_infty (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (i : Fin (2 * k + 5))
    (hPi : crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)))
      ⟨k + 2, by omega⟩ = 0) :
    EptInf (2 * k + 4) (d ∘ i.succAbove) = OnePoint.infty := by
  have e : (⟨(2 * k + 4) / 2, by omega⟩ : Fin (2 * k + 4 + 1)) = ⟨k + 2, by omega⟩ := by
    ext; simp only; omega
  exact EptInf_eq_infty _ _ (by rw [e]; exact hPi)

/-- **`P₀ ≠ 0` branch** for `E := EptInf`: the kernel circle. -/
theorem hodd_inf_P0_ne (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (h : GenPosN d)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0)
    (hPi : ∀ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
             (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ ≠ 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * k + 5), EptInf (2 * k + 4) (d ∘ i.succAbove) ∈ Y := by
  obtain ⟨Y, hY, hm⟩ := hodd_levelPoint k d (hc_of_genPos (by omega) d h) hP0 hPi
  exact ⟨Y, hY, fun i => by rw [EptInf_child_eq_coe k d i (hPi i)]; exact hm i⟩

/-- **`P₀ = 0` branch** for `E := EptInf`: a line through `∞`, no child hypothesis. -/
theorem hodd_inf_P0_eq (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (h : GenPosN d)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 = 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * k + 5), EptInf (2 * k + 4) (d ∘ i.succAbove) ∈ Y := by
  have hd : ∀ j, d j ≠ 0 := hc_of_genPos (by omega) d h
  set G : Fin (2 * k + 5) → Prop := fun i => crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
    (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ ≠ 0 with hG
  -- it suffices to put the good children (finite level point) on a line `lineS p u`
  suffices H : ∃ p u : ℂ, u ≠ 0 ∧ ∀ i (hi : G i), ∃ t : ℝ,
      levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r)))) = p + t • u by
    obtain ⟨p, u, hu, ht⟩ := H
    refine ⟨Clifford.lineS p u, Or.inr ⟨p, u, hu, rfl⟩, fun i => ?_⟩
    by_cases hi : G i
    · rw [EptInf_child_eq_coe k d i hi]
      obtain ⟨t, htt⟩ := ht i hi
      exact Set.mem_insert_of_mem _ ⟨_, ⟨t, htt⟩, rfl⟩
    · rw [EptInf_child_eq_infty k d i (not_not.1 hi)]
      exact Set.mem_insert _ _
  by_cases hQ0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) ⟨k + 3, by omega⟩ = 0
  · -- all good children coincide
    have hL := QL_zero_of_P0_Q0 k d hP0 hQ0
    have hdet : ((KP (2 * k + 5) d (fun j => conj (d j))).submatrix id
        (Fin.last (2 * k + 5)).succAbove).det = 0 := by
      unfold crossVec at hL
      exact (mul_eq_zero.1 hL).resolve_left (pow_ne_zero _ (by norm_num))
    obtain ⟨V, hV0, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    refine ⟨-V (Fin.last _) / V ⟨k + 2, by omega⟩, 1, one_ne_zero, fun i hi => ⟨0, ?_⟩⟩
    rw [levelPointN_of_ker k _ hi V (child_mulVec_of_parentN k d hd V hV i) hV0]
    simp
  · have hl0 : (-1 : ℂ) ^ (k + 3) * crossVec (KP (2 * k + 5) d (fun j => conj (d j)))
        ⟨k + 3, by omega⟩ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) hQ0
    by_cases hne : ∃ i0, G i0
    · obtain ⟨i0, hi0⟩ := hne
      obtain ⟨p, u, hu, ht⟩ := collinear_of_reallin
        (fun i : {i : Fin (2 * k + 5) // G i} => levelPointN (2 * k + 4)
          (crossVec (KP (2 * k + 4) (d ∘ i.1.succAbove)
          (fun r => conj ((d ∘ i.1.succAbove) r))))) ⟨i0, hi0⟩
        ((-1 : ℂ) ^ (k + 3) * crossVec (KP (2 * k + 5) d (fun j => conj (d j))) ⟨k + 3, by omega⟩)
        (MN k d (fun r => conj (d r)) (fun r => -conj (d r) ^ (k + 2))
          (fun r => -(-d r) ^ (k + 3))).det
        (MN k d (fun r => conj (d r)) (fun r => conj (d r) ^ (k + 3))
          (fun r => -(-d r) ^ (k + 3))).det hl0
        (fun i => by
          have hl := child_line_P0N k d hd hP0 i.1 i.2
          simp only at hl
          linear_combination hl)
      refine ⟨p, u, hu, fun i hi => ?_⟩
      obtain ⟨t, htt⟩ := ht ⟨i, hi⟩
      exact ⟨t, by rw [Complex.real_smul]; exact htt⟩
    · exact ⟨0, 1, one_ne_zero, fun i hi => absurd ⟨i, hi⟩ hne⟩

/-- **J22 — the odd payload at general `k`, both `P₀` branches, for `E := EptInf`.** The conclusion
is exactly the body of the `hodd` argument of `Clifford.cliffordChainS_all_of` at `E := EptInf`.
The only extra hypothesis is the child non-degeneracy, and only in the circle branch `P₀ ≠ 0`. -/
theorem hodd_inf (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (h : GenPosN d)
    (hPi : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0 →
      ∀ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ ≠ 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * k + 5), EptInf (2 * k + 4) (d ∘ i.succAbove) ∈ Y := by
  by_cases hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 = 0
  · exact hodd_inf_P0_eq k d h hP0
  · exact hodd_inf_P0_ne k d h hP0 (hPi hP0)

/-- `hodd` in the exact quantified form consumed by `cliffordChainS_all_of` (`E := EptInf`),
from the child non-degeneracy in the circle branch. -/
theorem hodd_inf_all
    (hPi : ∀ (k : ℕ) (d : Fin (2 * k + 5) → ℂ), GenPosN d →
      crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0 →
      ∀ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ ≠ 0) :
    ∀ (k : ℕ) (d : Fin (2 * k + 5) → ℂ), GenPosN d →
      ∃ Y, Clifford.IsGCircleS Y ∧ ∀ i : Fin (2 * k + 5), EptInf (2 * k + 4) (d ∘ i.succAbove) ∈ Y :=
  fun k d h => hodd_inf k d h (hPi k d h)

/-- At `k = 0` the child hypothesis is discharged by `GenPosN` (`P₂ = mD ≠ 0`): unconditional. -/
theorem hodd_inf_zero (d : Fin (2 * 0 + 5) → ℂ) (h : GenPosN d) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * 0 + 5), EptInf (2 * 0 + 4) (d ∘ i.succAbove) ∈ Y :=
  hodd_inf 0 d h (fun _ i => crossVec_KP4_P2_ne_zero _ (h.comp_succAbove i))

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.EptInf_child_eq_coe
#print axioms Clifford.MorleyKernel.EptInf_child_eq_infty
#print axioms Clifford.MorleyKernel.hodd_inf_P0_ne
#print axioms Clifford.MorleyKernel.hodd_inf_P0_eq
#print axioms Clifford.MorleyKernel.hodd_inf
#print axioms Clifford.MorleyKernel.hodd_inf_all
#print axioms Clifford.MorleyKernel.hodd_inf_zero
#check @Clifford.MorleyKernel.hodd_inf
#check @Clifford.MorleyKernel.hodd_inf_all
#check @Clifford.MorleyKernel.hodd_inf_zero

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- **Consumer check**: `hodd_inf_all` plugs into `cliffordChainS_all_of` at `E := EptInf`
(with `h4 := h4_pt_inf`); only `heven` for `EptInf` and the circle-branch child condition remain. -/
theorem cliffordChainS_of_inf
    (hPi : ∀ (k : ℕ) (d : Fin (2 * k + 5) → ℂ), GenPosN d →
      crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0 →
      ∀ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ ≠ 0)
    (heven : ∀ (k : ℕ) (c : Fin (2 * k + 6) → ℂ), GenPosN c → ∀ i : Fin (2 * k + 6),
      ∃ Y, Clifford.IsGCircleS Y ∧ EptInf (2 * k + 6) c ∈ Y ∧
        ∀ j : Fin (2 * k + 5), EptInf (2 * k + 4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y)
    (n : ℕ) (hn : 3 ≤ n) : CliffordChainS n :=
  Clifford.cliffordChainS_all_of EptInf h4_pt_inf (hodd_inf_all hPi) heven n hn

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.cliffordChainS_of_inf
#check @Clifford.MorleyKernel.cliffordChainS_of_inf

/-! ## J24 — the odd payload with no hypothesis: removing `hPi`

If `P₀ ≠ 0` and some child `i₀` has middle coordinate `P_{k+2} = 0`, then (by the conjugation
symmetry) also its `P₀ = 0`; the extension `V = (w, 0)` and the shift `S = (0, w)` of its cross vector
`w` are killed by every parent row except row `i₀`, so a nonzero combination lies in the parent
kernel with vanishing `P₀`-coordinate, which forces `w = 0` (`child_crossVec_zero_of_P3`). A Laplace
expansion along row `i₀` then gives `Q_{k+2}(parent) = 0` (`parent_detL_zero`), so the parent minus
its last column has a kernel vector shared by all children: every *finite* child level point is the
same point (`children_eq_of_P3_zero`), a fortiori collinear (`child_line_of_P3_zero`). -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section J24
variable {R : Type*} [CommRing R]

theorem kpe_odd_eq_mul_y (k : ℕ) (x y : R) (j : ℕ) (hj : j ≤ 2 * k + 4) :
    kpe (2 * k + 5) x y j = y * kpe (2 * k + 4) x y j := by
  have h5 : (2 * k + 5) / 2 = k + 2 := by omega
  have h4 : (2 * k + 4) / 2 = k + 2 := by omega
  simp only [kpe, h5, h4]
  split_ifs with h
  · rw [show 2 * k + 5 - (k + 2) - j = (2 * k + 4 - (k + 2) - j) + 1 by omega, pow_succ]; ring
  · rw [show 2 * k + 5 - (k + 2) - 1 - (j - (k + 2 + 1)) =
      (2 * k + 4 - (k + 2) - 1 - (j - (k + 2 + 1))) + 1 by omega, pow_succ]; ring

theorem kpe_odd_succ_eq_mul_x (k : ℕ) (x y : R) (j : ℕ) (hj : j ≤ 2 * k + 4) (hm : j ≠ k + 2) :
    kpe (2 * k + 5) x y (j + 1) = -x * kpe (2 * k + 4) x y j := by
  have h5 : (2 * k + 5) / 2 = k + 2 := by omega
  have h4 : (2 * k + 4) / 2 = k + 2 := by omega
  simp only [kpe, h5, h4]
  by_cases h : j ≤ k + 1
  · rw [if_pos (by omega), if_pos (by omega),
      show 2 * k + 5 - (k + 2) - (j + 1) = 2 * k + 4 - (k + 2) - j by omega, pow_succ]; ring
  · rw [if_neg (by omega), if_neg (by omega), show j + 1 - (k + 2 + 1) = (j - (k + 2 + 1)) + 1 by omega,
      show 2 * k + 5 - (k + 2) - 1 - (j - (k + 2 + 1) + 1) =
        2 * k + 4 - (k + 2) - 1 - (j - (k + 2 + 1)) by omega, pow_succ]; ring

/-- The shift `(0, W₀, W₁, …)` of a sequence. -/
def shN (W : ℕ → R) (j : ℕ) : R := if j = 0 then 0 else W (j - 1)

theorem gN_range (k : ℕ) (x y : R) (w : Fin (2 * k + 5) → R) :
    gN k x y w = ∑ j ∈ Finset.range (2 * k + 5), kpe (2 * k + 4) x y j * extN w j := by
  rw [gN, ← Fin.sum_univ_eq_sum_range (fun j => kpe (2 * k + 4) x y j * extN w j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [extN_fin]

/-- A parent row against the extension `(w, 0)` is `y ·` the child row against `w`. -/
theorem rowV_N (k : ℕ) (x y : R) (w : Fin (2 * k + 5) → R) :
    ∑ j : Fin (2 * k + 5 + 1), kpe (2 * k + 5) x y j * extN w j = y * gN k x y w := by
  have hS : ∑ j : Fin (2 * k + 5 + 1), kpe (2 * k + 5) x y j * extN w j =
      ∑ j ∈ Finset.range (2 * k + 5 + 1), kpe (2 * k + 5) x y j * extN w j :=
    Fin.sum_univ_eq_sum_range (fun j => kpe (2 * k + 5) x y j * extN w j) _
  rw [hS, Finset.sum_range_succ, gN_range, Finset.mul_sum]
  have h0 : extN w (2 * k + 5) = 0 := by simp [extN]
  rw [h0, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [kpe_odd_eq_mul_y k x y j (by simp at hj; omega)]; ring

/-- A parent row against the shift `(0, w)` is `-x ·` the child row against `w`, when `w_{k+2} = 0`. -/
theorem rowS_N (k : ℕ) (x y : R) (w : Fin (2 * k + 5) → R) (hw : w ⟨k + 2, by omega⟩ = 0) :
    ∑ j : Fin (2 * k + 5 + 1), kpe (2 * k + 5) x y j * shN (extN w) j = -x * gN k x y w := by
  have hS : ∑ j : Fin (2 * k + 5 + 1), kpe (2 * k + 5) x y j * shN (extN w) j =
      ∑ j ∈ Finset.range (2 * k + 5 + 1), kpe (2 * k + 5) x y j * shN (extN w) j :=
    Fin.sum_univ_eq_sum_range (fun j => kpe (2 * k + 5) x y j * shN (extN w) j) _
  rw [hS, Finset.sum_range_succ', gN_range, Finset.mul_sum]
  simp only [shN, if_true, mul_zero, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hm : j = k + 2
  · subst hm
    have : extN w (k + 2) = 0 := by rw [extN, dif_pos (by omega)]; exact hw
    rw [this]; ring
  · rw [kpe_odd_succ_eq_mul_x k x y j (by simp at hj; omega) hm]; ring

end J24

/-- With `P₀ ≠ 0`, a parent kernel vector with vanishing `P₀`-coordinate is zero. -/
theorem parent_ker_zero_of_P0 (k : ℕ) (d : Fin (2 * k + 5) → ℂ)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0)
    (X : Fin (2 * k + 5 + 1) → ℂ) (hX : KP (2 * k + 5) d (fun j => conj (d j)) *ᵥ X = 0)
    (hX0 : X 0 = 0) : X = 0 := by
  have hk := ker_eq_span_crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 hP0
  have hmem : X ∈ LinearMap.ker (KP (2 * k + 5) d (fun j => conj (d j))).mulVecLin := by simpa using hX
  rw [hk, Submodule.mem_span_singleton] at hmem
  obtain ⟨s, hs⟩ := hmem
  have e0 := congrFun hs 0
  simp only [Pi.smul_apply, smul_eq_mul] at e0
  rw [hX0] at e0
  have hs0 : s = 0 := (mul_eq_zero.1 e0).resolve_right hP0
  rw [← hs, hs0, zero_smul]

/-- **Key lemma.** With `P₀ ≠ 0`, a child whose middle coordinate `P_{k+2}` vanishes has
vanishing cross vector (the child matrix is rank-deficient). No general-position hypothesis. -/
theorem child_crossVec_zero_of_P3 (k : ℕ) (d : Fin (2 * k + 5) → ℂ)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0) (i : Fin (2 * k + 5))
    (hi : crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)))
      ⟨k + 2, by omega⟩ = 0) :
    crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r))) = 0 := by
  set w := crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r))) with hw
  set A := KP (2 * k + 5) d (fun j => conj (d j)) with hA
  have hw0 : w 0 = 0 := by
    have h := conj_crossVec_even (k + 1) (d ∘ i.succAbove)
    have h' : conj (w ⟨k + 2, by omega⟩) = w 0 := h
    rw [hi, map_zero] at h'
    exact h'.symm
  set V : Fin (2 * k + 5 + 1) → ℂ := fun j => extN w j with hV
  set S : Fin (2 * k + 5 + 1) → ℂ := fun j => shN (extN w) j with hS
  have hrowV : ∀ r, (A *ᵥ V) (i.succAbove r) = 0 := by
    intro r
    have e := rowV_N k (d (i.succAbove r)) (conj (d (i.succAbove r))) w
    have g := gN_crossVec k (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)) r
    change ∑ j : Fin (2 * k + 5 + 1), kpe (2 * k + 5) (d (i.succAbove r)) (conj (d (i.succAbove r))) j *
      extN w j = 0
    rw [e]
    change conj (d (i.succAbove r)) * gN k (d (i.succAbove r)) (conj (d (i.succAbove r))) w = 0
    have g' : gN k (d (i.succAbove r)) (conj (d (i.succAbove r))) w = 0 := g
    rw [g', mul_zero]
  have hrowS : ∀ r, (A *ᵥ S) (i.succAbove r) = 0 := by
    intro r
    have e := rowS_N k (d (i.succAbove r)) (conj (d (i.succAbove r))) w hi
    have g := gN_crossVec k (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)) r
    change ∑ j : Fin (2 * k + 5 + 1), kpe (2 * k + 5) (d (i.succAbove r)) (conj (d (i.succAbove r))) j *
      shN (extN w) j = 0
    rw [e]
    have g' : gN k (d (i.succAbove r)) (conj (d (i.succAbove r))) w = 0 := g
    rw [g', mul_zero]
  have hext : ∀ j : Fin (2 * k + 5), w j = extN w j := fun j => (extN_fin w j).symm
  have hV0 : V 0 = 0 := by
    change extN w 0 = 0
    rw [extN, dif_pos (by omega)]; exact hw0
  by_cases hβ : (A *ᵥ V) i = 0
  · have hAV : A *ᵥ V = 0 := by
      funext ρ
      rcases Fin.eq_self_or_eq_succAbove i ρ with rfl | ⟨r, rfl⟩
      · exact hβ
      · exact hrowV r
    have hVz := parent_ker_zero_of_P0 k d hP0 V hAV hV0
    funext j
    have := congrFun hVz ⟨j, by omega⟩
    rw [hext j]
    exact this
  · set α := (A *ᵥ S) i with hα
    set β := (A *ᵥ V) i with hβd
    have hAX : A *ᵥ (α • V - β • S) = 0 := by
      funext ρ
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
      rcases Fin.eq_self_or_eq_succAbove i ρ with rfl | ⟨r, rfl⟩
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; rw [← hα, ← hβd]; ring
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hrowV r, hrowS r]; ring
    have hX0 : (α • V - β • S) 0 = 0 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hV0]
      change α * 0 - β * shN (extN w) 0 = 0
      simp [shN]
    have hXz := parent_ker_zero_of_P0 k d hP0 _ hAX hX0
    have hdown : ∀ t, t ≤ 2 * k + 5 → extN w (2 * k + 5 - t) = 0 := by
      intro t
      induction t with
      | zero => intro _; simp [extN]
      | succ t ih =>
        intro ht
        have h1 := ih (by omega)
        have hc := congrFun hXz ⟨2 * k + 5 - t, by omega⟩
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
        change α * extN w (2 * k + 5 - t) - β * shN (extN w) (2 * k + 5 - t) = 0 at hc
        rw [h1, shN, if_neg (by omega), show 2 * k + 5 - t - 1 = 2 * k + 5 - (t + 1) by omega] at hc
        have : β * extN w (2 * k + 5 - (t + 1)) = 0 := by linear_combination -hc
        exact (mul_eq_zero.1 this).resolve_left hβ
    funext j
    rw [hext j, show (j : ℕ) = 2 * k + 5 - (2 * k + 5 - j) by omega]
    exact hdown _ (by omega)

/-- **Laplace step.** A child with vanishing cross vector forces `Q_{k+2}(parent) = 0`: the parent
without its last column is singular. -/
theorem parent_detL_zero (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (i : Fin (2 * k + 5))
    (hw : crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r))) = 0) :
    ((KP (2 * k + 5) d (fun j => conj (d j))).submatrix id (Fin.last (2 * k + 5)).succAbove).det = 0 := by
  rw [Matrix.det_succ_row _ i]
  refine Finset.sum_eq_zero fun j _ => ?_
  have e : ((KP (2 * k + 5) d (fun j => conj (d j))).submatrix id
      (Fin.last (2 * k + 5)).succAbove).submatrix i.succAbove j.succAbove =
      (subScaled (k + 1) d (fun j => conj (d j)) i).submatrix id j.succAbove := by
    rw [← KP_sub_eq_odd]; rfl
  have hc := crossVec_subScaled (k + 1) d (fun j => conj (d j)) i j
  have hw' : crossVec (KP (2 * (k + 1) + 2) (d ∘ i.succAbove) ((fun j => conj (d j)) ∘ i.succAbove)) = 0 :=
    hw
  have hz : crossVec (subScaled (k + 1) d (fun j => conj (d j)) i) j = 0 := by
    rw [hc]
    have hz' := congrFun hw' j
    simp only [Pi.zero_apply] at hz'
    erw [hz', mul_zero]
  unfold crossVec at hz
  have hdet := (mul_eq_zero.1 hz).resolve_left (pow_ne_zero _ (by norm_num))
  rw [e, hdet, mul_zero]

/-- **All finite children coincide** when `P₀ ≠ 0` and some child has `P_{k+2} = 0`. -/
theorem children_eq_of_P3_zero (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (h : GenPosN d)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0)
    (hsome : ∃ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
               (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ = 0) :
    ∃ p : ℂ, ∀ i : Fin (2 * k + 5),
      (crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)))
          ⟨k + 2, by omega⟩ ≠ 0 →
        levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
          (fun r => conj ((d ∘ i.succAbove) r)))) = p) := by
  obtain ⟨i0, hi0⟩ := hsome
  have hd : ∀ j, d j ≠ 0 := hc_of_genPos (by omega) d h
  have hdet := parent_detL_zero k d i0 (child_crossVec_zero_of_P3 k d hP0 i0 hi0)
  obtain ⟨V, hV0, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  exact ⟨-V (Fin.last _) / V ⟨k + 2, by omega⟩, fun i hi =>
    levelPointN_of_ker k _ hi V (child_mulVec_of_parentN k d hd V hV i) hV0⟩

/-- **Target 1.** A vanishing child `P_{k+2}` (with `P₀ ≠ 0`) puts the finite children on one line
`p + ℝ·u` (explicit witnesses: `p` the common point, `u = 1`). -/
theorem child_line_of_P3_zero (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (h : GenPosN d)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0)
    (hsome : ∃ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
               (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ = 0) :
    ∃ p u : ℂ, u ≠ 0 ∧ ∀ i : Fin (2 * k + 5),
      (crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)))
          ⟨k + 2, by omega⟩ ≠ 0 →
        ∃ t : ℝ, levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
          (fun r => conj ((d ∘ i.succAbove) r)))) = p + (t : ℂ) * u) := by
  obtain ⟨p, hp⟩ := children_eq_of_P3_zero k d h hP0 hsome
  exact ⟨p, 1, one_ne_zero, fun i hi => ⟨0, by rw [hp i hi]; simp⟩⟩

/-- The third branch: `P₀ ≠ 0`, some child at `∞`; a line through the finite children and `∞`. -/
theorem hodd_inf_P0_ne_some (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (h : GenPosN d)
    (hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 ≠ 0)
    (hsome : ∃ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
               (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ = 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * k + 5), EptInf (2 * k + 4) (d ∘ i.succAbove) ∈ Y := by
  obtain ⟨p, u, hu, ht⟩ := child_line_of_P3_zero k d h hP0 hsome
  refine ⟨Clifford.lineS p u, Or.inr ⟨p, u, hu, rfl⟩, fun i => ?_⟩
  by_cases hi : crossVec (KP (2 * k + 4) (d ∘ i.succAbove) (fun r => conj ((d ∘ i.succAbove) r)))
      ⟨k + 2, by omega⟩ = 0
  · rw [EptInf_child_eq_infty k d i hi]
    exact Set.mem_insert _ _
  · rw [EptInf_child_eq_coe k d i hi]
    obtain ⟨t, htt⟩ := ht i hi
    exact Set.mem_insert_of_mem _ ⟨_, ⟨t, by rw [Complex.real_smul]; exact htt⟩, rfl⟩

/-- **Target 2.** The odd payload for `E := EptInf`, with **no hypothesis** beyond general position. -/
theorem hodd_inf' (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (h : GenPosN d) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      ∀ i : Fin (2 * k + 5), EptInf (2 * k + 4) (d ∘ i.succAbove) ∈ Y := by
  by_cases hP0 : crossVec (KP (2 * k + 5) d (fun j => conj (d j))) 0 = 0
  · exact hodd_inf_P0_eq k d h hP0
  · by_cases hall : ∀ i : Fin (2 * k + 5), crossVec (KP (2 * k + 4) (d ∘ i.succAbove)
        (fun r => conj ((d ∘ i.succAbove) r))) ⟨k + 2, by omega⟩ ≠ 0
    · exact hodd_inf_P0_ne k d h hP0 hall
    · push Not at hall
      exact hodd_inf_P0_ne_some k d h hP0 hall

/-- **Target 3a.** `hodd` in the exact form consumed by `cliffordChainS_all_of` (`E := EptInf`). -/
theorem hodd_inf_all' :
    ∀ (k : ℕ) (d : Fin (2 * k + 5) → ℂ), GenPosN d →
      ∃ Y, Clifford.IsGCircleS Y ∧ ∀ i : Fin (2 * k + 5), EptInf (2 * k + 4) (d ∘ i.succAbove) ∈ Y :=
  fun k d h => hodd_inf' k d h

/-- **Target 3b.** The whole odd side discharged: the Clifford chain on the sphere for all `n ≥ 3`
from the even payload alone. -/
theorem cliffordChainS_of_inf'
    (heven : ∀ (k : ℕ) (c : Fin (2 * k + 6) → ℂ), GenPosN c → ∀ i : Fin (2 * k + 6),
      ∃ Y, Clifford.IsGCircleS Y ∧ EptInf (2 * k + 6) c ∈ Y ∧
        ∀ j : Fin (2 * k + 5), EptInf (2 * k + 4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y)
    (n : ℕ) (hn : 3 ≤ n) : CliffordChainS n :=
  Clifford.cliffordChainS_all_of EptInf h4_pt_inf hodd_inf_all' heven n hn

end Clifford.MorleyKernel

#print axioms Clifford.MorleyKernel.kpe_odd_eq_mul_y
#print axioms Clifford.MorleyKernel.kpe_odd_succ_eq_mul_x
#print axioms Clifford.MorleyKernel.gN_range
#print axioms Clifford.MorleyKernel.rowV_N
#print axioms Clifford.MorleyKernel.rowS_N
#print axioms Clifford.MorleyKernel.parent_ker_zero_of_P0
#print axioms Clifford.MorleyKernel.child_crossVec_zero_of_P3
#print axioms Clifford.MorleyKernel.parent_detL_zero
#print axioms Clifford.MorleyKernel.children_eq_of_P3_zero
#print axioms Clifford.MorleyKernel.child_line_of_P3_zero
#print axioms Clifford.MorleyKernel.hodd_inf_P0_ne_some
#print axioms Clifford.MorleyKernel.hodd_inf'
#print axioms Clifford.MorleyKernel.hodd_inf_all'
#print axioms Clifford.MorleyKernel.cliffordChainS_of_inf'
#check @Clifford.MorleyKernel.child_crossVec_zero_of_P3
#check @Clifford.MorleyKernel.parent_detL_zero
#check @Clifford.MorleyKernel.children_eq_of_P3_zero
#check @Clifford.MorleyKernel.child_line_of_P3_zero
#check @Clifford.MorleyKernel.hodd_inf_P0_ne_some
#check @Clifford.MorleyKernel.hodd_inf'
#check @Clifford.MorleyKernel.hodd_inf_all'
#check @Clifford.MorleyKernel.cliffordChainS_of_inf'

#check @Clifford.MorleyKernel.stepEven_gen
#check @Clifford.MorleyKernel.stepOdd_gen
#check @Clifford.MorleyKernel.kernelCircle_isGCircleS
#check @Clifford.MorleyKernel.hodd_levelPoint
#check @Clifford.MorleyKernel.EptInf_child_eq_coe
#check @Clifford.MorleyKernel.EptInf_eq_coe
#check @Clifford.GenPosN.comp_succAbove

/-! ## J26: `heven_kernel` — the even step, kernel branch (rewiring only) -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section J26

theorem heven_kernel (k : ℕ) (c : Fin (2*k+6) → ℂ) (h : GenPosN c) (i : Fin (2*k+6))
    (hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ ≠ 0)
    (hP0  : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 ≠ 0)
    (hPi  : ∀ j : Fin (2*k+5), crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
              (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      EptInf (2*k+6) c ∈ Y ∧
      ∀ j : Fin (2*k+5), EptInf (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y := by
  set d : Fin (2*k+5) → ℂ := c ∘ i.succAbove with hd_def
  have hdg : GenPosN d := h.comp_succAbove i
  have hdc : ∀ j, d j ≠ 0 := hc_of_genPos (by omega) d hdg
  have hcc : ∀ j, c j ≠ 0 := hc_of_genPos (by omega) c h
  refine ⟨OnePoint.some ''
      {z : ℂ | oddCircleEq (k+2) (crossVec (KP (2*k+5) d (fun r => conj (d r)))) z = 0},
    kernelCircle_isGCircleS (k+2) _ hP0, ?_, ?_⟩
  · have hmid' : crossVec (KP (2*k+6) c (fun j => conj (c j)))
        ⟨(2*k+6)/2, by omega⟩ ≠ 0 := by
      have he : (⟨(2*k+6)/2, by omega⟩ : Fin (2*k+6+1)) = ⟨k+3, by omega⟩ := Fin.ext (by show (2*k+6)/2 = k+3; omega)
      rw [he]; exact hmid
    have hE : EptInf (2*k+6) c = Ept (2*k+6) c := EptInf_eq_coe (2*k+6) c hmid'
    rw [hE]
    refine ⟨levelPointN (2*k+6) (crossVec (KP (2*k+6) c (fun j => conj (c j)))), ?_, rfl⟩
    exact stepEven_gen (k+2) (by omega) c hcc hmid i
  · intro j
    rw [EptInf_child_eq_coe k d j (hPi j)]
    exact ⟨_, stepOdd_gen (k+1) d hdc j (hPi j), rfl⟩

end J26
end Clifford.MorleyKernel

#check @Clifford.MorleyKernel.heven_kernel
#print axioms Clifford.MorleyKernel.heven_kernel

/-! ## J28: branch (b) — the parent level point on the children's line -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

section J28
variable {R : Type*} [CommRing R]

theorem kpe5_lo (k : ℕ) (x y : R) (j : ℕ) (hj : j ≤ k + 2) :
    kpe (2 * k + 5) x y j = (-x) ^ j * y ^ (k + 3 - j) := by
  unfold kpe
  rw [if_pos (show j ≤ (2 * k + 5) / 2 by omega), show 2 * k + 5 - (2 * k + 5) / 2 - j = k + 3 - j by omega]

theorem kpe6_lo (k : ℕ) (x y : R) (j : ℕ) (hj : j ≤ k + 3) :
    kpe (2 * k + 6) x y j = (-x) ^ j * y ^ (k + 3 - j) := by
  unfold kpe
  rw [if_pos (show j ≤ (2 * k + 6) / 2 by omega), show 2 * k + 6 - (2 * k + 6) / 2 - j = k + 3 - j by omega]

theorem kpe5_hi (k : ℕ) (x y : R) (j : ℕ) (hj : k + 3 ≤ j) (hj' : j ≤ 2 * k + 5) :
    kpe (2 * k + 5) x y j = -((-x) ^ (j - (k + 3)) * y ^ (2 * k + 5 - j)) := by
  unfold kpe
  rw [if_neg (show ¬ j ≤ (2 * k + 5) / 2 by omega),
    show j - ((2 * k + 5) / 2 + 1) = j - (k + 3) by omega,
    show 2 * k + 5 - (2 * k + 5) / 2 - 1 - (j - (k + 3)) = 2 * k + 5 - j by omega]

theorem kpe6_hi (k : ℕ) (x y : R) (j : ℕ) (hj : k + 4 ≤ j) (hj' : j ≤ 2 * k + 6) :
    kpe (2 * k + 6) x y j = -((-x) ^ (j - (k + 4)) * y ^ (2 * k + 6 - j)) := by
  unfold kpe
  rw [if_neg (show ¬ j ≤ (2 * k + 6) / 2 by omega),
    show j - ((2 * k + 6) / 2 + 1) = j - (k + 4) by omega,
    show 2 * k + 6 - (2 * k + 6) / 2 - 1 - (j - (k + 4)) = 2 * k + 6 - j by omega]

end J28

/-- **The parent level point kills the subfamily's `MN` matrix.** The rows of the subfamily are
rows of the parent `KP (2k+6)`; the parent cross vector, with its column `Q₀ = k+3` moved to the
end (sign flipped), is a nonzero kernel vector once `z̄ V₀ = V_{k+4}` and `z V_{k+3} = −V_last`. -/
theorem parent_det_MN (k : ℕ) (c : Fin (2*k+6) → ℂ) (i : Fin (2*k+6))
    (hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ ≠ 0) :
    let z := levelPointN (2*k+6) (crossVec (KP (2*k+6) c (fun j => conj (c j))))
    (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
      (fun r => conj ((c ∘ i.succAbove) r) ^ (k + 3) - conj z * conj ((c ∘ i.succAbove) r) ^ (k + 2))
      (fun r => z * -(-(c ∘ i.succAbove) r) ^ (k + 2) - (-(c ∘ i.succAbove) r) ^ (k + 3))).det = 0 := by
  intro z
  set V := crossVec (KP (2*k+6) c (fun j => conj (c j))) with hV
  have hV0 : V 0 ≠ 0 := crossVec_even_P0_ne_zero (k + 2) c hmid
  set W := extN V with hW
  have hz : z * W (k + 3) + W (2 * k + 6) = 0 := by
    have e1 : (⟨(2 * k + 6) / 2, by omega⟩ : Fin (2 * k + 6 + 1)) = ⟨k + 3, by omega⟩ := by
      ext; simp only; omega
    have e2 : (Fin.last (2 * k + 6)) = (⟨2 * k + 6, by omega⟩ : Fin (2 * k + 6 + 1)) := rfl
    have w3 : W (k + 3) = V ⟨k + 3, by omega⟩ := extN_fin V ⟨k + 3, by omega⟩
    have w6 : W (2 * k + 6) = V ⟨2 * k + 6, by omega⟩ := extN_fin V ⟨2 * k + 6, by omega⟩
    rw [w3, w6]
    show -V (Fin.last (2 * k + 6)) / V ⟨(2 * k + 6) / 2, by omega⟩ * V ⟨k + 3, by omega⟩ +
      V ⟨2 * k + 6, by omega⟩ = 0
    rw [e1, div_mul_cancel₀ _ hmid, e2]; ring
  have hZ : conj z * W 0 - W (k + 4) = 0 := by
    have h := conj_levelPointN_even (k + 2) c
    have h' : conj z = V ⟨k + 4, by omega⟩ / V 0 := h
    have w0 : W 0 = V 0 := extN_fin V (0 : Fin (2 * k + 6 + 1))
    have w4 : W (k + 4) = V ⟨k + 4, by omega⟩ := extN_fin V ⟨k + 4, by omega⟩
    rw [w0, w4, h', div_mul_cancel₀ _ hV0, sub_self]
  set U : ℕ → ℂ := fun j => if j = 2 * k + 4 then -W (k + 3) else if j ≤ k + 2 then W j else W (j + 2)
    with hU
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨fun j => U j, ?_, ?_⟩
  · intro h0
    have := congrFun h0 0
    have w0 : W 0 = V 0 := extN_fin V (0 : Fin (2 * k + 6 + 1))
    simp only [hU, Fin.val_zero, if_neg (show (0 : ℕ) ≠ 2 * k + 4 by omega),
      if_pos (show (0 : ℕ) ≤ k + 2 by omega), Pi.zero_apply, w0] at this
    exact hV0 this
  · funext r
    set x := c (i.succAbove r) with hx
    set y := conj x with hy
    set A := y ^ (k + 3) - conj z * y ^ (k + 2) with hA
    set B := z * -(-x) ^ (k + 2) - (-x) ^ (k + 3) with hB
    set F : ℕ → ℂ := fun j => colN k x y A B j * U j with hF
    set G : ℕ → ℂ := fun j => kpe (2 * k + 6) x y j * W j with hG
    have hS : (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
        (fun r => conj ((c ∘ i.succAbove) r) ^ (k + 3) - conj z * conj ((c ∘ i.succAbove) r) ^ (k + 2))
        (fun r => z * -(-(c ∘ i.succAbove) r) ^ (k + 2) - (-(c ∘ i.succAbove) r) ^ (k + 3)) *ᵥ
          fun j => U j) r = ∑ j ∈ Finset.range (2 * k + 5), F j := by
      rw [← Fin.sum_univ_eq_sum_range F]; rfl
    have hR : ∑ j ∈ Finset.range (2 * k + 6 + 1), G j = 0 := by
      have h := congrFun (mulVec_crossVec (KP (2*k+6) c (fun j => conj (c j)))) (i.succAbove r)
      rw [← Fin.sum_univ_eq_sum_range G]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
      simp only [hG]; rw [hW, extN_fin]; rfl
    rw [hS, Pi.zero_apply]
    have e1 : 2 * k + 5 = (k + 3) + (k + 2) := by omega
    have e2 : 2 * k + 6 + 1 = (k + 3) + (k + 4) := by omega
    have B1 := Finset.sum_range_succ' F (k + 2)
    have B2 := Finset.sum_range_succ (fun t => F (k + 3 + t)) (k + 1)
    have C1 := Finset.sum_range_succ' G (k + 2)
    have C2 := Finset.sum_range_succ' (fun t => G (k + 3 + t)) (k + 3)
    have C3 := Finset.sum_range_succ' (fun t => G (k + 3 + (t + 1))) (k + 2)
    have C4 := Finset.sum_range_succ (fun t => G (k + 3 + (t + 1 + 1))) (k + 1)
    beta_reduce at B2 C2 C3 C4
    rw [e2, Finset.sum_range_add, C1, C2, C3, C4] at hR
    rw [e1, Finset.sum_range_add, B1, B2]
    have T1 : ∑ t ∈ Finset.range (k + 2), F (t + 1) = ∑ t ∈ Finset.range (k + 2), G (t + 1) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht := Finset.mem_range.1 ht
      simp only [hF, hG, colN, hU, if_neg (show t + 1 ≠ 0 by omega),
        if_neg (show t + 1 ≠ 2 * k + 4 by omega), if_pos (show t + 1 ≤ k + 2 by omega)]
      rw [kpe5_lo k x y _ (by omega), kpe6_lo k x y _ (by omega)]
    have T2 : ∑ t ∈ Finset.range (k + 1), F (k + 3 + t) =
        ∑ t ∈ Finset.range (k + 1), G (k + 3 + (t + 1 + 1)) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht := Finset.mem_range.1 ht
      simp only [hF, hG, colN, hU, if_neg (show k + 3 + t ≠ 0 by omega),
        if_neg (show k + 3 + t ≠ 2 * k + 4 by omega), if_neg (show ¬ (k + 3 + t ≤ k + 2) by omega)]
      rw [kpe5_hi k x y _ (by omega) (by omega), kpe6_hi k x y _ (by omega) (by omega),
        show k + 3 + t + 1 - (k + 3) = k + 3 + (t + 1 + 1) - (k + 4) by omega,
        show 2 * k + 5 - (k + 3 + t + 1) = 2 * k + 6 - (k + 3 + (t + 1 + 1)) by omega,
        show k + 3 + t + 2 = k + 3 + (t + 1 + 1) by omega]
    have hF0 : F 0 = A * W 0 := by
      simp only [hF, colN, hU, if_neg (show (0 : ℕ) ≠ 2 * k + 4 by omega),
        if_pos (show (0 : ℕ) ≤ k + 2 by omega), if_true]
    have hFL : F (k + 3 + (k + 1)) = B * -W (k + 3) := by
      rw [show k + 3 + (k + 1) = 2 * k + 4 by omega]
      simp only [hF, colN, hU, if_neg (show 2 * k + 4 ≠ 0 by omega), if_true]
    have hG0 : G 0 = y ^ (k + 3) * W 0 := by
      simp only [hG]; rw [kpe6_lo k x y _ (by omega)]; simp
    have hG3 : G (k + 3 + 0) = (-x) ^ (k + 3) * W (k + 3) := by
      simp only [hG, add_zero]; rw [kpe6_lo k x y _ (by omega)]; simp
    have hG4 : G (k + 3 + (0 + 1)) = -(y ^ (k + 2)) * W (k + 4) := by
      simp only [hG, zero_add]
      rw [kpe6_hi k x y _ (by omega) (by omega), show k + 3 + 1 - (k + 4) = 0 by omega,
        show 2 * k + 6 - (k + 3 + 1) = k + 2 by omega, show k + 3 + 1 = k + 4 by omega]
      ring
    have hGL : G (k + 3 + (k + 1 + 1 + 1)) = -((-x) ^ (k + 2)) * W (2 * k + 6) := by
      simp only [hG]
      rw [kpe6_hi k x y _ (by omega) (by omega), show k + 3 + (k + 1 + 1 + 1) - (k + 4) = k + 2 by omega,
        show 2 * k + 6 - (k + 3 + (k + 1 + 1 + 1)) = 0 by omega,
        show k + 3 + (k + 1 + 1 + 1) = 2 * k + 6 by omega]
      ring
    rw [T1, T2, hF0, hFL]
    rw [hG0, hG3, hG4, hGL] at hR
    rw [hA, hB]
    linear_combination hR - y ^ (k + 2) * hZ + (-x) ^ (k + 2) * hz

theorem parent_on_child_line (k : ℕ) (c : Fin (2*k+6) → ℂ) (h : GenPosN c) (i : Fin (2*k+6))
    (hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ ≠ 0)
    (hP0  : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 = 0)
    (hQ0  : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r)))
              ⟨k+3, by omega⟩ ≠ 0) :
    let z := levelPointN (2*k+6) (crossVec (KP (2*k+6) c (fun j => conj (c j))))
    (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
        (fun r => conj ((c ∘ i.succAbove) r) ^ (k + 3)) (fun r => -(-(c ∘ i.succAbove) r) ^ (k + 3))).det +
      (-1) ^ (k + 3) * crossVec (KP (2*k+5) (c ∘ i.succAbove)
        (fun r => conj ((c ∘ i.succAbove) r))) ⟨k+3, by omega⟩ * z +
      (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
        (fun r => -conj ((c ∘ i.succAbove) r) ^ (k + 2))
        (fun r => -(-(c ∘ i.succAbove) r) ^ (k + 3))).det * conj z = 0 := by
  intro z
  have hd := parent_det_MN k c i hmid
  simp only at hd
  rw [det_MN_expand, det_MN_D, det_MN_F, hP0] at hd
  linear_combination hd

end Clifford.MorleyKernel

#check @Clifford.MorleyKernel.parent_on_child_line
#print axioms Clifford.MorleyKernel.parent_on_child_line

/-! ## J29: branch (a) — `hmid = 0` with `P₀(w) ≠ 0` forces the parent cross vector to vanish -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- With `v_{k+3} = 0` (hence `v₀ = 0`), the parent cross vector, with columns `0, k+3` dropped and
`v_{k+4}` moved to the front, is a kernel vector of the subfamily's `MN` at the `F`-columns. -/
theorem parent_mid_ker_MNF (k : ℕ) (c : Fin (2*k+6) → ℂ) (i : Fin (2*k+6))
    (hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ = 0) :
    MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
      (fun r => -conj ((c ∘ i.succAbove) r) ^ (k + 2))
      (fun r => -(-(c ∘ i.succAbove) r) ^ (k + 2)) *ᵥ
        (fun j : Fin (2*k+5) =>
          (fun j : ℕ => if j = 0 then extN (crossVec (KP (2*k+6) c (fun j => conj (c j)))) (k + 4)
            else if j ≤ k + 2 then extN (crossVec (KP (2*k+6) c (fun j => conj (c j)))) j
            else extN (crossVec (KP (2*k+6) c (fun j => conj (c j)))) (j + 2)) j) = 0 := by
  set V := crossVec (KP (2*k+6) c (fun j => conj (c j))) with hV
  set W := extN V with hW
  have hW3 : W (k + 3) = 0 := by
    rw [hW, extN_fin V ⟨k + 3, by omega⟩]; exact hmid
  have hW0 : W 0 = 0 := by
    have e := extN_fin V (0 : Fin (2 * k + 6 + 1))
    simp only [Fin.val_zero] at e
    rw [hW, e]
    have h : conj (V ⟨k + 3, by omega⟩) = V 0 := conj_crossVec_even (k + 2) c
    rw [← h]; exact (map_eq_zero _).2 hmid
  set U : ℕ → ℂ := fun j => if j = 0 then W (k + 4) else if j ≤ k + 2 then W j else W (j + 2)
    with hU
  funext r
  set x := c (i.succAbove r) with hx
  set y := conj x with hy
  set A := -y ^ (k + 2) with hA
  set B := -(-x) ^ (k + 2) with hB
  set F : ℕ → ℂ := fun j => colN k x y A B j * U j with hF
  set G : ℕ → ℂ := fun j => kpe (2 * k + 6) x y j * W j with hG
  have hS : (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
      (fun r => -conj ((c ∘ i.succAbove) r) ^ (k + 2))
      (fun r => -(-(c ∘ i.succAbove) r) ^ (k + 2)) *ᵥ
        fun j => U j) r = ∑ j ∈ Finset.range (2 * k + 5), F j := by
    rw [← Fin.sum_univ_eq_sum_range F]; rfl
  have hR : ∑ j ∈ Finset.range (2 * k + 6 + 1), G j = 0 := by
    have h := congrFun (mulVec_crossVec (KP (2*k+6) c (fun j => conj (c j)))) (i.succAbove r)
    rw [← Fin.sum_univ_eq_sum_range G]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
    simp only [hG]; rw [hW, extN_fin]; rfl
  rw [hS, Pi.zero_apply]
  have e1 : 2 * k + 5 = (k + 3) + (k + 2) := by omega
  have e2 : 2 * k + 6 + 1 = (k + 3) + (k + 4) := by omega
  have B1 := Finset.sum_range_succ' F (k + 2)
  have B2 := Finset.sum_range_succ (fun t => F (k + 3 + t)) (k + 1)
  have C1 := Finset.sum_range_succ' G (k + 2)
  have C2 := Finset.sum_range_succ' (fun t => G (k + 3 + t)) (k + 3)
  have C3 := Finset.sum_range_succ' (fun t => G (k + 3 + (t + 1))) (k + 2)
  have C4 := Finset.sum_range_succ (fun t => G (k + 3 + (t + 1 + 1))) (k + 1)
  beta_reduce at B2 C2 C3 C4
  rw [e2, Finset.sum_range_add, C1, C2, C3, C4] at hR
  rw [e1, Finset.sum_range_add, B1, B2]
  have T1 : ∑ t ∈ Finset.range (k + 2), F (t + 1) = ∑ t ∈ Finset.range (k + 2), G (t + 1) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht := Finset.mem_range.1 ht
    simp only [hF, hG, colN, hU, if_neg (show t + 1 ≠ 0 by omega),
      if_neg (show t + 1 ≠ 2 * k + 4 by omega), if_pos (show t + 1 ≤ k + 2 by omega)]
    rw [kpe5_lo k x y _ (by omega), kpe6_lo k x y _ (by omega)]
  have T2 : ∑ t ∈ Finset.range (k + 1), F (k + 3 + t) =
      ∑ t ∈ Finset.range (k + 1), G (k + 3 + (t + 1 + 1)) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht := Finset.mem_range.1 ht
    simp only [hF, hG, colN, hU, if_neg (show k + 3 + t ≠ 0 by omega),
      if_neg (show k + 3 + t ≠ 2 * k + 4 by omega), if_neg (show ¬ (k + 3 + t ≤ k + 2) by omega)]
    rw [kpe5_hi k x y _ (by omega) (by omega), kpe6_hi k x y _ (by omega) (by omega),
      show k + 3 + t + 1 - (k + 3) = k + 3 + (t + 1 + 1) - (k + 4) by omega,
      show 2 * k + 5 - (k + 3 + t + 1) = 2 * k + 6 - (k + 3 + (t + 1 + 1)) by omega,
      show k + 3 + t + 2 = k + 3 + (t + 1 + 1) by omega]
  have hF0 : F 0 = A * W (k + 4) := by
    simp only [hF, colN, hU, if_true]
  have hFL : F (k + 3 + (k + 1)) = B * W (2 * k + 6) := by
    rw [show k + 3 + (k + 1) = 2 * k + 4 by omega]
    simp only [hF, colN, hU, if_neg (show 2 * k + 4 ≠ 0 by omega), if_true,
      if_neg (show ¬ (2 * k + 4 ≤ k + 2) by omega)]
  have hG0 : G 0 = y ^ (k + 3) * W 0 := by
    simp only [hG]; rw [kpe6_lo k x y _ (by omega)]; simp
  have hG3 : G (k + 3 + 0) = (-x) ^ (k + 3) * W (k + 3) := by
    simp only [hG, add_zero]; rw [kpe6_lo k x y _ (by omega)]; simp
  have hG4 : G (k + 3 + (0 + 1)) = -(y ^ (k + 2)) * W (k + 4) := by
    simp only [hG, zero_add]
    rw [kpe6_hi k x y _ (by omega) (by omega), show k + 3 + 1 - (k + 4) = 0 by omega,
      show 2 * k + 6 - (k + 3 + 1) = k + 2 by omega, show k + 3 + 1 = k + 4 by omega]
    ring
  have hGL : G (k + 3 + (k + 1 + 1 + 1)) = -((-x) ^ (k + 2)) * W (2 * k + 6) := by
    simp only [hG]
    rw [kpe6_hi k x y _ (by omega) (by omega), show k + 3 + (k + 1 + 1 + 1) - (k + 4) = k + 2 by omega,
      show 2 * k + 6 - (k + 3 + (k + 1 + 1 + 1)) = 0 by omega,
      show k + 3 + (k + 1 + 1 + 1) = 2 * k + 6 by omega]
    ring
  rw [T1, T2, hF0, hFL]
  rw [hG0, hG3, hG4, hGL] at hR
  rw [hA, hB]
  linear_combination hR - y ^ (k + 3) * hW0 - (-x) ^ (k + 3) * hW3

/-- **Branch (a) is the degenerate parent.** `v_{k+3} = 0` together with `P₀(w) ≠ 0` for the
subfamily `w` forces the whole parent cross vector to vanish. -/
theorem parent_crossVec_zero_of_mid (k : ℕ) (c : Fin (2*k+6) → ℂ) (i : Fin (2*k+6))
    (hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ = 0)
    (hP0  : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 ≠ 0) :
    crossVec (KP (2*k+6) c (fun j => conj (c j))) = 0 := by
  set V := crossVec (KP (2*k+6) c (fun j => conj (c j))) with hV
  have hdet : (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
      (fun r => -conj ((c ∘ i.succAbove) r) ^ (k + 2))
      (fun r => -(-(c ∘ i.succAbove) r) ^ (k + 2))).det ≠ 0 := by
    rw [det_MN_F]
    refine mul_ne_zero ?_ hP0
    rcases Int.units_eq_one_or (Equiv.Perm.sign (sigN k)) with h | h <;> simp [h]
  have hU := parent_mid_ker_MNF k c i hmid
  have hU0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hU
  have hW0 : V 0 = 0 := by
    have h : conj (V ⟨k + 3, by omega⟩) = V 0 := conj_crossVec_even (k + 2) c
    rw [← h]; exact (map_eq_zero _).2 hmid
  funext j
  rw [Pi.zero_apply]
  have hj := j.isLt
  by_cases j0 : (j : ℕ) = 0
  · rw [show j = 0 from Fin.ext j0]; exact hW0
  by_cases j3 : (j : ℕ) = k + 3
  · rw [show j = ⟨k + 3, by omega⟩ from Fin.ext j3]; exact hmid
  by_cases jlo : (j : ℕ) ≤ k + 2
  · have h := congrFun hU0 ⟨j, by omega⟩
    simp only [Pi.zero_apply, if_neg j0, if_pos jlo] at h
    rwa [← hV, extN_fin V j] at h
  by_cases j4 : (j : ℕ) = k + 4
  · have h := congrFun hU0 0
    simp only [Pi.zero_apply, Fin.val_zero, if_true] at h
    rwa [← hV, show k + 4 = ((j : ℕ)) from j4.symm, extN_fin V j] at h
  · have h := congrFun hU0 ⟨j - 2, by omega⟩
    simp only [Pi.zero_apply, if_neg (show (j : ℕ) - 2 ≠ 0 by omega),
      if_neg (show ¬ ((j : ℕ) - 2 ≤ k + 2) by omega)] at h
    rwa [← hV, show (j : ℕ) - 2 + 2 = j by omega, extN_fin V j] at h

/-- **Branch (a), target shape plus the rank hypothesis `hv`** (the parent cross vector is nonzero,
as in `heven_mid_line` at `n = 6`). Under `hv` the branch is empty: `hmid` and `hP0` force `v = 0`. -/
theorem child_line_of_parent_mid_zero (k : ℕ) (c : Fin (2*k+6) → ℂ) (h : GenPosN c)
    (i : Fin (2*k+6))
    (hv : crossVec (KP (2*k+6) c (fun j => conj (c j))) ≠ 0)
    (hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ = 0)
    (hP0  : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 ≠ 0) :
    ∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5),
      (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0 →
        ∃ t : ℝ, levelPointN (2*k+4) (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r)))) = p + (t : ℂ) * u) :=
  absurd (parent_crossVec_zero_of_mid k c i hmid hP0) hv

end Clifford.MorleyKernel

#check @Clifford.MorleyKernel.parent_mid_ker_MNF
#check @Clifford.MorleyKernel.parent_crossVec_zero_of_mid
#check @Clifford.MorleyKernel.child_line_of_parent_mid_zero
#print axioms Clifford.MorleyKernel.parent_crossVec_zero_of_mid
#print axioms Clifford.MorleyKernel.child_line_of_parent_mid_zero

namespace Clifford.MorleyKernel

open ComplexConjugate in
/-- **General-`k` `hmid` consequence.** `V⟨k+3⟩ = 0` and `V_last ≠ 0` force `P₀(w) = 0` for
every `(2k+5)`-subfamily (row relation 2 at `m = k+2`). Generalises `subfamily_P0_zero`. -/
theorem subfamily_P0_zero_gen (k : ℕ) (c : Fin (2*k+6) → ℂ)
    (hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ = 0)
    (hlast : crossVec (KP (2*k+6) c (fun j => conj (c j))) (Fin.last (2*k+6)) ≠ 0)
    (i : Fin (2*k+6)) :
    crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 = 0 := by
  have h0 : crossVec (KP (2*k+6) c (fun j => conj (c j))) 0 = 0 := by
    have E : conj (crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩)
        = crossVec (KP (2*k+6) c (fun j => conj (c j))) 0 := conj_crossVec_even (k+2) c
    rw [← E, hmid, map_zero]
  have R := rowRel2_gen (k+2) (by omega) c (fun j => conj (c j)) i
  change -(crossVec (KP (2*k+6) c (fun j => conj (c j))) 0 * _) +
      crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ * _ +
      crossVec (KP (2*k+6) c (fun j => conj (c j))) (Fin.last (2*k+6)) *
        crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 = 0 at R
  rw [h0, hmid] at R
  simp only [zero_mul, neg_zero, zero_add] at R
  exact (mul_eq_zero.1 R).resolve_left hlast

end Clifford.MorleyKernel

#check @Clifford.MorleyKernel.subfamily_P0_zero_gen
#print axioms Clifford.MorleyKernel.subfamily_P0_zero_gen

/-! ## J31: the even payload `heven_inf` -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- Packaging: a line `p + ℝ u` through the parent level point (when finite) and the finite
grandchildren gives the `heven` conclusion (`lineS` contains `∞`). -/
theorem heven_of_line (k : ℕ) (c : Fin (2*k+6) → ℂ) (i : Fin (2*k+6)) (p u : ℂ) (hu : u ≠ 0)
    (hpar : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ ≠ 0 →
      ∃ t : ℝ, levelPointN (2*k+6) (crossVec (KP (2*k+6) c (fun j => conj (c j)))) = p + (t : ℂ) * u)
    (hch : ∀ j : Fin (2*k+5), crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0 →
      ∃ t : ℝ, levelPointN (2*k+4) (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r)))) = p + (t : ℂ) * u) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      EptInf (2*k+6) c ∈ Y ∧
      ∀ j : Fin (2*k+5), EptInf (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y := by
  refine ⟨Clifford.lineS p u, Or.inr ⟨p, u, hu, rfl⟩, ?_, fun j => ?_⟩
  · have he : (⟨(2*k+6)/2, by omega⟩ : Fin (2*k+6+1)) = ⟨k+3, by omega⟩ :=
      Fin.ext (by show (2*k+6)/2 = k+3; omega)
    by_cases hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ = 0
    · rw [EptInf_eq_infty _ _ (by rw [he]; exact hmid)]
      exact Set.mem_insert _ _
    · rw [EptInf_eq_coe _ _ (by rw [he]; exact hmid)]
      obtain ⟨t, ht⟩ := hpar hmid
      exact Set.mem_insert_of_mem _ ⟨_, ⟨t, by rw [Complex.real_smul]; exact ht⟩, rfl⟩
  · by_cases hj : crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ = 0
    · rw [EptInf_child_eq_infty k _ j hj]
      exact Set.mem_insert _ _
    · rw [EptInf_child_eq_coe k _ j hj]
      obtain ⟨t, ht⟩ := hch j hj
      exact Set.mem_insert_of_mem _ ⟨_, ⟨t, by rw [Complex.real_smul]; exact ht⟩, rfl⟩

/-- A line through a point `z` and a common point `q` of the finite grandchildren. -/
theorem heven_of_common (k : ℕ) (c : Fin (2*k+6) → ℂ) (i : Fin (2*k+6)) (q : ℂ)
    (hq : ∀ j : Fin (2*k+5), crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0 →
      levelPointN (2*k+4) (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r)))) = q) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      EptInf (2*k+6) c ∈ Y ∧
      ∀ j : Fin (2*k+5), EptInf (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y := by
  set z := levelPointN (2*k+6) (crossVec (KP (2*k+6) c (fun j => conj (c j)))) with hz
  by_cases h0 : z - q = 0
  · refine heven_of_line k c i q 1 one_ne_zero (fun _ => ⟨0, ?_⟩) (fun j hj => ⟨0, ?_⟩)
    · rw [← hz]; simp; linear_combination h0
    · rw [hq j hj]; simp
  · refine heven_of_line k c i q (z - q) h0 (fun _ => ⟨1, ?_⟩) (fun j hj => ⟨0, ?_⟩)
    · rw [← hz]; push_cast; ring
    · rw [hq j hj]; simp

/-- **The `P₀ = 0` line branch** (both `hmid` cases). -/
theorem heven_line_of_P0 (k : ℕ) (c : Fin (2*k+6) → ℂ) (h : GenPosN c) (i : Fin (2*k+6))
    (hP0 : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 = 0) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      EptInf (2*k+6) c ∈ Y ∧
      ∀ j : Fin (2*k+5), EptInf (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y := by
  have hdg : GenPosN (c ∘ i.succAbove) := h.comp_succAbove i
  have hd : ∀ j, (c ∘ i.succAbove) j ≠ 0 := hc_of_genPos (by omega) _ hdg
  by_cases hQ0 : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r)))
      ⟨k+3, by omega⟩ = 0
  · have hL := QL_zero_of_P0_Q0 k _ hP0 hQ0
    have hdet : ((KP (2 * k + 5) (c ∘ i.succAbove) (fun j => conj ((c ∘ i.succAbove) j))).submatrix id
        (Fin.last (2 * k + 5)).succAbove).det = 0 := by
      unfold crossVec at hL
      exact (mul_eq_zero.1 hL).resolve_left (pow_ne_zero _ (by norm_num))
    obtain ⟨W, hW0, hW⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    exact heven_of_common k c i (-W (Fin.last _) / W ⟨k + 2, by omega⟩) (fun j hj =>
      levelPointN_of_ker k _ hj W (child_mulVec_of_parentN k _ hd W hW j) hW0)
  · have hl0 : (-1 : ℂ) ^ (k + 3) * crossVec (KP (2 * k + 5) (c ∘ i.succAbove)
        (fun j => conj ((c ∘ i.succAbove) j))) ⟨k + 3, by omega⟩ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) hQ0
    by_cases hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ = 0
    · -- parent at `∞`: only the finite grandchildren need a line
      by_cases hne : ∃ j0 : Fin (2*k+5), crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j0.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j0.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0
      · obtain ⟨j0, hj0⟩ := hne
        obtain ⟨p, u, hu, ht⟩ := collinear_of_reallin
          (fun j : {j : Fin (2*k+5) // crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
              (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0} =>
            levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) ((c ∘ i.succAbove) ∘ j.1.succAbove)
              (fun r => conj (((c ∘ i.succAbove) ∘ j.1.succAbove) r))))) ⟨j0, hj0⟩
          ((-1 : ℂ) ^ (k + 3) * crossVec (KP (2 * k + 5) (c ∘ i.succAbove)
            (fun j => conj ((c ∘ i.succAbove) j))) ⟨k + 3, by omega⟩)
          (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
            (fun r => -conj ((c ∘ i.succAbove) r) ^ (k + 2))
            (fun r => -(-(c ∘ i.succAbove) r) ^ (k + 3))).det
          (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
            (fun r => conj ((c ∘ i.succAbove) r) ^ (k + 3))
            (fun r => -(-(c ∘ i.succAbove) r) ^ (k + 3))).det hl0
          (fun j => by
            have hl := child_line_P0N k _ hd hP0 j.1 j.2
            simp only at hl
            linear_combination hl)
        exact heven_of_line k c i p u hu (fun h' => absurd hmid h') (fun j hj => ht ⟨j, hj⟩)
      · push Not at hne
        exact heven_of_line k c i 0 1 one_ne_zero (fun h' => absurd hmid h')
          (fun j hj => absurd (hne j) hj)
    · -- parent finite: one real-linear equation for the parent and the finite grandchildren
      obtain ⟨p, u, hu, ht⟩ := collinear_of_reallin
        (fun o : Option {j : Fin (2*k+5) // crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
              (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0} =>
          Option.elim o (levelPointN (2*k+6) (crossVec (KP (2*k+6) c (fun j => conj (c j)))))
            (fun j => levelPointN (2 * k + 4) (crossVec (KP (2 * k + 4) ((c ∘ i.succAbove) ∘ j.1.succAbove)
              (fun r => conj (((c ∘ i.succAbove) ∘ j.1.succAbove) r)))))) none
        ((-1 : ℂ) ^ (k + 3) * crossVec (KP (2 * k + 5) (c ∘ i.succAbove)
          (fun j => conj ((c ∘ i.succAbove) j))) ⟨k + 3, by omega⟩)
        (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
          (fun r => -conj ((c ∘ i.succAbove) r) ^ (k + 2))
          (fun r => -(-(c ∘ i.succAbove) r) ^ (k + 3))).det
        (MN k (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))
          (fun r => conj ((c ∘ i.succAbove) r) ^ (k + 3))
          (fun r => -(-(c ∘ i.succAbove) r) ^ (k + 3))).det hl0
        (fun o => by
          rcases o with _ | j
          · have hl := parent_on_child_line k c h i hmid hP0 hQ0
            simp only at hl
            simp only [Option.elim]
            linear_combination hl
          · have hl := child_line_P0N k _ hd hP0 j.1 j.2
            simp only at hl
            simp only [Option.elim]
            linear_combination hl)
      exact heven_of_line k c i p u hu (fun _ => ht none) (fun j hj => ht (some ⟨j, hj⟩))

/-- **The even payload with the residual corner as an explicit hypothesis.** `hcorner` is used
only when `V = 0` (`hmid = hlast = 0`, `P₀(d) ≠ 0`) and every grandchild is finite. -/
theorem heven_inf_of_corner (k : ℕ) (c : Fin (2*k+6) → ℂ) (h : GenPosN c) (i : Fin (2*k+6))
    (hcorner : crossVec (KP (2*k+6) c (fun j => conj (c j))) = 0 →
      crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 ≠ 0 →
      (∀ j : Fin (2*k+5), crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0) →
      ∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5), ∃ t : ℝ,
        levelPointN (2*k+4) (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
          (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r)))) = p + (t : ℂ) * u) :
    ∃ Y : Set (OnePoint ℂ), Clifford.IsGCircleS Y ∧
      EptInf (2*k+6) c ∈ Y ∧
      ∀ j : Fin (2*k+5), EptInf (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y := by
  by_cases hP0 : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 = 0
  · exact heven_line_of_P0 k c h i hP0
  have hdg : GenPosN (c ∘ i.succAbove) := h.comp_succAbove i
  by_cases hall : ∀ j : Fin (2*k+5), crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
      (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0
  · by_cases hmid : crossVec (KP (2*k+6) c (fun j => conj (c j))) ⟨k+3, by omega⟩ = 0
    · have hV := parent_crossVec_zero_of_mid k c i hmid hP0
      obtain ⟨p, u, hu, ht⟩ := hcorner hV hP0 hall
      exact heven_of_line k c i p u hu (fun h' => absurd hmid h') (fun j _ => ht j)
    · exact heven_kernel k c h i hmid hP0 hall
  · push Not at hall
    obtain ⟨q, hq⟩ := children_eq_of_P3_zero k _ hdg hP0 hall
    exact heven_of_common k c i q hq

end Clifford.MorleyKernel

#check @Clifford.MorleyKernel.heven_of_line
#check @Clifford.MorleyKernel.heven_of_common
#check @Clifford.MorleyKernel.heven_line_of_P0
#check @Clifford.MorleyKernel.heven_inf_of_corner
#print axioms Clifford.MorleyKernel.heven_of_line
#print axioms Clifford.MorleyKernel.heven_of_common
#print axioms Clifford.MorleyKernel.heven_line_of_P0
#print axioms Clifford.MorleyKernel.heven_inf_of_corner

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- **The residual corner, as a named proposition** (NOT proved): `V = 0`, `P₀(d) ≠ 0`, every
grandchild finite ⇒ the grandchildren are collinear. -/
def EvenCorner : Prop :=
  ∀ (k : ℕ) (c : Fin (2*k+6) → ℂ), GenPosN c → ∀ i : Fin (2*k+6),
    crossVec (KP (2*k+6) c (fun j => conj (c j))) = 0 →
    crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 ≠ 0 →
    (∀ j : Fin (2*k+5), crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0) →
    ∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5), ∃ t : ℝ,
      levelPointN (2*k+4) (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r)))) = p + (t : ℂ) * u

theorem heven_inf_all_of_corner (hC : EvenCorner) :
    ∀ (k : ℕ) (c : Fin (2*k+6) → ℂ), GenPosN c → ∀ i : Fin (2*k+6),
      ∃ Y, Clifford.IsGCircleS Y ∧ EptInf (2*k+6) c ∈ Y ∧
        ∀ j : Fin (2*k+5), EptInf (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y :=
  fun k c h i => heven_inf_of_corner k c h i (hC k c h i)

theorem cliffordChainS_of_corner (hC : EvenCorner) (n : ℕ) (hn : 3 ≤ n) : CliffordChainS n :=
  cliffordChainS_of_inf' (heven_inf_all_of_corner hC) n hn

end Clifford.MorleyKernel

#check @Clifford.MorleyKernel.heven_inf_all_of_corner
#check @Clifford.MorleyKernel.cliffordChainS_of_corner
#print axioms Clifford.MorleyKernel.heven_inf_all_of_corner
#print axioms Clifford.MorleyKernel.cliffordChainS_of_corner

/-! ## J32: towards `EvenCorner_proof` (work in progress) -/

namespace Clifford.MorleyKernel
open Complex ComplexConjugate Matrix

/-- **Reduction of the corner.** If the subfamily cross vector `w` has `w_last = 0` (and `w₀ ≠ 0`),
then `w` without its last entry is a common kernel vector of every grandchild matrix, so all finite
grandchild level points coincide (`= -w_{2k+4} / w_{k+2}`), in particular they are collinear. -/
theorem evenCorner_of_QL (k : ℕ) (c : Fin (2*k+6) → ℂ) (h : GenPosN c) (i : Fin (2*k+6))
    (hP0 : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 ≠ 0)
    (hQL : crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r)))
      (Fin.last _) = 0)
    (hall : ∀ j : Fin (2*k+5), crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0) :
    ∃ p u : ℂ, u ≠ 0 ∧ ∀ j : Fin (2*k+5), ∃ t : ℝ,
      levelPointN (2*k+4) (crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r)))) = p + (t : ℂ) * u := by
  have hdg : GenPosN (c ∘ i.succAbove) := h.comp_succAbove i
  have hd : ∀ j, (c ∘ i.succAbove) j ≠ 0 := hc_of_genPos (by omega) _ hdg
  set A := KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r)) with hA
  set w := crossVec A with hw
  set U : Fin (2*k+5) → ℂ := fun l => w (Fin.castSucc l) with hU
  have hU0 : U ≠ 0 := by
    intro h0
    have := congrFun h0 0
    exact hP0 this
  have hker : A.submatrix id (Fin.last (2*k+5)).succAbove *ᵥ U = 0 := by
    funext r
    have h1 := congrFun (mulVec_crossVec A) r
    simp only [mulVec, dotProduct, Pi.zero_apply] at h1 ⊢
    rw [Fin.sum_univ_castSucc] at h1
    rw [← hw, hQL, mul_zero, add_zero] at h1
    simpa [Matrix.submatrix_apply, Fin.succAbove_last, hU] using h1
  refine ⟨-U (Fin.last _) / U ⟨k + 2, by omega⟩, 1, one_ne_zero, fun j => ⟨0, ?_⟩⟩
  rw [levelPointN_of_ker k _ (hall j) U (child_mulVec_of_parentN k _ hd U hker j) hU0]
  simp

/-- The residual scalar identity: in the corner the subfamily's last coordinate vanishes. -/
def EvenCornerQL : Prop :=
  ∀ (k : ℕ) (c : Fin (2*k+6) → ℂ), GenPosN c → ∀ i : Fin (2*k+6),
    crossVec (KP (2*k+6) c (fun j => conj (c j))) = 0 →
    crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) 0 ≠ 0 →
    (∀ j : Fin (2*k+5), crossVec (KP (2*k+4) ((c ∘ i.succAbove) ∘ j.succAbove)
        (fun r => conj (((c ∘ i.succAbove) ∘ j.succAbove) r))) ⟨k+2, by omega⟩ ≠ 0) →
    crossVec (KP (2*k+5) (c ∘ i.succAbove) (fun r => conj ((c ∘ i.succAbove) r))) (Fin.last _) = 0

theorem evenCorner_of_cornerQL (hQ : EvenCornerQL) : EvenCorner :=
  fun k c h i hV hP0 hall => evenCorner_of_QL k c h i hP0 (hQ k c h i hV hP0 hall) hall

end Clifford.MorleyKernel

#check @Clifford.MorleyKernel.evenCorner_of_QL
#check @Clifford.MorleyKernel.evenCorner_of_cornerQL
#print axioms Clifford.MorleyKernel.evenCorner_of_QL
#print axioms Clifford.MorleyKernel.evenCorner_of_cornerQL
