import Mathlib

/-!
# Paper K at general `n` (K4): null cone, tangency, equal power, Prop 3.1, simplex E1
-/

namespace PaperKn

open Finset

/-- A Lie cycle in `ℝⁿ`: coordinates `(r, c, v, w)`. -/
@[ext] structure Cyc (n : ℕ) where
  r : ℝ
  c : Fin n → ℝ
  v : ℝ
  w : ℝ

variable {n : ℕ}

instance : Add (Cyc n) := ⟨fun X Y => ⟨X.r + Y.r, X.c + Y.c, X.v + Y.v, X.w + Y.w⟩⟩
instance : SMul ℝ (Cyc n) := ⟨fun a X => ⟨a * X.r, a • X.c, a * X.v, a * X.w⟩⟩

@[simp] lemma add_r (X Y : Cyc n) : (X + Y).r = X.r + Y.r := rfl
@[simp] lemma add_c (X Y : Cyc n) : (X + Y).c = X.c + Y.c := rfl
@[simp] lemma add_v (X Y : Cyc n) : (X + Y).v = X.v + Y.v := rfl
@[simp] lemma add_w (X Y : Cyc n) : (X + Y).w = X.w + Y.w := rfl
@[simp] lemma smul_r (a : ℝ) (X : Cyc n) : (a • X).r = a * X.r := rfl
@[simp] lemma smul_c (a : ℝ) (X : Cyc n) : (a • X).c = a • X.c := rfl
@[simp] lemma smul_v (a : ℝ) (X : Cyc n) : (a • X).v = a * X.v := rfl
@[simp] lemma smul_w (a : ℝ) (X : Cyc n) : (a • X).w = a * X.w := rfl

/-- The Lie form. -/
def B (X Y : Cyc n) : ℝ := X.r*Y.r - ∑ i, X.c i * Y.c i - X.v*Y.w - X.w*Y.v

/-! ## A. Null cone and basics -/

theorem B_self_eq_zero_iff (X : Cyc n) :
    B X X = 0 ↔ X.r^2 - ∑ i, (X.c i)^2 = 2 * X.v * X.w := by
  unfold B
  simp only [sq]
  constructor <;> intro h <;> linear_combination h

theorem B_comm (X Y : Cyc n) : B X Y = B Y X := by
  unfold B
  simp only [mul_comm (X.c _)]
  ring

theorem B_add_right (X Y Z : Cyc n) : B X (Y + Z) = B X Y + B X Z := by
  unfold B
  simp only [add_r, add_c, add_v, add_w, Pi.add_apply, mul_add, sum_add_distrib]
  ring

theorem B_smul_right (a : ℝ) (X Y : Cyc n) : B X (a • Y) = a * B X Y := by
  unfold B
  simp only [smul_r, smul_c, smul_v, smul_w, Pi.smul_apply, smul_eq_mul]
  rw [show ∑ i, X.c i * (a * Y.c i) = a * ∑ i, X.c i * Y.c i by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring]
  ring

theorem B_add_left (X Y Z : Cyc n) : B (X + Y) Z = B X Z + B Y Z := by
  rw [B_comm, B_add_right, B_comm Z, B_comm Z]

theorem B_smul_left (a : ℝ) (X Y : Cyc n) : B (a • X) Y = a * B X Y := by
  rw [B_comm, B_smul_right, B_comm]

/-! ## B. Tangency identity -/

lemma sum_cross_sq (a b : Fin n → ℝ) (x y : ℝ) :
    ∑ i, (a i * y - b i * x)^2
      = y^2 * ∑ i, (a i)^2 - 2 * x * y * ∑ i, a i * b i + x^2 * ∑ i, (b i)^2 := by
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

theorem tangency_identity (X Y : Cyc n) (hX : B X X = 0) (hY : B Y Y = 0) :
    -2 * X.v * Y.v * B X Y
      = (X.r*Y.v - Y.r*X.v)^2 - ∑ i, (X.c i*Y.v - Y.c i*X.v)^2 := by
  rw [sum_cross_sq]
  have hX' := (B_self_eq_zero_iff X).mp hX
  have hY' := (B_self_eq_zero_iff Y).mp hY
  unfold B
  linear_combination -(Y.v)^2 * hX' - (X.v)^2 * hY'

theorem tangency_of_B_eq_zero (X Y : Cyc n) (hX : B X X = 0) (hY : B Y Y = 0)
    (h : B X Y = 0) :
    (X.r*Y.v - Y.r*X.v)^2 - ∑ i, (X.c i*Y.v - Y.c i*X.v)^2 = 0 := by
  rw [← tangency_identity X Y hX hY, h]; ring

theorem B_eq_zero_iff_tangent (X Y : Cyc n) (hX : B X X = 0) (hY : B Y Y = 0)
    (hv : X.v ≠ 0) (hv' : Y.v ≠ 0) :
    B X Y = 0 ↔ (X.r*Y.v - Y.r*X.v)^2 = ∑ i, (X.c i*Y.v - Y.c i*X.v)^2 := by
  refine ⟨fun h => sub_eq_zero.mp (tangency_of_B_eq_zero X Y hX hY h), fun h => ?_⟩
  have hid := tangency_identity X Y hX hY
  rw [h, sub_self] at hid
  have hne : -2 * X.v * Y.v ≠ 0 := by
    have : (-2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero this hv) hv'
  exact (mul_eq_zero.mp hid).resolve_left hne


/-! ## C. Equal power -/

lemma sum_sub_sq (a b : Fin n → ℝ) :
    ∑ k, (a k - b k)^2 = ∑ k, (a k)^2 - 2 * ∑ k, a k * b k + ∑ k, (b k)^2 := by
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- **C.** Power of `(pt P, P.r/P.v)` w.r.t. an affine cycle `X` (`v = 1`, `w = (r² − ‖c‖²)/2`)
B-orthogonal to `P`: the constant `∑ (P.c k/P.v)² − (P.r/P.v)² + 2 P.w/P.v`. -/
theorem power_eq_const (P X : Cyc n) (hP : P.v ≠ 0) (hv : X.v = 1)
    (hw : X.w = (X.r^2 - ∑ k, (X.c k)^2) / 2) (h : B P X = 0) :
    (∑ k, (P.c k / P.v - X.c k)^2) - (P.r / P.v - X.r)^2
      = ∑ k, (P.c k / P.v)^2 - (P.r / P.v)^2 + 2 * P.w / P.v := by
  rw [sum_sub_sq]
  have hQ : ∑ k, P.c k / P.v * X.c k = (∑ k, P.c k * X.c k) * P.v⁻¹ := by
    rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
  rw [hQ]
  unfold B at h
  rw [hv, hw] at h
  have hinv : P.v * P.v⁻¹ = 1 := mul_inv_cancel₀ hP
  linear_combination (2 * P.v⁻¹) * h + (X.r^2 - ∑ k, (X.c k)^2) * hinv

theorem equal_power {ι : Type*} (X : ι → Cyc n) (P : Cyc n) (hP : P.v ≠ 0)
    (hv : ∀ i, (X i).v = 1) (hw : ∀ i, (X i).w = ((X i).r^2 - ∑ k, ((X i).c k)^2) / 2)
    (h : ∀ i, B P (X i) = 0) (i j : ι) :
    (∑ k, (P.c k / P.v - (X i).c k)^2) - (P.r / P.v - (X i).r)^2
      = (∑ k, (P.c k / P.v - (X j).c k)^2) - (P.r / P.v - (X j).r)^2 := by
  rw [power_eq_const P _ hP (hv i) (hw i) (h i), power_eq_const P _ hP (hv j) (hw j) (h j)]

/-! ## D. Prop 3.1 collinearity -/

/-- Affine point `P_X = c / v`. -/
noncomputable def pt (X : Cyc n) : Fin n → ℝ := fun k => X.c k / X.v

theorem pt_affine_comb (A A' : Cyc n) (α β : ℝ)
    (hA : A.v ≠ 0) (hA' : A'.v ≠ 0) (hP : (α • A + β • A').v ≠ 0) :
    ∃ s t : ℝ, s + t = 1 ∧ pt (α • A + β • A') = s • pt A + t • pt A' := by
  simp only [add_v, smul_v] at hP
  refine ⟨α * A.v / (α * A.v + β * A'.v), β * A'.v / (α * A.v + β * A'.v), ?_, ?_⟩
  · field_simp
  · funext k
    simp only [pt, add_c, add_v, smul_c, smul_v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp

/-- **D. Prop 3.1 (collinearity step)** at general `n`. -/
theorem prop31 (X : Fin (n+2) → Cyc n) (i : Fin (n+2)) (A A' P : Cyc n)
    (hspan : ∀ Y, (∀ j, j ≠ i → B Y (X j) = 0) → ∃ α β : ℝ, Y = α • A + β • A')
    (hP : ∀ j, B P (X j) = 0)
    (hA : A.v ≠ 0) (hA' : A'.v ≠ 0) (hPv : P.v ≠ 0) :
    (∃ s t : ℝ, s + t = 1 ∧ pt P = s • pt A + t • pt A') ∧
      Collinear ℝ ({pt P, pt A, pt A'} : Set (Fin n → ℝ)) := by
  obtain ⟨α, β, rfl⟩ := hspan P (fun j _ => hP j)
  obtain ⟨s, t, hst, hpt⟩ := pt_affine_comb A A' α β hA hA' hPv
  refine ⟨⟨s, t, hst, hpt⟩, ?_⟩
  apply collinear_insert_of_mem_affineSpan_pair
  have : pt (α • A + β • A') = AffineMap.lineMap (pt A) (pt A') t := by
    rw [hpt, AffineMap.lineMap_apply_module, ← hst]; simp
  rw [this]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-! ## E. The simplex instance -/

/-- Affine cycle with centre `c` and radius `r`. -/
noncomputable def aff (r : ℝ) (c : Fin n → ℝ) : Cyc n := ⟨r, c, 1, (r^2 - ∑ k, (c k)^2) / 2⟩

/-- Equal radii: `pt P` is equidistant from all centres (circumcentre reading). -/
theorem dist_sq_const {m : ℕ} (c : Fin m → Fin n → ℝ) (ρ₀ : ℝ) (P : Cyc n) (hP : P.v ≠ 0)
    (h : ∀ i, B P (aff ρ₀ (c i)) = 0) (i : Fin m) :
    ∑ k, (pt P k - c i k)^2
      = ∑ k, (P.c k / P.v)^2 - (P.r / P.v)^2 + 2 * P.w / P.v + (P.r / P.v - ρ₀)^2 := by
  have := power_eq_const P (aff ρ₀ (c i)) hP rfl rfl (h i)
  simp only [aff] at this
  simp only [pt]
  linarith

/-- Linear core: a vector orthogonal to `n+1` affinely independent points of `ℝⁿ` is zero. -/
theorem eq_zero_of_orth_affineIndependent {m : ℕ} (hm : m = n + 1) (c : Fin m → Fin n → ℝ)
    (hc : AffineIndependent ℝ c) (p : Fin n → ℝ) (hp : ∀ i, ∑ k, p k * c i k = 0) : p = 0 := by
  have htop : affineSpan ℝ (Set.range c) = ⊤ := by
    rw [hc.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_fin,
      Module.finrank_fin_fun, hm]
  have hmem : p ∈ affineSpan ℝ (Set.range c) := by rw [htop]; trivial
  obtain ⟨w, hw1, hpw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hmem
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1] at hpw
  have hpp : ∑ k, p k * p k = 0 := by
    have e : ∑ k, p k * p k = ∑ k, p k * (∑ i, w i • c i) k := by rw [← hpw]
    rw [e]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
    rw [sum_comm]
    refine sum_eq_zero fun i _ => ?_
    rw [show ∑ k, p k * (w i * c i k) = w i * ∑ k, p k * c i k by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring, hp i, mul_zero]
  funext k
  have := (sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg (p k))).mp hpp k (mem_univ k)
  exact mul_self_eq_zero.mp this

/-- **E (corrected).** `n+1` affinely independent unit circles/spheres whose centres have
centroid `0` and are equidistant from it (e.g. a regular simplex), plus any affine cycle `X₀`:
if `P ⊥_B` all of them with `P.v ≠ 0`, then `pt P = 0`. -/
theorem simplex_E1 {m : ℕ} (hm : m = n + 1) (c : Fin m → Fin n → ℝ)
    (hsum : ∑ i, c i = 0) (hc : AffineIndependent ℝ c)
    (hnorm : ∀ i j, ∑ k, (c i k)^2 = ∑ k, (c j k)^2)
    (X₀ : Cyc n) (P : Cyc n) (hPv : P.v ≠ 0)
    (hP : ∀ i, B P (aff 1 (c i)) = 0) (_hP0 : B P X₀ = 0) :
    pt P = 0 := by
  subst hm
  set d := ∑ k, (P.c k / P.v)^2 - (P.r / P.v)^2 + 2 * P.w / P.v + (P.r / P.v - 1)^2
  have hd := dist_sq_const c 1 P hPv hP
  set p := pt P
  -- `⟨p, c_i⟩ = κ` for every `i`
  set κ := (∑ k, (p k)^2 + ∑ k, (c 0 k)^2 - d) / 2
  have hκ : ∀ i, ∑ k, p k * c i k = κ := by
    intro i
    have := hd i
    rw [sum_sub_sq, hnorm i 0] at this
    simp only [κ]; linarith
  have hsumk : ∀ k, ∑ i, c i k = 0 := fun k => by
    have := congrFun hsum k; simpa [Finset.sum_apply] using this
  have htot : ∑ i, ∑ k, p k * c i k = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun k _ => ?_
    rw [← mul_sum, hsumk k, mul_zero]
  simp only [hκ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
  have hκ0 : κ = 0 := by
    rcases mul_eq_zero.mp htot with h | h
    · exact absurd h (by positivity)
    · exact h
  exact eq_zero_of_orth_affineIndependent rfl c hc p (fun i => by rw [hκ i, hκ0])


/-! ## F. Circumcentre reading -/

/-- **F.** Under the hypotheses of `simplex_E1`, the common squared distance
`d = ∑ (pt P − c_i)²` equals `‖c_i‖²`, the squared circumradius of the simplex. -/
theorem simplex_circumradius {m : ℕ} (hm : m = n + 1) (c : Fin m → Fin n → ℝ)
    (hsum : ∑ i, c i = 0) (hc : AffineIndependent ℝ c)
    (hnorm : ∀ i j, ∑ k, (c i k)^2 = ∑ k, (c j k)^2)
    (X₀ : Cyc n) (P : Cyc n) (hPv : P.v ≠ 0)
    (hP : ∀ i, B P (aff 1 (c i)) = 0) (hP0 : B P X₀ = 0) (i : Fin m) :
    ∑ k, (c i k)^2
      = ∑ k, (P.c k / P.v)^2 - (P.r / P.v)^2 + 2 * P.w / P.v + (P.r / P.v - 1)^2 := by
  have h0 := simplex_E1 hm c hsum hc hnorm X₀ P hPv hP hP0
  rw [← dist_sq_const c 1 P hPv hP i, h0]
  simp

/-! ## Counterexample: without `hnorm` the brief's E fails (n = 2).
Centres `(-1,-1), (2,-1), (-1,2)` (centroid `0`, a right triangle), unit radii,
`X₀ = aff 3 (3,3)`, `P = (0, (1/2,1/2), 1, 3/2)`: `pt P = (1/2,1/2)` is the circumcentre. -/

def cex_c : Fin 3 → Fin 2 → ℝ := ![![-1, -1], ![2, -1], ![-1, 2]]
noncomputable def cex_P : Cyc 2 := ⟨0, ![1/2, 1/2], 1, 3/2⟩

theorem cex_sum : ∑ i, cex_c i = 0 := by
  funext k; fin_cases k <;> simp [cex_c, Fin.sum_univ_three] <;> norm_num

theorem cex_affInd : AffineIndependent ℝ cex_c := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [cex_c, Fin.sum_univ_three] at h0 h1 hw
  fin_cases i <;> simp <;> linarith

theorem cex_orth : (∀ i, B cex_P (aff 1 (cex_c i)) = 0) ∧ B cex_P (aff 3 ![3, 3]) = 0 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [B, aff, cex_P, cex_c, Fin.sum_univ_two] <;> norm_num
  · simp [B, aff, cex_P, Fin.sum_univ_two]; norm_num

theorem cex_pt_ne : pt cex_P ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [pt, cex_P] at this

/-- The brief's statement of E (no equal-norm hypothesis) is false. -/
theorem brief_E_false : ¬ (∀ (c : Fin 3 → Fin 2 → ℝ), ∑ i, c i = 0 → AffineIndependent ℝ c →
    ∀ (X₀ P : Cyc 2), P.v ≠ 0 → (∀ i, B P (aff 1 (c i)) = 0) → B P X₀ = 0 → pt P = 0) := by
  intro H
  exact cex_pt_ne (H cex_c cex_sum cex_affInd _ cex_P (by simp [cex_P]) cex_orth.1 cex_orth.2)

end PaperKn

#print axioms PaperKn.B_self_eq_zero_iff
#print axioms PaperKn.B_add_right
#print axioms PaperKn.B_smul_right
#print axioms PaperKn.tangency_identity
#print axioms PaperKn.B_eq_zero_iff_tangent
#print axioms PaperKn.power_eq_const
#print axioms PaperKn.equal_power
#print axioms PaperKn.prop31
#print axioms PaperKn.dist_sq_const
#print axioms PaperKn.eq_zero_of_orth_affineIndependent
#print axioms PaperKn.simplex_E1
#print axioms PaperKn.simplex_circumradius
#print axioms PaperKn.brief_E_false
