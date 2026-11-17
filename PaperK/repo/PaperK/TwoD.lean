import Mathlib

/-!
# Paper K, extension E1 in ℝ²: the degenerate locus is removable

Cycles `X = (r, a, b, v, w)` (indices 0..4), bilinear form
`B(X,Y) = r r' − a a' − b b' − v w' − w v'`.
Affine circle: `circ r a b = (r, a, b, 1, (r² − a² − b²)/2)`.
-/

namespace PaperK2

noncomputable section

/-- Płatek bilinear form on `Fin 5 → ℝ`. -/
def B (X Y : Fin 5 → ℝ) : ℝ :=
  X 0 * Y 0 - X 1 * Y 1 - X 2 * Y 2 - X 3 * Y 4 - X 4 * Y 3

/-- Affine oriented circle with centre `(a,b)` and signed radius `r`. -/
def circ (r a b : ℝ) : Fin 5 → ℝ := ![r, a, b, 1, (r ^ 2 - a ^ 2 - b ^ 2) / 2]

/-- Laguerre power `‖p − c‖² − (ρ − r)²` of the point/cycle `P` (normalised by `P 3`)
with respect to the circle of centre `(a,b)`, radius `r`. -/
def pw (P : Fin 5 → ℝ) (r a b : ℝ) : ℝ :=
  (P 1 / P 3 - a) ^ 2 + (P 2 / P 3 - b) ^ 2 - (P 0 / P 3 - r) ^ 2

/-- The constant value of the power. -/
def pconst (P : Fin 5 → ℝ) : ℝ :=
  (P 1 / P 3) ^ 2 + (P 2 / P 3) ^ 2 - (P 0 / P 3) ^ 2 + 2 * (P 4 / P 3)

lemma B_circ (P : Fin 5 → ℝ) (r a b : ℝ) :
    B P (circ r a b) = P 0 * r - P 1 * a - P 2 * b - P 3 * ((r ^ 2 - a ^ 2 - b ^ 2) / 2) - P 4 := by
  simp [B, circ]

/-! ## A. equal_power -/

/-- Pointwise form: orthogonality to one circle pins its power to `pconst P`. -/
theorem power_eq_const (P : Fin 5 → ℝ) (hP : P 3 ≠ 0) (r a b : ℝ)
    (h : B P (circ r a b) = 0) : pw P r a b = pconst P := by
  rw [B_circ] at h
  unfold pw pconst
  field_simp
  linear_combination (2 * P 3) * h

/-- **A. equal_power.** For a family of circles indexed by `ι`, all B-orthogonal to `P`
with `P 3 ≠ 0`, the Laguerre power `‖p − c_i‖² − (ρ − r_i)²` is independent of `i`. -/
theorem equal_power {ι : Type*} (P : Fin 5 → ℝ) (hP : P 3 ≠ 0)
    (r a b : ι → ℝ) (h : ∀ i, B P (circ (r i) (a i) (b i)) = 0) (i j : ι) :
    pw P (r i) (a i) (b i) = pw P (r j) (a j) (b j) := by
  rw [power_eq_const P hP _ _ _ (h i), power_eq_const P hP _ _ _ (h j)]

/-! ## D. Uniqueness (and existence) of the equal-power point -/

/-- Equidistance from three points. -/
def Equi (x y : ℝ) (a b : Fin 3 → ℝ) : Prop :=
  (x - a 0) ^ 2 + (y - b 0) ^ 2 = (x - a 1) ^ 2 + (y - b 1) ^ 2 ∧
  (x - a 0) ^ 2 + (y - b 0) ^ 2 = (x - a 2) ^ 2 + (y - b 2) ^ 2

/-- Non-collinearity determinant. -/
def D3 (a b : Fin 3 → ℝ) : ℝ := (a 1 - a 0) * (b 2 - b 0) - (a 2 - a 0) * (b 1 - b 0)

/-- **D (uniqueness).** Two points equidistant from three non-collinear points coincide. -/
theorem equi_unique (a b : Fin 3 → ℝ) (hD : D3 a b ≠ 0) (x y x' y' : ℝ)
    (h : Equi x y a b) (h' : Equi x' y' a b) : x = x' ∧ y = y' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  unfold D3 at hD
  -- linear system: 2(a1-a0)(x-x') + 2(b1-b0)(y-y') = 0, same with index 2
  have e1 : (a 1 - a 0) * (x - x') + (b 1 - b 0) * (y - y') = 0 := by nlinarith
  have e2 : (a 2 - a 0) * (x - x') + (b 2 - b 0) * (y - y') = 0 := by nlinarith
  have hx : ((a 1 - a 0) * (b 2 - b 0) - (a 2 - a 0) * (b 1 - b 0)) * (x - x') = 0 := by
    linear_combination (b 2 - b 0) * e1 - (b 1 - b 0) * e2
  have hy : ((a 1 - a 0) * (b 2 - b 0) - (a 2 - a 0) * (b 1 - b 0)) * (y - y') = 0 := by
    linear_combination (a 1 - a 0) * e2 - (a 2 - a 0) * e1
  rcases mul_eq_zero.1 hx with h | h
  · exact absurd h hD
  rcases mul_eq_zero.1 hy with h' | h'
  · exact absurd h' hD
  exact ⟨by linarith, by linarith⟩

/-- Explicit circumcentre (Cramer). -/
def ccx (a b : Fin 3 → ℝ) : ℝ :=
  (((a 1) ^ 2 - (a 0) ^ 2 + (b 1) ^ 2 - (b 0) ^ 2) * (b 2 - b 0)
    - ((a 2) ^ 2 - (a 0) ^ 2 + (b 2) ^ 2 - (b 0) ^ 2) * (b 1 - b 0)) / (2 * D3 a b)
def ccy (a b : Fin 3 → ℝ) : ℝ :=
  ((a 1 - a 0) * ((a 2) ^ 2 - (a 0) ^ 2 + (b 2) ^ 2 - (b 0) ^ 2)
    - (a 2 - a 0) * ((a 1) ^ 2 - (a 0) ^ 2 + (b 1) ^ 2 - (b 0) ^ 2)) / (2 * D3 a b)

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

/-- **D (existence).** The explicit circumcentre is equidistant. -/
theorem equi_cc (a b : Fin 3 → ℝ) (hD : D3 a b ≠ 0) : Equi (ccx a b) (ccy a b) a b :=
  cc_generic (a 0) (a 1) (a 2) (b 0) (b 1) (b 2) hD _ _ rfl rfl

/-- **D.** The equal-power set is exactly one point. -/
theorem equi_iff (a b : Fin 3 → ℝ) (hD : D3 a b ≠ 0) (x y : ℝ) :
    Equi x y a b ↔ (x = ccx a b ∧ y = ccy a b) := by
  constructor
  · intro h; exact equi_unique a b hD _ _ _ _ h (equi_cc a b hD)
  · rintro ⟨rfl, rfl⟩; exact equi_cc a b hD

/-- **D (Laguerre form).** For three circles of a common radius `r₀` with non-collinear centres,
the points `(x,y)` having equal Laguerre power (for any fixed `ρ`) to all three form a single point. -/
theorem equal_power_point_unique (a b : Fin 3 → ℝ) (hD : D3 a b ≠ 0) (r₀ ρ x y : ℝ) :
    ((x - a 0) ^ 2 + (y - b 0) ^ 2 - (ρ - r₀) ^ 2 = (x - a 1) ^ 2 + (y - b 1) ^ 2 - (ρ - r₀) ^ 2 ∧
     (x - a 0) ^ 2 + (y - b 0) ^ 2 - (ρ - r₀) ^ 2 = (x - a 2) ^ 2 + (y - b 2) ^ 2 - (ρ - r₀) ^ 2)
    ↔ (x = ccx a b ∧ y = ccy a b) := by
  rw [← equi_iff a b hD]
  unfold Equi
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-! ## E. Equal-radius circles at any triangle: `P_X` is the circumcentre -/

/-- **E.** If `P` (with `P 3 ≠ 0`) is B-orthogonal to three circles of equal radius `r₀` with
non-collinear centres (plus any further circles — not needed), then `P_X` is the circumcentre. -/
theorem PX_circumcentre (P : Fin 5 → ℝ) (hP : P 3 ≠ 0) (a b : Fin 3 → ℝ) (hD : D3 a b ≠ 0)
    (r₀ : ℝ) (h : ∀ i, B P (circ r₀ (a i) (b i)) = 0) :
    P 1 / P 3 = ccx a b ∧ P 2 / P 3 = ccy a b := by
  have e := equal_power P hP (fun _ => r₀) a b h
  rw [← equal_power_point_unique a b hD r₀ (P 0 / P 3)]
  exact ⟨e 0 1, e 0 2⟩

/-! ## B. Equilateral triple -/

/-- **B (parameter form).** Unit circles at `(0,0),(2,0),(1,t)` with `t² = 3`, `t > 0`, and an
arbitrary fourth circle `(r,a,b)`; `P` B-orthogonal to all four with `P 3 ≠ 0`.
Then `P_X = (1, t/3)`. -/
theorem equilateral_PX_param (t : ℝ) (ht : t ^ 2 = 3) (htpos : 0 < t)
    (P : Fin 5 → ℝ) (hP : P 3 ≠ 0) (r a b : ℝ)
    (h1 : B P (circ 1 0 0) = 0) (h2 : B P (circ 1 2 0) = 0) (h3 : B P (circ 1 1 t) = 0)
    (_h4 : B P (circ r a b) = 0) :
    P 1 / P 3 = 1 ∧ P 2 / P 3 = t / 3 := by
  have e1 := power_eq_const P hP _ _ _ h1
  have e2 := power_eq_const P hP _ _ _ h2
  have e3 := power_eq_const P hP _ _ _ h3
  unfold pw at e1 e2 e3
  set x := P 1 / P 3
  set y := P 2 / P 3
  have hx : x = 1 := by nlinarith
  refine ⟨hx, ?_⟩
  clear_value x y
  have : 2 * t * y = 2 := by
    subst hx; nlinarith
  have htne : t ≠ 0 := htpos.ne'
  field_simp
  nlinarith

/-- **B (headline, `Real.sqrt 3`).** `P_X = (1, √3/3)`. -/
theorem equilateral_PX (P : Fin 5 → ℝ) (hP : P 3 ≠ 0) (r a b : ℝ)
    (h1 : B P (circ 1 0 0) = 0) (h2 : B P (circ 1 2 0) = 0)
    (h3 : B P (circ 1 1 (Real.sqrt 3)) = 0) (h4 : B P (circ r a b) = 0) :
    (P 1 / P 3, P 2 / P 3) = ((1 : ℝ), Real.sqrt 3 / 3) := by
  obtain ⟨hx, hy⟩ := equilateral_PX_param (Real.sqrt 3) (Real.sq_sqrt (by norm_num))
    (Real.sqrt_pos.2 (by norm_num)) P hP r a b h1 h2 h3 h4
  rw [hx, hy]

/-- The point `(1, √3/3)` is the unique point equidistant from the three vertices. -/
theorem equilateral_centre_unique (x y : ℝ) :
    (x ^ 2 + y ^ 2 = (x - 2) ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 = (x - 1) ^ 2 + (y - Real.sqrt 3) ^ 2)
    ↔ (x = 1 ∧ y = Real.sqrt 3 / 3) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x = 1 := by nlinarith
    refine ⟨hx, ?_⟩
    subst hx
    have : 2 * Real.sqrt 3 * y = 2 := by nlinarith
    field_simp
    nlinarith
  · rintro ⟨rfl, rfl⟩
    constructor
    · ring
    · field_simp; nlinarith

/-! ## C. Square of four unit circles -/

/-- Square centres `(1,1), (−1,1), (−1,−1), (1,−1)`. -/
def sqa : Fin 4 → ℝ := ![1, -1, -1, 1]
def sqb : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- Oriented tangency (Laguerre power zero) of the oriented circle `(x,y;ρ)` to the circle
`(a,b;r)`: `‖(x,y) − (a,b)‖² = (ρ − r)²`. -/
def Tangent (x y ρ a b r : ℝ) : Prop := (x - a) ^ 2 + (y - b) ^ 2 = (ρ - r) ^ 2

/-- **C.1.** For each 3-subset (omit index `k`) of the four unit circles of the square, an oriented
circle is tangent to the three remaining ones iff it is centred at `(0,0)` with radius `1 ± √2`.
So the two Apollonius solutions are concentric (common centre, distinct radii). -/
theorem square_apollonius (k : Fin 4) (x y ρ : ℝ) :
    (∀ i : Fin 4, i ≠ k → Tangent x y ρ (sqa i) (sqb i) 1) ↔
    (x = 0 ∧ y = 0 ∧ (ρ = 1 + Real.sqrt 2 ∨ ρ = 1 - Real.sqrt 2)) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have rho_iff : (ρ - 1) ^ 2 = 2 ↔ (ρ = 1 + Real.sqrt 2 ∨ ρ = 1 - Real.sqrt 2) := by
    constructor
    · intro h
      have : (ρ - 1 - Real.sqrt 2) * (ρ - 1 + Real.sqrt 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> subst h <;> nlinarith
  rw [← rho_iff]
  fin_cases k <;> simp [Tangent, sqa, sqb, Fin.forall_fin_succ] <;>
  · constructor
    · intro h
      obtain ⟨h1, h2, h3⟩ := h
      have hx : x = 0 := by nlinarith
      have hy : y = 0 := by nlinarith
      subst hx hy
      exact ⟨rfl, rfl, by nlinarith⟩
    · rintro ⟨rfl, rfl, h⟩
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- The two concentric solutions really have distinct radii. -/
theorem square_apollonius_radii_ne : (1 + Real.sqrt 2 : ℝ) ≠ 1 - Real.sqrt 2 := by
  have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  intro h; linarith

/-- **C.2 (null space, exact).** For the four unit circles of the square, `P` is B-orthogonal to all
four iff `P 1 = 0`, `P 2 = 0`, `P 4 = P 0 + P 3 / 2`. So the `4 × 5` matrix has rank 3 (null space
of dimension 2 — a rank drop from the generic 4; all 4×4 minors vanish, no canonical cofactor
vector), and **every** null vector has its centre slots zero. -/
theorem square_null_space (P : Fin 5 → ℝ) :
    (∀ i : Fin 4, B P (circ 1 (sqa i) (sqb i)) = 0) ↔
    (P 1 = 0 ∧ P 2 = 0 ∧ P 4 = P 0 + P 3 / 2) := by
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, B_circ, sqa, sqb]
  simp
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    refine ⟨by ring, by ring, by ring, by ring⟩

/-- The null space is genuinely 2-dimensional: it is exactly the span of two explicit
independent null vectors `(1,0,0,0,1)` and `(0,0,0,1,1/2)`. -/
theorem square_null_span (P : Fin 5 → ℝ) :
    (∀ i : Fin 4, B P (circ 1 (sqa i) (sqb i)) = 0) ↔
    ∃ s u : ℝ, P = s • ![1, 0, 0, 0, 1] + u • ![0, 0, 0, 1, 1 / 2] := by
  rw [square_null_space]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨P 0, P 3, ?_⟩
    funext i
    fin_cases i <;> simp [h1, h2, h3] <;> ring
  · rintro ⟨s, u, rfl⟩
    simp
    ring

/-- The two spanning vectors are linearly independent (so the rank of the 4×5 matrix is 3). -/
theorem square_null_indep (s u : ℝ)
    (h : s • (![1, 0, 0, 0, 1] : Fin 5 → ℝ) + u • ![0, 0, 0, 1, 1 / 2] = 0) : s = 0 ∧ u = 0 := by
  have h0 := congrFun h 0
  have h3 := congrFun h 3
  simp at h0 h3
  exact ⟨h0, h3⟩

/-- **C.2 (point).** Any null vector with `P 3 ≠ 0` gives `P_X = (0,0)`. -/
theorem square_PX (P : Fin 5 → ℝ) (_hP : P 3 ≠ 0)
    (h : ∀ i : Fin 4, B P (circ 1 (sqa i) (sqb i)) = 0) :
    (P 1 / P 3, P 2 / P 3) = ((0 : ℝ), (0 : ℝ)) := by
  obtain ⟨h1, h2, -⟩ := (square_null_space P).1 h
  simp [h1, h2]

/-- **C (via equal_power, the "removable" mechanism).** Same conclusion obtained only from
`equal_power` + the equidistance uniqueness of D applied to the triple omitting the 4th circle. -/
theorem square_PX_via_equal_power (P : Fin 5 → ℝ) (hP : P 3 ≠ 0)
    (h : ∀ i : Fin 4, B P (circ 1 (sqa i) (sqb i)) = 0) :
    P 1 / P 3 = 0 ∧ P 2 / P 3 = 0 := by
  have ha : (fun i : Fin 3 => sqa i.castSucc) = ![1, -1, -1] := by
    funext i; fin_cases i <;> rfl
  have hb : (fun i : Fin 3 => sqb i.castSucc) = ![1, 1, -1] := by
    funext i; fin_cases i <;> rfl
  have h' : ∀ i : Fin 3, B P (circ 1 ((![1, -1, -1] : Fin 3 → ℝ) i) ((![1, 1, -1] : Fin 3 → ℝ) i)) = 0 := by
    intro i
    have := h i.castSucc
    rw [← ha, ← hb]
    exact this
  have a2 : (![1, -1, -1] : Fin 3 → ℝ) 2 = -1 := rfl
  have b2 : (![1, 1, -1] : Fin 3 → ℝ) 2 = -1 := rfl
  have e := PX_circumcentre P hP ![1, -1, -1] ![1, 1, -1] (by norm_num [D3, a2, b2]) 1 h'
  rw [e.1, e.2]
  norm_num [ccx, ccy, D3, a2, b2]

end

end PaperK2

#print axioms PaperK2.equal_power
#print axioms PaperK2.power_eq_const
#print axioms PaperK2.equilateral_PX_param
#print axioms PaperK2.equilateral_PX
#print axioms PaperK2.equilateral_centre_unique
#print axioms PaperK2.square_apollonius
#print axioms PaperK2.square_apollonius_radii_ne
#print axioms PaperK2.square_null_space
#print axioms PaperK2.square_null_span
#print axioms PaperK2.square_null_indep
#print axioms PaperK2.square_PX
#print axioms PaperK2.square_PX_via_equal_power
#print axioms PaperK2.equi_unique
#print axioms PaperK2.equi_cc
#print axioms PaperK2.equi_iff
#print axioms PaperK2.equal_power_point_unique
#print axioms PaperK2.PX_circumcentre
