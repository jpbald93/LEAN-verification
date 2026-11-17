import Inversion

/-!
# L15 item I5b: geometric existence (and classification) of the two Soddy circles

Classical definitions copied verbatim from `PaperIClassical.lean` (sha256 prefix
`1c595a90ccb3925a`), namespace renamed to `SoddyExists`.

Main results:
* `soddyCentre` — the explicit centre of the fourth circle of signed radius `ρ`, as an affine
  combination of the three given centres with rational coefficients in `r₀, r₁, r₂, ρ`;
* `soddy_tangent` — if `1/ρ` is a root of the Descartes quadratic, the circle
  `(soddyCentre C ρ, ρ)` is (signed-)tangent to all three given circles;
* `classical_I5b` — the L15 statement I5b, verbatim: for `ε = ±1` and
  `κ = k₀+k₁+k₂ + ε·2√(k₀k₁+k₁k₂+k₂k₀) ≠ 0` there is a centre `c` making
  `C 0, C 1, C 2, (c, 1/κ)` a Descartes configuration;
* `soddy_centre_unique` — a circle of given signed radius tangent to the triple has a unique
  centre;
* `soddy_classify` — every signed circle completing a Descartes configuration with the triple has
  curvature `κ₊` or `κ₋` and centre `soddyCentre C ρ`;
* `soddy_exactly_two` — `κ₊ > 0`, `κ₊ ≠ κ₋`, and the signed circles tangent to the triple are
  exactly the inner Soddy circle and, when `κ₋ ≠ 0`, the outer one.
The curvatures come from `Inversion.descartes_solve`; the "only these curvatures" direction uses
`Inversion.descartes`.
-/

open EuclideanGeometry RealInnerProductSpace

local notation "E2" => EuclideanSpace ℝ (Fin 2)

noncomputable section

namespace SoddyExists

/-! ## Verbatim classical definitions -/

/-- A circle with *signed* radius: `(centre, ρ)`, `ρ ≠ 0`; `ρ < 0` marks an enclosing
circle.  Signed curvature is `1/ρ`.  Two such circles are tangent in the Descartes sense:
both positive → externally tangent; one negative → the positive one is inside the negative
one and internally tangent to it; never both negative. -/
def ClassicalSignedTangent (x y : E2 × ℝ) : Prop :=
  x.2 ≠ 0 ∧ y.2 ≠ 0 ∧ ¬ (x.2 < 0 ∧ y.2 < 0) ∧
    ((x.2 < 0 ∨ y.2 < 0) → x.2 + y.2 < 0) ∧ dist x.1 y.1 = |x.2 + y.2|

/-- `n` mutually tangent circles with signed radii (Descartes configuration for `n = 4`). -/
def ClassicalMutuallyTangent {n : ℕ} (C : Fin n → E2 × ℝ) : Prop :=
  (∀ i, (C i).2 ≠ 0) ∧ ∀ i j, i ≠ j → ClassicalSignedTangent (C i) (C j)

/-! ## Pure algebra -/

/-- Numerator of the coefficient of `c₁ - c₀`. -/
def numS (r₁ r₂ r₃ p : ℝ) : ℝ :=
  r₁ ^ 2 * r₂ * r₃ - r₁ ^ 2 * r₂ * p + r₁ ^ 2 * r₃ * p + r₁ * r₂ * r₃ ^ 2 + r₁ * r₃ ^ 2 * p
    - r₂ * r₃ ^ 2 * p

/-- Numerator of the coefficient of `c₂ - c₀`. -/
def numT (r₁ r₂ r₃ p : ℝ) : ℝ :=
  r₁ ^ 2 * r₂ * r₃ + r₁ ^ 2 * r₂ * p - r₁ ^ 2 * r₃ * p + r₁ * r₂ ^ 2 * r₃ + r₁ * r₂ ^ 2 * p
    - r₂ ^ 2 * r₃ * p

/-- Common denominator. -/
def den (r₁ r₂ r₃ : ℝ) : ℝ := 2 * r₁ * r₂ * r₃ * (r₁ + r₂ + r₃)

/-- The Descartes polynomial in radii (`= -(r₁r₂r₃p)² · descartesForm (1/r₁) (1/r₂) (1/r₃) (1/p)`). -/
def polyP (r₁ r₂ r₃ p : ℝ) : ℝ :=
  r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2 - 2 * r₁ ^ 2 * r₂ ^ 2 * r₃ * p + r₁ ^ 2 * r₂ ^ 2 * p ^ 2
    - 2 * r₁ ^ 2 * r₂ * r₃ ^ 2 * p - 2 * r₁ ^ 2 * r₂ * r₃ * p ^ 2 + r₁ ^ 2 * r₃ ^ 2 * p ^ 2
    - 2 * r₁ * r₂ ^ 2 * r₃ ^ 2 * p - 2 * r₁ * r₂ ^ 2 * r₃ * p ^ 2 - 2 * r₁ * r₂ * r₃ ^ 2 * p ^ 2
    + r₂ ^ 2 * r₃ ^ 2 * p ^ 2

theorem polyP_eq (r₁ r₂ r₃ p : ℝ) (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0) (hp : p ≠ 0) :
    polyP r₁ r₂ r₃ p =
      -(r₁ * r₂ * r₃ * p) ^ 2 * Inversion.descartesForm (1 / r₁) (1 / r₂) (1 / r₃) (1 / p) := by
  unfold polyP Inversion.descartesForm
  field_simp
  ring

/-- Quadratic form of `α u + β v` from the three side lengths of the centre triangle. -/
theorem gen_sq (ux uy vx vy α β A B C₂₃ : ℝ)
    (h12 : ux ^ 2 + uy ^ 2 = A) (h13 : vx ^ 2 + vy ^ 2 = B)
    (h23 : (vx - ux) ^ 2 + (vy - uy) ^ 2 = C₂₃) :
    (α * ux + β * vx) ^ 2 + (α * uy + β * vy) ^ 2 =
      (α ^ 2 + α * β) * A + (β ^ 2 + α * β) * B - α * β * C₂₃ := by
  linear_combination (α ^ 2 + α * β) * h12 + (β ^ 2 + α * β) * h13 - α * β * h23

/-- The three case identities (pure `ring`): with `P = 0` they say the candidate centre is at
distance `|rᵢ + p|` from each given centre. -/
theorem case0 (r₁ r₂ r₃ p : ℝ) :
    let α := numS r₁ r₂ r₃ p; let β := numT r₁ r₂ r₃ p
    (α ^ 2 + α * β) * (r₁ + r₂) ^ 2 + (β ^ 2 + α * β) * (r₁ + r₃) ^ 2 - α * β * (r₂ + r₃) ^ 2 =
      den r₁ r₂ r₃ ^ 2 * (r₁ + p) ^ 2 + 2 * den r₁ r₂ r₃ * polyP r₁ r₂ r₃ p := by
  intro α β; simp only [α, β, numS, numT, den, polyP]; ring

theorem case1 (r₁ r₂ r₃ p : ℝ) :
    let α := numS r₁ r₂ r₃ p - den r₁ r₂ r₃; let β := numT r₁ r₂ r₃ p
    (α ^ 2 + α * β) * (r₁ + r₂) ^ 2 + (β ^ 2 + α * β) * (r₁ + r₃) ^ 2 - α * β * (r₂ + r₃) ^ 2 =
      den r₁ r₂ r₃ ^ 2 * (r₂ + p) ^ 2 + 2 * den r₁ r₂ r₃ * polyP r₁ r₂ r₃ p := by
  intro α β; simp only [α, β, numS, numT, den, polyP]; ring

theorem case2 (r₁ r₂ r₃ p : ℝ) :
    let α := numS r₁ r₂ r₃ p; let β := numT r₁ r₂ r₃ p - den r₁ r₂ r₃
    (α ^ 2 + α * β) * (r₁ + r₂) ^ 2 + (β ^ 2 + α * β) * (r₁ + r₃) ^ 2 - α * β * (r₂ + r₃) ^ 2 =
      den r₁ r₂ r₃ ^ 2 * (r₃ + p) ^ 2 + 2 * den r₁ r₂ r₃ * polyP r₁ r₂ r₃ p := by
  intro α β; simp only [α, β, numS, numT, den, polyP]; ring

/-! ## Coordinates in `E2` -/

theorem dist_sq2 (x y : E2) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- The explicit centre of the circle of signed radius `p` tangent to the three circles. -/
def soddyCentre (C : Fin 3 → E2 × ℝ) (p : ℝ) : E2 :=
  (C 0).1 + (numS (C 0).2 (C 1).2 (C 2).2 p / den (C 0).2 (C 1).2 (C 2).2) • ((C 1).1 - (C 0).1)
    + (numT (C 0).2 (C 1).2 (C 2).2 p / den (C 0).2 (C 1).2 (C 2).2) • ((C 2).1 - (C 0).1)

theorem soddyCentre_apply (C : Fin 3 → E2 × ℝ) (p : ℝ) (i : Fin 2) :
    soddyCentre C p i = (C 0).1 i
      + numS (C 0).2 (C 1).2 (C 2).2 p / den (C 0).2 (C 1).2 (C 2).2 * ((C 1).1 i - (C 0).1 i)
      + numT (C 0).2 (C 1).2 (C 2).2 p / den (C 0).2 (C 1).2 (C 2).2 * ((C 2).1 i - (C 0).1 i) := by
  simp [soddyCentre]

/-- **Tangency of the explicit circle.** If the three circles are pairwise externally tangent with
positive radii and `p` is a root of the Descartes polynomial, the circle centred at
`soddyCentre C p` with signed radius `p` is at distance `|rᵢ + p|` from each centre. -/
theorem soddy_dist_sq (C : Fin 3 → E2 × ℝ) (hpos : ∀ i, 0 < (C i).2)
    (h01 : dist (C 0).1 (C 1).1 = (C 0).2 + (C 1).2)
    (h02 : dist (C 0).1 (C 2).1 = (C 0).2 + (C 2).2)
    (h12 : dist (C 1).1 (C 2).1 = (C 1).2 + (C 2).2)
    (p : ℝ) (hP : polyP (C 0).2 (C 1).2 (C 2).2 p = 0) (j : Fin 3) :
    dist (soddyCentre C p) (C j).1 ^ 2 = ((C j).2 + p) ^ 2 := by
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  set r₁ := (C 0).2; set r₂ := (C 1).2; set r₃ := (C 2).2
  have hD : den r₁ r₂ r₃ ≠ 0 := by unfold den; positivity
  have e01 := congrArg (· ^ 2) h01; have e02 := congrArg (· ^ 2) h02
  have e12 := congrArg (· ^ 2) h12
  simp only [dist_sq2] at e01 e02 e12
  set ux := (C 1).1 0 - (C 0).1 0; set uy := (C 1).1 1 - (C 0).1 1
  set vx := (C 2).1 0 - (C 0).1 0; set vy := (C 2).1 1 - (C 0).1 1
  have A : ux ^ 2 + uy ^ 2 = (r₁ + r₂) ^ 2 := by simp only [ux, uy]; linear_combination e01
  have B : vx ^ 2 + vy ^ 2 = (r₁ + r₃) ^ 2 := by simp only [vx, vy]; linear_combination e02
  have C23 : (vx - ux) ^ 2 + (vy - uy) ^ 2 = (r₂ + r₃) ^ 2 := by
    simp only [ux, uy, vx, vy]; linear_combination e12
  rw [dist_sq2, soddyCentre_apply, soddyCentre_apply]
  set D := den r₁ r₂ r₃
  set Ns := numS r₁ r₂ r₃ p; set Nt := numT r₁ r₂ r₃ p
  fin_cases j
  · have g := gen_sq ux uy vx vy Ns Nt _ _ _ A B C23
    have c := case0 r₁ r₂ r₃ p
    simp only at c
    rw [hP, mul_zero, add_zero] at c
    have : ((C 0).1 0 + Ns / D * ((C 1).1 0 - (C 0).1 0) + Nt / D * ((C 2).1 0 - (C 0).1 0) -
        (C 0).1 0) ^ 2 + ((C 0).1 1 + Ns / D * ((C 1).1 1 - (C 0).1 1) +
        Nt / D * ((C 2).1 1 - (C 0).1 1) - (C 0).1 1) ^ 2 =
        ((Ns * ux + Nt * vx) ^ 2 + (Ns * uy + Nt * vy) ^ 2) / D ^ 2 := by
      simp only [ux, uy, vx, vy]; field_simp; ring
    simp only [Fin.zero_eta, Fin.isValue]
    rw [this, g, c]; field_simp; rfl
  · have g := gen_sq ux uy vx vy (Ns - D) Nt _ _ _ A B C23
    have c := case1 r₁ r₂ r₃ p
    simp only at c
    rw [hP, mul_zero, add_zero] at c
    have : ((C 0).1 0 + Ns / D * ((C 1).1 0 - (C 0).1 0) + Nt / D * ((C 2).1 0 - (C 0).1 0) -
        (C 1).1 0) ^ 2 + ((C 0).1 1 + Ns / D * ((C 1).1 1 - (C 0).1 1) +
        Nt / D * ((C 2).1 1 - (C 0).1 1) - (C 1).1 1) ^ 2 =
        (((Ns - D) * ux + Nt * vx) ^ 2 + ((Ns - D) * uy + Nt * vy) ^ 2) / D ^ 2 := by
      simp only [ux, uy, vx, vy]; field_simp; ring
    simp only [Fin.mk_one, Fin.isValue]
    rw [this, g, c]; field_simp; rfl
  · have g := gen_sq ux uy vx vy Ns (Nt - D) _ _ _ A B C23
    have c := case2 r₁ r₂ r₃ p
    simp only at c
    rw [hP, mul_zero, add_zero] at c
    have : ((C 0).1 0 + Ns / D * ((C 1).1 0 - (C 0).1 0) + Nt / D * ((C 2).1 0 - (C 0).1 0) -
        (C 2).1 0) ^ 2 + ((C 0).1 1 + Ns / D * ((C 1).1 1 - (C 0).1 1) +
        Nt / D * ((C 2).1 1 - (C 0).1 1) - (C 2).1 1) ^ 2 =
        ((Ns * ux + (Nt - D) * vx) ^ 2 + (Ns * uy + (Nt - D) * vy) ^ 2) / D ^ 2 := by
      simp only [ux, uy, vx, vy]; field_simp; ring
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [this, g, c]; field_simp; rfl

/-! ## Uniqueness of the centre for a given signed radius -/

/-- A point at prescribed squared distances `(rⱼ + p)²` from the three centres is unique (the
centres are affinely independent: their Gram determinant is `4 r₀ r₁ r₂ (r₀ + r₁ + r₂) > 0`). -/
theorem centre_unique (C : Fin 3 → E2 × ℝ) (hpos : ∀ i, 0 < (C i).2)
    (h01 : dist (C 0).1 (C 1).1 = (C 0).2 + (C 1).2)
    (h02 : dist (C 0).1 (C 2).1 = (C 0).2 + (C 2).2)
    (h12 : dist (C 1).1 (C 2).1 = (C 1).2 + (C 2).2)
    (p : ℝ) (x y : E2)
    (hx : ∀ j, dist x (C j).1 ^ 2 = ((C j).2 + p) ^ 2)
    (hy : ∀ j, dist y (C j).1 ^ 2 = ((C j).2 + p) ^ 2) : x = y := by
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have e01 := congrArg (· ^ 2) h01; have e02 := congrArg (· ^ 2) h02
  have e12 := congrArg (· ^ 2) h12
  simp only [dist_sq2] at e01 e02 e12
  have x0 := hx 0; have x1 := hx 1; have x2 := hx 2
  have y0 := hy 0; have y1 := hy 1; have y2 := hy 2
  simp only [dist_sq2] at x0 x1 x2 y0 y1 y2
  set ux := (C 1).1 0 - (C 0).1 0; set uy := (C 1).1 1 - (C 0).1 1
  set vx := (C 2).1 0 - (C 0).1 0; set vy := (C 2).1 1 - (C 0).1 1
  set wx := x 0 - y 0; set wy := x 1 - y 1
  have L1 : wx * ux + wy * uy = 0 := by
    simp only [wx, wy, ux, uy]; linear_combination (x1 - x0 - y1 + y0) / (-2)
  have L2 : wx * vx + wy * vy = 0 := by
    simp only [wx, wy, vx, vy]; linear_combination (x2 - x0 - y2 + y0) / (-2)
  have A : ux ^ 2 + uy ^ 2 = ((C 0).2 + (C 1).2) ^ 2 := by
    simp only [ux, uy]; linear_combination e01
  have B : vx ^ 2 + vy ^ 2 = ((C 0).2 + (C 2).2) ^ 2 := by
    simp only [vx, vy]; linear_combination e02
  have C23 : (vx - ux) ^ 2 + (vy - uy) ^ 2 = ((C 1).2 + (C 2).2) ^ 2 := by
    simp only [ux, uy, vx, vy]; linear_combination e12
  set g := (((C 0).2 + (C 1).2) ^ 2 + ((C 0).2 + (C 2).2) ^ 2 - ((C 1).2 + (C 2).2) ^ 2) / 2
  have G : ux * vx + uy * vy = g := by simp only [g]; linear_combination (A + B - C23) / 2
  have hdet : (ux * vy - uy * vx) ^ 2 =
      4 * (C 0).2 * (C 1).2 * (C 2).2 * ((C 0).2 + (C 1).2 + (C 2).2) := by
    have : ((C 0).2 + (C 1).2) ^ 2 * ((C 0).2 + (C 2).2) ^ 2 - g ^ 2 =
        4 * (C 0).2 * (C 1).2 * (C 2).2 * ((C 0).2 + (C 1).2 + (C 2).2) := by
      simp only [g]; ring
    linear_combination (vx ^ 2 + vy ^ 2) * A + ((C 0).2 + (C 1).2) ^ 2 * B
      - (ux * vx + uy * vy + g) * G + this
  have hd : ux * vy - uy * vx ≠ 0 := by
    intro h0
    have hpos' : 0 < 4 * (C 0).2 * (C 1).2 * (C 2).2 * ((C 0).2 + (C 1).2 + (C 2).2) := by
      positivity
    rw [← hdet, h0] at hpos'
    norm_num at hpos'
  have hwx : wx = 0 := by
    have : wx * (ux * vy - uy * vx) = 0 := by linear_combination vy * L1 - uy * L2
    exact (mul_eq_zero.1 this).resolve_right hd
  have hwy : wy = 0 := by
    have : wy * (ux * vy - uy * vx) = 0 := by linear_combination -vx * L1 + ux * L2
    exact (mul_eq_zero.1 this).resolve_right hd
  ext i
  fin_cases i
  · show x 0 = y 0; exact sub_eq_zero.1 hwx
  · show x 1 = y 1; exact sub_eq_zero.1 hwy

/-! ## From distances to signed tangency -/

theorem signedTangent_symm {x y : E2 × ℝ} (h : ClassicalSignedTangent x y) :
    ClassicalSignedTangent y x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h2, h1, fun ⟨a, b⟩ ↦ h3 ⟨b, a⟩, fun hh ↦ ?_, ?_⟩
  · rw [add_comm]; exact h4 hh.symm
  · rw [dist_comm, add_comm]; exact h5

/-- For positive curvatures, `2√(k₀k₁+k₁k₂+k₂k₀) < 2k₀ + k₁ + k₂`. -/
theorem sqrt_lt (k₀ k₁ k₂ : ℝ) (h₀ : 0 < k₀) (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    2 * √(k₀ * k₁ + k₁ * k₂ + k₂ * k₀) < 2 * k₀ + k₁ + k₂ := by
  have hq : 0 ≤ k₀ * k₁ + k₁ * k₂ + k₂ * k₀ := by positivity
  have hs := Real.sq_sqrt hq
  have hs0 := Real.sqrt_nonneg (k₀ * k₁ + k₁ * k₂ + k₂ * k₀)
  nlinarith [sq_nonneg (k₁ - k₂)]

/-- Positive curvatures `kᵢ = 1/rᵢ`; for either Soddy value `κ`, `κ + kᵢ > 0`, so when `κ < 0`
the enclosing circle of radius `-1/κ` is strictly larger than each given circle. -/
theorem kappa_add_pos (k₀ k₁ k₂ ε : ℝ) (h₀ : 0 < k₀) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hε : ε = 1 ∨ ε = -1) :
    let κ := k₀ + k₁ + k₂ + ε * 2 * √(k₀ * k₁ + k₁ * k₂ + k₂ * k₀)
    0 < κ + k₀ ∧ 0 < κ + k₁ ∧ 0 < κ + k₂ := by
  intro κ
  have a := sqrt_lt k₀ k₁ k₂ h₀ h₁ h₂
  have b := sqrt_lt k₁ k₂ k₀ h₁ h₂ h₀
  have c := sqrt_lt k₂ k₀ k₁ h₂ h₀ h₁
  have e1 : k₁ * k₂ + k₂ * k₀ + k₀ * k₁ = k₀ * k₁ + k₁ * k₂ + k₂ * k₀ := by ring
  have e2 : k₂ * k₀ + k₀ * k₁ + k₁ * k₂ = k₀ * k₁ + k₁ * k₂ + k₂ * k₀ := by ring
  rw [e1] at b; rw [e2] at c
  have hs0 := Real.sqrt_nonneg (k₀ * k₁ + k₁ * k₂ + k₂ * k₀)
  rcases hε with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> simp only [κ] <;> nlinarith

/-- Distance data ⇒ signed tangency between a positive circle `x` and `(c, ρ)`, given that
`x.2 + ρ < 0` whenever `ρ < 0` (the enclosing circle is strictly larger). -/
theorem signedTangent_of_sq (x : E2 × ℝ) (c : E2) (ρ : ℝ) (hx : 0 < x.2) (hρ : ρ ≠ 0)
    (hneg : ρ < 0 → x.2 + ρ < 0) (hd : dist x.1 c ^ 2 = (x.2 + ρ) ^ 2) :
    ClassicalSignedTangent x (c, ρ) := by
  refine ⟨hx.ne', hρ, fun ⟨a, _⟩ ↦ by linarith, fun hh ↦ ?_, ?_⟩
  · rcases hh with hh | hh
    · linarith
    · exact hneg hh
  · show dist x.1 c = |x.2 + ρ|
    rw [← Real.sqrt_sq_eq_abs, ← hd, Real.sqrt_sq dist_nonneg]

/-! ## Main theorem: existence (classical I5b, verbatim) -/

/-- Unpack the pairwise tangencies of three positive circles. -/
theorem pair_dist (C : Fin 3 → E2 × ℝ) (h : ClassicalMutuallyTangent C)
    (hpos : ∀ i, 0 < (C i).2) (i j : Fin 3) (hij : i ≠ j) :
    dist (C i).1 (C j).1 = (C i).2 + (C j).2 := by
  have := (h.2 i j hij).2.2.2.2
  rw [this, abs_of_pos (by linarith [hpos i, hpos j])]

/-- **The Soddy circle for a given Descartes root.** For three pairwise externally tangent
circles with positive radii and either sign `ε`, if `κ ≠ 0` the circle
`(soddyCentre C (1/κ), 1/κ)` completes a Descartes configuration. -/
theorem soddy_circle (C : Fin 3 → E2 × ℝ) (h : ClassicalMutuallyTangent C)
    (hpos : ∀ i, 0 < (C i).2) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    let k := fun i => 1 / (C i).2
    let κ := k 0 + k 1 + k 2 + ε * 2 * Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0)
    κ ≠ 0 → ClassicalMutuallyTangent ![C 0, C 1, C 2, (soddyCentre C (1 / κ), 1 / κ)] := by
  intro k κ hκ
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have k0 : 0 < k 0 := by simp only [k]; positivity
  have k1 : 0 < k 1 := by simp only [k]; positivity
  have k2 : 0 < k 2 := by simp only [k]; positivity
  have hρ : (1 / κ) ≠ 0 := one_div_ne_zero hκ
  -- `κ` is a Descartes root (`descartes_solve`), hence `polyP … (1/κ) = 0`
  have hD : Inversion.descartesForm (k 0) (k 1) (k 2) κ = 0 := by
    rw [Inversion.descartes_solve]
    refine ⟨by positivity, ?_⟩
    rcases hε with rfl | rfl
    · left; simp only [κ]; ring
    · right; simp only [κ]; ring
  have hP : polyP (C 0).2 (C 1).2 (C 2).2 (1 / κ) = 0 := by
    rw [polyP_eq _ _ _ _ p0.ne' p1.ne' p2.ne' hρ, one_div_one_div]
    simp only [k] at hD
    rw [hD, mul_zero]
  have hd := soddy_dist_sq C hpos (pair_dist C h hpos 0 1 (by decide))
    (pair_dist C h hpos 0 2 (by decide)) (pair_dist C h hpos 1 2 (by decide)) (1 / κ) hP
  obtain ⟨a0, a1, a2⟩ := kappa_add_pos (k 0) (k 1) (k 2) ε k0 k1 k2 hε
  have hneg : ∀ j : Fin 3, 1 / κ < 0 → (C j).2 + 1 / κ < 0 := by
    intro j hn
    have hκn : κ < 0 := by rwa [one_div_neg] at hn
    have aj : 0 < κ + 1 / (C j).2 := by
      fin_cases j
      · exact a0
      · exact a1
      · exact a2
    have pj := hpos j
    have : (C j).2 * κ + 1 > 0 := by
      have := mul_pos pj aj
      rwa [mul_add, mul_one_div_cancel pj.ne'] at this
    have e : (C j).2 + 1 / κ = ((C j).2 * κ + 1) / κ := by field_simp
    rw [e]; exact div_neg_of_pos_of_neg this hκn
  have T : ∀ j : Fin 3, ClassicalSignedTangent (C j) (soddyCentre C (1 / κ), 1 / κ) := by
    intro j
    refine signedTangent_of_sq (C j) _ _ (hpos j) hρ (hneg j) ?_
    rw [dist_comm]; exact hd j
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact p0.ne'
    · exact p1.ne'
    · exact p2.ne'
    · exact hρ
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact h.2 _ _ (by decide)
      | exact T _
      | exact signedTangent_symm (T _)

/-- **Classical I5b (L15), verbatim statement, proved.** -/
theorem classical_I5b (C : Fin 3 → E2 × ℝ) (h : ClassicalMutuallyTangent C)
    (hpos : ∀ i, 0 < (C i).2) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    let k := fun i => 1 / (C i).2
    let κ := k 0 + k 1 + k 2 + ε * 2 * Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0)
    κ ≠ 0 → ∃ c : E2, ClassicalMutuallyTangent ![C 0, C 1, C 2, (c, 1 / κ)] := by
  intro k κ hκ
  exact ⟨_, soddy_circle C h hpos ε hε hκ⟩

/-! ## Classification: these are the only ones ("exactly two") -/

/-- The standard isometry `E2 ≃ ℂ` (used to apply `Inversion.descartes`, stated in `ℂ`). -/
abbrev e : E2 ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

theorem tangent_sq' {x y : E2 × ℝ} (h : ClassicalSignedTangent x y) :
    dist (e x.1) (e y.1) ^ 2 = (x.2 + y.2) ^ 2 := by
  rw [LinearIsometryEquiv.dist_map, h.2.2.2.2, sq_abs]

/-- **Every circle tangent to the triple is one of the two Soddy circles.** If
`C 0, C 1, C 2, (c, ρ)` is a Descartes configuration (the three given circles positive), then
`1/ρ = κ₊` or `1/ρ = κ₋` (the two roots, via `Inversion.descartes` + `descartes_solve`) and
`c = soddyCentre C ρ`. -/
theorem soddy_classify (C : Fin 3 → E2 × ℝ) (hpos : ∀ i, 0 < (C i).2) (c : E2) (ρ : ℝ)
    (hw : ClassicalMutuallyTangent ![C 0, C 1, C 2, (c, ρ)]) :
    let k := fun i => 1 / (C i).2
    let s := Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0)
    (1 / ρ = k 0 + k 1 + k 2 + 2 * s ∨ 1 / ρ = k 0 + k 1 + k 2 - 2 * s) ∧
      c = soddyCentre C ρ := by
  intro k s
  have T : ∀ i j : Fin 4, i ≠ j →
      ClassicalSignedTangent (![C 0, C 1, C 2, (c, ρ)] i) (![C 0, C 1, C 2, (c, ρ)] j) := hw.2
  have t01 := T 0 1 (by decide); have t02 := T 0 2 (by decide); have t03 := T 0 3 (by decide)
  have t12 := T 1 2 (by decide); have t13 := T 1 3 (by decide); have t23 := T 2 3 (by decide)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at t01 t02 t03 t12 t13 t23
  have hρ : ρ ≠ 0 := t03.2.1
  have hdesc := Inversion.descartes (hpos 0).ne' (hpos 1).ne' (hpos 2).ne' hρ
    (tangent_sq' t01) (tangent_sq' t02) (tangent_sq' t03) (tangent_sq' t12)
    (tangent_sq' t13) (tangent_sq' t23)
  have hF : Inversion.descartesForm (k 0) (k 1) (k 2) (1 / ρ) = 0 := by
    unfold Inversion.descartesForm; simp only [k]; linear_combination hdesc
  refine ⟨((Inversion.descartes_solve _ _ _ _).1 hF).2, ?_⟩
  -- centre: same distances as `soddyCentre C ρ`
  have pd : ∀ (i j : Fin 3), i ≠ j → dist (C i).1 (C j).1 = (C i).2 + (C j).2 := by
    intro i j hij
    have hm : ClassicalMutuallyTangent C := by
      refine ⟨fun i ↦ (hpos i).ne', fun i j hij ↦ ?_⟩
      have := T (Fin.castSucc i) (Fin.castSucc j) (by simpa [Fin.ext_iff] using hij)
      fin_cases i <;> fin_cases j <;> simpa using this
    exact pair_dist C hm hpos i j hij
  have hP : polyP (C 0).2 (C 1).2 (C 2).2 ρ = 0 := by
    rw [polyP_eq _ _ _ _ (hpos 0).ne' (hpos 1).ne' (hpos 2).ne' hρ]
    simp only [k] at hF; rw [hF, mul_zero]
  have sq_of : ∀ {x : E2 × ℝ}, ClassicalSignedTangent x (c, ρ) →
      dist c x.1 ^ 2 = (x.2 + ρ) ^ 2 := by
    intro x hx
    have := hx.2.2.2.2
    rw [dist_comm] at this
    rw [this, sq_abs]
  have hx : ∀ j : Fin 3, dist c (C j).1 ^ 2 = ((C j).2 + ρ) ^ 2 := by
    intro j
    match j with
    | 0 => exact sq_of t03
    | 1 => exact sq_of t13
    | 2 => exact sq_of t23
  exact centre_unique C hpos (pd 0 1 (by decide)) (pd 0 2 (by decide)) (pd 1 2 (by decide)) ρ
    c _ hx (soddy_dist_sq C hpos (pd 0 1 (by decide)) (pd 0 2 (by decide)) (pd 1 2 (by decide))
      ρ hP)

/-- **Exactly two (or one plus a line).** For three pairwise externally tangent circles with
positive radii, with `κ± = k₀+k₁+k₂ ± 2√(k₀k₁+k₁k₂+k₂k₀)`:
* `κ₊ > 0` and `κ₊ ≠ κ₋`;
* a signed circle `(c, ρ)` completes a Descartes configuration **iff** it is the inner Soddy
  circle `(soddyCentre C (1/κ₊), 1/κ₊)` or (when `κ₋ ≠ 0`) the outer one
  `(soddyCentre C (1/κ₋), 1/κ₋)`.
When `κ₋ = 0` the outer "circle" is a line, which is not a signed circle here, so there is
exactly one circle. -/
theorem soddy_exactly_two (C : Fin 3 → E2 × ℝ) (h : ClassicalMutuallyTangent C)
    (hpos : ∀ i, 0 < (C i).2) :
    let k := fun i => 1 / (C i).2
    let κp := k 0 + k 1 + k 2 + 2 * Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0)
    let κm := k 0 + k 1 + k 2 - 2 * Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0)
    0 < κp ∧ κp ≠ κm ∧
    ∀ (c : E2) (ρ : ℝ), ClassicalMutuallyTangent ![C 0, C 1, C 2, (c, ρ)] ↔
      ((c, ρ) = (soddyCentre C (1 / κp), 1 / κp) ∨
        (κm ≠ 0 ∧ (c, ρ) = (soddyCentre C (1 / κm), 1 / κm))) := by
  intro k κp κm
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have k0 : 0 < k 0 := by simp only [k]; positivity
  have k1 : 0 < k 1 := by simp only [k]; positivity
  have k2 : 0 < k 2 := by simp only [k]; positivity
  have hsq : 0 < Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0) := Real.sqrt_pos.2 (by positivity)
  have hp : 0 < κp := by simp only [κp]; positivity
  refine ⟨hp, by simp only [κp, κm]; intro hh; linarith, fun c ρ ↦ ⟨fun hw ↦ ?_, ?_⟩⟩
  · obtain ⟨hk, hc⟩ := soddy_classify C hpos c ρ hw
    have hρ : ρ ≠ 0 := hw.1 3
    rcases hk with hk | hk
    · left
      have hk' : 1 / ρ = κp := hk
      have : ρ = 1 / κp := by rw [← hk', one_div_one_div]
      subst this; rw [hc]
    · right
      have hk' : 1 / ρ = κm := hk
      have : ρ = 1 / κm := by rw [← hk', one_div_one_div]
      subst this
      refine ⟨fun h0 ↦ hρ (by simp [h0]), by rw [hc]⟩
  · have ep : k 0 + k 1 + k 2 + 1 * 2 * Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0) = κp := by
      simp only [κp]; ring
    have em : k 0 + k 1 + k 2 + -1 * 2 * Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0) = κm := by
      simp only [κm]; ring
    have Hp := soddy_circle C h hpos 1 (Or.inl rfl)
    have Hm := soddy_circle C h hpos (-1) (Or.inr rfl)
    simp only [] at Hp Hm
    rw [ep] at Hp; rw [em] at Hm
    rintro (hh | ⟨hm, hh⟩)
    · rw [hh]; exact Hp hp.ne'
    · rw [hh]; exact Hm hm

end SoddyExists
