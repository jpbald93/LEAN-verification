/-
  L13 blind re-formalisation of the Paper K draft (paperk_frozen_v2.tex).
  Writer had access to the .tex only. Every statement below is an independent reading.
  All statements are stated as `Prop`-valued definitions and `#check`ed (no proofs are claimed):
  no Mathlib build was available on the writer's machine, so no proof could be checked.
  Invented vocabulary (not in Mathlib): `lie`, `ctr`, `chart`, `lag`, `gram`, `cof`, `det4`,
  `lie3`, `ctr3`, `chart3`, `LV`, `lieN`, `ctrN`, `chartN`, `sqd`.
-/
import Mathlib

namespace L13Blind

open Matrix

noncomputable section

/-! ## Vocabulary at n = 2: slots (r, a, b, v, w) = indices 0..4 -/

/-- The paper's form B(X,Y) = r r' - c·c' - v w' - w v' (negative of the source's form). -/
def lie (X Y : Fin 5 → ℝ) : ℝ :=
  X 0 * Y 0 - X 1 * Y 1 - X 2 * Y 2 - X 3 * Y 4 - X 4 * Y 3

/-- Affine centre (P₁/P₃, P₂/P₃). -/
def ctr (P : Fin 5 → ℝ) : Fin 2 → ℝ := ![P 1 / P 3, P 2 / P 3]

/-- Affine chart: circle of signed radius r, centre (a,b). -/
def chart (r a b : ℝ) : Fin 5 → ℝ := ![r, a, b, 1, (r ^ 2 - a ^ 2 - b ^ 2) / 2]

/-- Squared Euclidean distance in `Fin m → ℝ`, written out. -/
def sqd {m : ℕ} (x y : Fin m → ℝ) : ℝ := ∑ k, (x k - y k) ^ 2

/-- Laguerre power of point/radius (p, ρ) with respect to the cycle with centre c, radius r. -/
def lag {m : ℕ} (p : Fin m → ℝ) (ρ : ℝ) (c : Fin m → ℝ) (r : ℝ) : ℝ := sqd p c - (ρ - r) ^ 2

/-- An explicit Gram matrix of `lie`. -/
def gram : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
     0, -1, 0, 0, 0;
     0, 0, -1, 0, 0;
     0, 0, 0, 0, -1;
     0, 0, 0, -1, 0]

/-- Signed maximal minors of a 4×5 matrix: (-1)^k det (M without column k). -/
def cof (M : Matrix (Fin 4) (Fin 5) ℝ) : Fin 5 → ℝ :=
  fun k => (-1 : ℝ) ^ (k : ℕ) * (M.submatrix id k.succAbove).det

/-- det of the 4×4 matrix whose columns are c₁ c₂ c₃ c₄. -/
def det4 (c₁ c₂ c₃ c₄ : Fin 4 → ℝ) : ℝ :=
  (Matrix.of fun i j => ![c₁ i, c₂ i, c₃ i, c₄ i] j).det

/-! ## §3 encoding claims (n = 2) -/

-- UNPROVED:
def s01_null_iff : Prop :=
  ∀ X : Fin 5 → ℝ, lie X X = 0 ↔ X 0 ^ 2 - X 1 ^ 2 - X 2 ^ 2 = 2 * X 3 * X 4
#check s01_null_iff

-- UNPROVED:
def s02_gram : Prop :=
  ∃ G : Matrix (Fin 5) (Fin 5) ℝ, G.IsSymm ∧ G * G = 1 ∧ ∀ X Y, lie X Y = X ⬝ᵥ (G *ᵥ Y)
#check s02_gram

/-- Signature reading of the abstract: the SOURCE form (= -lie) has 3 = n+1 positive and 2 negative
squares. -/
-- UNPROVED:
def s03_signature : Prop :=
  ∃ e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ), ∀ X,
    -lie X X = e X 0 ^ 2 + e X 1 ^ 2 + e X 2 ^ 2 - e X 3 ^ 2 - e X 4 ^ 2
#check s03_signature

-- UNPROVED:
def s04_tangency : Prop :=
  ∀ X Y : Fin 5 → ℝ, lie X X = 0 → lie Y Y = 0 →
    -2 * X 3 * Y 3 * lie X Y =
      (X 0 * Y 3 - Y 0 * X 3) ^ 2 - ((X 1 * Y 3 - Y 1 * X 3) ^ 2 + (X 2 * Y 3 - Y 2 * X 3) ^ 2)
#check s04_tangency

/-- The polynomial defect of the tangency identity (LHS − RHS), no null hypotheses. -/
-- UNPROVED:
def s05_tangency_defect : Prop :=
  ∀ X Y : Fin 5 → ℝ,
    -2 * X 3 * Y 3 * lie X Y -
      ((X 0 * Y 3 - Y 0 * X 3) ^ 2 - ((X 1 * Y 3 - Y 1 * X 3) ^ 2 + (X 2 * Y 3 - Y 2 * X 3) ^ 2))
    = -(Y 3 ^ 2 * lie X X + X 3 ^ 2 * lie Y Y)
#check s05_tangency_defect

-- UNPROVED:
def s06_tangency_not_identity : Prop :=
  ¬ ∀ X Y : Fin 5 → ℝ,
    -2 * X 3 * Y 3 * lie X Y =
      (X 0 * Y 3 - Y 0 * X 3) ^ 2 - ((X 1 * Y 3 - Y 1 * X 3) ^ 2 + (X 2 * Y 3 - Y 2 * X 3) ^ 2)
#check s06_tangency_not_identity

/-- Oriented tangency, v = v' = 1 (affine chart). -/
-- UNPROVED:
def s07_tangency_chart : Prop :=
  ∀ r a b r' a' b' : ℝ,
    2 * lie (chart r a b) (chart r' a' b') = (a - a') ^ 2 + (b - b') ^ 2 - (r - r') ^ 2
#check s07_tangency_chart

/-- Iff form for non-zero v-slots (reading: radius r/v, centre c/v). -/
-- UNPROVED:
def s08_tangent_iff : Prop :=
  ∀ X Y : Fin 5 → ℝ, lie X X = 0 → lie Y Y = 0 → X 3 ≠ 0 → Y 3 ≠ 0 →
    (lie X Y = 0 ↔ sqd (ctr X) (ctr Y) = (X 0 / X 3 - Y 0 / Y 3) ^ 2)
#check s08_tangent_iff

-- UNPROVED:
def s09_cofactor_null : Prop :=
  ∀ M : Matrix (Fin 4) (Fin 5) ℝ, M *ᵥ cof M = 0
#check s09_cofactor_null

-- UNPROVED:
def s10_cofactor_orth : Prop :=
  ∀ (M : Matrix (Fin 4) (Fin 5) ℝ) (i : Fin 4), lie (gram *ᵥ cof M) (M i) = 0
#check s10_cofactor_orth

/-! ## Theorem 1 (collinearity, n = 2) -/

-- UNPROVED:
def s11_thm1 : Prop :=
  ∀ (X : Fin 4 → Fin 5 → ℝ) (A A' P : Fin 5 → ℝ) (i : Fin 4),
    (∀ Y : Fin 5 → ℝ, (∀ j, j ≠ i → lie Y (X j) = 0) →
        Y ∈ Submodule.span ℝ ({A, A'} : Set (Fin 5 → ℝ))) →
    (∀ j, lie P (X j) = 0) →
    A 3 ≠ 0 → A' 3 ≠ 0 → P 3 ≠ 0 →
    P ∈ Submodule.span ℝ ({A, A'} : Set (Fin 5 → ℝ)) ∧
    (∃ s t : ℝ, s + t = 1 ∧ ctr P = s • ctr A + t • ctr A') ∧
    Collinear ℝ ({ctr P, ctr A, ctr A'} : Set (Fin 2 → ℝ))
#check s11_thm1

/-- Cofactor variant: P := gram · cof M, rows of M the four cycles. -/
-- UNPROVED:
def s12_thm1_cofactor : Prop :=
  ∀ (M : Matrix (Fin 4) (Fin 5) ℝ) (A A' : Fin 5 → ℝ) (i : Fin 4),
    (∀ Y : Fin 5 → ℝ, (∀ j, j ≠ i → lie Y (M j) = 0) →
        Y ∈ Submodule.span ℝ ({A, A'} : Set (Fin 5 → ℝ))) →
    A 3 ≠ 0 → A' 3 ≠ 0 → (gram *ᵥ cof M) 3 ≠ 0 →
    (gram *ᵥ cof M) ∈ Submodule.span ℝ ({A, A'} : Set (Fin 5 → ℝ)) ∧
    ∃ s t : ℝ, s + t = 1 ∧ ctr (gram *ᵥ cof M) = s • ctr A + t • ctr A'
#check s12_thm1_cofactor

/-! ## General n vocabulary: a Lie vector is (r, c, v, w) ∈ ℝ × ℝⁿ × ℝ × ℝ -/

abbrev LV (n : ℕ) := ℝ × (Fin n → ℝ) × ℝ × ℝ

def lieN {n : ℕ} (X Y : LV n) : ℝ :=
  X.1 * Y.1 - ∑ k, X.2.1 k * Y.2.1 k - X.2.2.1 * Y.2.2.2 - X.2.2.2 * Y.2.2.1

def ctrN {n : ℕ} (P : LV n) : Fin n → ℝ := fun k => P.2.1 k / P.2.2.1

def chartN {n : ℕ} (r : ℝ) (c : Fin n → ℝ) : LV n :=
  (r, c, 1, (r ^ 2 - ∑ k, c k ^ 2) / 2)

-- UNPROVED:
def s13_null_iff_N : Prop :=
  ∀ (n : ℕ) (X : LV n), lieN X X = 0 ↔ X.1 ^ 2 - ∑ k, X.2.1 k ^ 2 = 2 * X.2.2.1 * X.2.2.2
#check s13_null_iff_N

-- UNPROVED:
def s14_tangency_N : Prop :=
  ∀ (n : ℕ) (X Y : LV n), lieN X X = 0 → lieN Y Y = 0 →
    -2 * X.2.2.1 * Y.2.2.1 * lieN X Y =
      (X.1 * Y.2.2.1 - Y.1 * X.2.2.1) ^ 2 - ∑ k, (X.2.1 k * Y.2.2.1 - Y.2.1 k * X.2.2.1) ^ 2
#check s14_tangency_N

-- UNPROVED:
def s15_tangent_iff_N : Prop :=
  ∀ (n : ℕ) (X Y : LV n), lieN X X = 0 → lieN Y Y = 0 → X.2.2.1 ≠ 0 → Y.2.2.1 ≠ 0 →
    (lieN X Y = 0 ↔ sqd (ctrN X) (ctrN Y) = (X.1 / X.2.2.1 - Y.1 / Y.2.2.1) ^ 2)
#check s15_tangent_iff_N

/-- Theorem 1 at general n: n+2 vectors, conclusion `Collinear` in ℝⁿ. -/
-- UNPROVED:
def s16_thm1_N : Prop :=
  ∀ (n : ℕ) (X : Fin (n + 2) → LV n) (A A' P : LV n) (i : Fin (n + 2)),
    (∀ Y : LV n, (∀ j, j ≠ i → lieN Y (X j) = 0) →
        Y ∈ Submodule.span ℝ ({A, A'} : Set (LV n))) →
    (∀ j, lieN P (X j) = 0) →
    A.2.2.1 ≠ 0 → A'.2.2.1 ≠ 0 → P.2.2.1 ≠ 0 →
    Collinear ℝ ({ctrN P, ctrN A, ctrN A'} : Set (Fin n → ℝ))
#check s16_thm1_N

/-! ## Theorem 2 (explicit equal-power point and radius, n = 2) -/

-- UNPROVED:
def s17_thm2 : Prop :=
  ∀ r a b : Fin 4 → ℝ,
    let s : Fin 4 → ℝ := fun i => a i ^ 2 + b i ^ 2 - r i ^ 2
    let one : Fin 4 → ℝ := fun _ => 1
    let D := det4 r a b one
    let p : Fin 2 → ℝ := ![-det4 r b s one / (2 * D), det4 r a s one / (2 * D)]
    let ρ := -det4 a b s one / (2 * D)
    D ≠ 0 →
    ∀ i, lag p ρ ![a i, b i] (r i) = sqd p 0 - ρ ^ 2 + det4 r a b s / D
#check s17_thm2

-- UNPROVED:
def s18_thm2_indep : Prop :=
  ∀ r a b : Fin 4 → ℝ,
    let s : Fin 4 → ℝ := fun i => a i ^ 2 + b i ^ 2 - r i ^ 2
    let one : Fin 4 → ℝ := fun _ => 1
    let D := det4 r a b one
    let p : Fin 2 → ℝ := ![-det4 r b s one / (2 * D), det4 r a s one / (2 * D)]
    let ρ := -det4 a b s one / (2 * D)
    D ≠ 0 → ∀ i j, lag p ρ ![a i, b i] (r i) = lag p ρ ![a j, b j] (r j)
#check s18_thm2_indep

/-- §5 prose claim (stated by the paper as hand-derived, not formalised): the corrected vector
P = (q₀, −q₁, −q₂, 2q₃, −q₄), q = cof of the rows (r,a,b,s,1), is orthogonal to the four chart
circles, has v-slot −2D, centre p and radius P₀/P₃ = ρ. -/
-- UNPROVED:
def s19_thm2_link : Prop :=
  ∀ r a b : Fin 4 → ℝ,
    let s : Fin 4 → ℝ := fun i => a i ^ 2 + b i ^ 2 - r i ^ 2
    let one : Fin 4 → ℝ := fun _ => 1
    let D := det4 r a b one
    let M : Matrix (Fin 4) (Fin 5) ℝ := Matrix.of fun i => ![r i, a i, b i, s i, 1]
    let q := cof M
    let P : Fin 5 → ℝ := ![q 0, -q 1, -q 2, 2 * q 3, -q 4]
    D ≠ 0 →
    (∀ i, lie P (chart (r i) (a i) (b i)) = 0) ∧ P 3 = -2 * D ∧
    ctr P = ![-det4 r b s one / (2 * D), det4 r a s one / (2 * D)] ∧
    P 0 / P 3 = -det4 a b s one / (2 * D)
#check s19_thm2_link

/-- §5 prose claim: the naive vector gram · cof of the rows (r,a,b,s,1) does NOT in general have
centre p. -/
-- UNPROVED:
def s20_thm2_naive_wrong : Prop :=
  ∃ r a b : Fin 4 → ℝ,
    let s : Fin 4 → ℝ := fun i => a i ^ 2 + b i ^ 2 - r i ^ 2
    let one : Fin 4 → ℝ := fun _ => 1
    let D := det4 r a b one
    let M : Matrix (Fin 4) (Fin 5) ℝ := Matrix.of fun i => ![r i, a i, b i, s i, 1]
    D ≠ 0 ∧ ctr (gram *ᵥ cof M) ≠ ![-det4 r b s one / (2 * D), det4 r a s one / (2 * D)]
#check s20_thm2_naive_wrong

/-! ## Theorem 3 (equal power) -/

/-- Reading: "normalised cycle" = null vector with v-slot 1. -/
-- UNPROVED:
def s21_thm3 : Prop :=
  ∀ P Y : Fin 5 → ℝ, P 3 ≠ 0 → Y 3 = 1 → lie Y Y = 0 → lie P Y = 0 →
    lag (ctr P) (P 0 / P 3) ![Y 1, Y 2] (Y 0) = -lie P P / P 3 ^ 2
#check s21_thm3

-- UNPROVED:
def s22_thm3_family : Prop :=
  ∀ (ι : Type) (P : Fin 5 → ℝ) (Y : ι → Fin 5 → ℝ), P 3 ≠ 0 →
    (∀ i, Y i 3 = 1) → (∀ i, lie (Y i) (Y i) = 0) → (∀ i, lie P (Y i) = 0) →
    ∀ i j, lag (ctr P) (P 0 / P 3) ![Y i 1, Y i 2] (Y i 0) =
           lag (ctr P) (P 0 / P 3) ![Y j 1, Y j 2] (Y j 0)
#check s22_thm3_family

/-- Coordinate form at n = 2, chart circles: common value |p|² − ρ² + 2P₄/P₃. -/
-- UNPROVED:
def s23_thm3_coord : Prop :=
  ∀ (P : Fin 5 → ℝ) (r a b : ℝ), P 3 ≠ 0 → lie P (chart r a b) = 0 →
    lag (ctr P) (P 0 / P 3) ![a, b] r = sqd (ctr P) 0 - (P 0 / P 3) ^ 2 + 2 * P 4 / P 3
#check s23_thm3_coord

/-- General n form. -/
-- UNPROVED:
def s24_thm3_N : Prop :=
  ∀ (n : ℕ) (P : LV n) (r : ℝ) (c : Fin n → ℝ), P.2.2.1 ≠ 0 → lieN P (chartN r c) = 0 →
    lag (ctrN P) (P.1 / P.2.2.1) c r = -lieN P P / P.2.2.1 ^ 2
#check s24_thm3_N

/-! ## §6 degenerate configurations, n = 2 -/

/-- Three circles of common radius r₀, non-collinear centres: the centre of any orthogonal P with
P₃ ≠ 0 is the (unique) equidistant point. -/
-- UNPROVED:
def s25_equal_circles : Prop :=
  ∀ (r₀ : ℝ) (c : Fin 3 → Fin 2 → ℝ) (P : Fin 5 → ℝ),
    ¬ Collinear ℝ (Set.range c) →
    (∀ i, lie P (chart r₀ (c i 0) (c i 1)) = 0) → P 3 ≠ 0 →
    (∀ i j, sqd (ctr P) (c i) = sqd (ctr P) (c j)) ∧
    ∀ x : Fin 2 → ℝ, (∀ i j, sqd x (c i) = sqd x (c j)) → x = ctr P
#check s25_equal_circles

/-- Theorem 4, read literally: P is a cycle (null). -/
-- UNPROVED:
def s26_thm4 : Prop :=
  ∀ P : Fin 5 → ℝ, lie P P = 0 → P 3 ≠ 0 →
    lie P (chart 1 0 0) = 0 → lie P (chart 1 2 0) = 0 → lie P (chart 1 1 (Real.sqrt 3)) = 0 →
    ctr P = ![1, Real.sqrt 3 / 3]
#check s26_thm4

/-- Theorem 4 without the null hypothesis on P (the prose's §6 discussion suggests it is unused). -/
-- UNPROVED:
def s27_thm4_no_null : Prop :=
  ∀ P : Fin 5 → ℝ, P 3 ≠ 0 →
    lie P (chart 1 0 0) = 0 → lie P (chart 1 2 0) = 0 → lie P (chart 1 1 (Real.sqrt 3)) = 0 →
    ctr P = ![1, Real.sqrt 3 / 3]
#check s27_thm4_no_null

/-- The four square circles. -/
def sq : Fin 4 → Fin 5 → ℝ := ![chart 1 1 1, chart 1 1 (-1), chart 1 (-1) 1, chart 1 (-1) (-1)]

/-- Theorem 5(a): for each omitted index k, the affine (chart) cycles orthogonal to the other three
are exactly the origin-centred ones with radius 1 ± √2. -/
-- UNPROVED:
def s28_thm5_apollonius : Prop :=
  ∀ (k : Fin 4) (r a b : ℝ), (∀ j, j ≠ k → lie (chart r a b) (sq j) = 0) ↔
    (a = 0 ∧ b = 0 ∧ (r = 1 + Real.sqrt 2 ∨ r = 1 - Real.sqrt 2))
#check s28_thm5_apollonius

-- UNPROVED:
def s29_thm5_distinct : Prop := (1 + Real.sqrt 2 : ℝ) ≠ 1 - Real.sqrt 2
#check s29_thm5_distinct

def sqU : Fin 5 → ℝ := ![1, 0, 0, 0, 1]
def sqW : Fin 5 → ℝ := ![0, 0, 0, 1, 1 / 2]

-- UNPROVED:
def s30_thm5_null_space : Prop :=
  (∀ Y : Fin 5 → ℝ, (∀ j, lie Y (sq j) = 0) ↔
      Y ∈ Submodule.span ℝ ({sqU, sqW} : Set (Fin 5 → ℝ))) ∧
  LinearIndependent ℝ ![sqU, sqW] ∧
  Module.finrank ℝ (Submodule.span ℝ ({sqU, sqW} : Set (Fin 5 → ℝ))) = 2
#check s30_thm5_null_space

-- UNPROVED:
def s31_thm5_not_null : Prop := lie sqU sqU ≠ 0 ∧ lie sqW sqW ≠ 0
#check s31_thm5_not_null

-- UNPROVED:
def s32_thm5_centre : Prop :=
  ∀ P : Fin 5 → ℝ, (∀ j, lie P (sq j) = 0) → P 3 ≠ 0 → ctr P = 0
#check s32_thm5_centre

/-! ## §6 regular tetrahedron in ℝ³: slots (r, x, y, z, v, w) -/

def lie3 (X Y : Fin 6 → ℝ) : ℝ :=
  X 0 * Y 0 - X 1 * Y 1 - X 2 * Y 2 - X 3 * Y 3 - X 4 * Y 5 - X 5 * Y 4

def ctr3 (P : Fin 6 → ℝ) : Fin 3 → ℝ := ![P 1 / P 4, P 2 / P 4, P 3 / P 4]

def chart3 (r : ℝ) (c : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![r, c 0, c 1, c 2, 1, (r ^ 2 - c 0 ^ 2 - c 1 ^ 2 - c 2 ^ 2) / 2]

def tet : Fin 4 → Fin 3 → ℝ := ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

/-- Reading: P a cycle (null), fifth sphere an arbitrary chart sphere. -/
-- UNPROVED:
def s33_tetra_centre : Prop :=
  ∀ (P : Fin 6 → ℝ) (r₅ : ℝ) (c₅ : Fin 3 → ℝ), lie3 P P = 0 →
    (∀ i, lie3 P (chart3 1 (tet i)) = 0) → lie3 P (chart3 r₅ c₅) = 0 → P 4 ≠ 0 →
    ctr3 P = 0
#check s33_tetra_centre

-- UNPROVED:
def s34_tetra_equidistant : Prop :=
  ∀ x : Fin 3 → ℝ, (∀ i j, sqd x (tet i) = sqd x (tet j)) → x = 0 ∧ sqd x (tet 0) = 3
#check s34_tetra_equidistant

-- UNPROVED:
def s35_tetra_apollonius : Prop :=
  ∀ i, lie3 (chart3 (Real.sqrt 3 + 1) 0) (chart3 1 (tet i)) = 0 ∧
       lie3 (chart3 (1 - Real.sqrt 3) 0) (chart3 1 (tet i)) = 0
#check s35_tetra_apollonius

/-- Scaled family, reading: same centres, common radius s > 0. -/
-- UNPROVED:
def s36_tetra_scaled : Prop :=
  ∀ (s : ℝ) (P : Fin 6 → ℝ) (r₅ : ℝ) (c₅ : Fin 3 → ℝ), 0 < s → lie3 P P = 0 →
    (∀ i, lie3 P (chart3 s (tet i)) = 0) → lie3 P (chart3 r₅ c₅) = 0 → P 4 ≠ 0 →
    ctr3 P = 0
#check s36_tetra_scaled

-- UNPROVED:
def s37_tetra_affind : Prop := AffineIndependent ℝ tet
#check s37_tetra_affind

/-- §9 claim: the tetrahedral unit spheres are 2√2 apart (so not mutually tangent). -/
-- UNPROVED:
def s38_tetra_apart : Prop := ∀ i j, i ≠ j → sqd (tet i) (tet j) = 8
#check s38_tetra_apart

/-! ## §6 regular simplex, general n -/

/-- Reading: no extra (n+2)-th cycle hypothesis (the prose says the paper's version carries one,
unused); "P a vector", not necessarily null. -/
-- UNPROVED:
def s39_simplex : Prop :=
  ∀ (n : ℕ) (c : Fin (n + 1) → Fin n → ℝ) (P : LV n),
    AffineIndependent ℝ c → ∑ i, c i = 0 → (∀ i j, sqd (c i) 0 = sqd (c j) 0) →
    (∀ i, lieN P (chartN 1 (c i)) = 0) → P.2.2.1 ≠ 0 →
    ctrN P = 0
#check s39_simplex

/-- Circumradius reading: common squared distance equals the squared circumradius of the simplex
(Mathlib's `Affine.Simplex.circumradius` in Euclidean space). -/
-- UNPROVED:
def s40_simplex_circumradius : Prop :=
  ∀ (n : ℕ) (c : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) (P : LV n)
    (h : AffineIndependent ℝ c),
    ∑ i, c i = 0 → (∀ i j, ‖c i‖ = ‖c j‖) →
    (∀ i, lieN P (chartN 1 (fun k => c i k)) = 0) → P.2.2.1 ≠ 0 →
    ∀ i, sqd (ctrN P) (fun k => c i k) = (⟨c, h⟩ : Affine.Simplex ℝ _ n).circumradius ^ 2
#check s40_simplex_circumradius

/-- Equidistance at general n, any unit spheres (no affine-independence needed in this reading). -/
-- UNPROVED:
def s41_dist_const : Prop :=
  ∀ (n : ℕ) (m : ℕ) (c : Fin m → Fin n → ℝ) (P : LV n),
    (∀ i, lieN P (chartN 1 (c i)) = 0) → P.2.2.1 ≠ 0 →
    ∀ i j, sqd (ctrN P) (c i) = sqd (ctrN P) (c j)
#check s41_dist_const

/-! ## Theorem 6 (centroid reading is false) -/

/-- The universal centroid statement, refuted: some n has a counterexample. -/
-- UNPROVED:
def s42_thm6 : Prop :=
  ¬ ∀ (n : ℕ) (c : Fin (n + 1) → Fin n → ℝ) (X₀ : LV n) (P : LV n),
      AffineIndependent ℝ c → ∑ i, c i = 0 →
      (∀ i, lieN P (chartN 1 (c i)) = 0) → lieN P X₀ = 0 → P.2.2.1 ≠ 0 →
      ctrN P = 0
#check s42_thm6

def cexC : Fin 3 → Fin 2 → ℝ := ![![-1, -1], ![2, -1], ![-1, 2]]
def cexP : Fin 5 → ℝ := ![0, 1 / 2, 1 / 2, 1, 3 / 2]

/-- The explicit n = 2 counterexample of §7. -/
-- UNPROVED:
def s43_thm6_explicit : Prop :=
  ∑ i, cexC i = 0 ∧ AffineIndependent ℝ cexC ∧
  (∀ i, lie cexP (chart 1 (cexC i 0) (cexC i 1)) = 0) ∧
  lie cexP (chart 3 3 3) = 0 ∧ cexP 3 = 1 ∧
  ctr cexP = ![1 / 2, 1 / 2] ∧ ctr cexP ≠ 0
#check s43_thm6_explicit

end

end L13Blind
