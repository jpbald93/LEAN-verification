/-
  L13 blind re-formalisation of the Paper K draft (paperk_frozen_v2.tex).
  Writer had access to the .tex only. Every statement below is an independent reading.
  All statements are stated as `Prop`-valued definitions and `#check`ed (no proofs are claimed):
  no Mathlib build was available on the writer's machine, so no proof could be checked.
  Invented vocabulary (not in Mathlib): `lie`, `ctr`, `chart`, `lag`, `gram`, `cof`, `det4`,
  `lie3`, `ctr3`, `chart3`, `LV`, `lieN`, `ctrN`, `chartN`, `sqd`.
-/
import Mathlib
import PaperK.LieCore
import PaperK.TwoD
import PaperK.ThreeD
import PaperK.GeneralN

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

/- Comparison certificates. Repository declarations occur only in type_of%.
   The preceding blind definitions are copied verbatim from the supplied file. -/
namespace L13Compare
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open L13Blind Matrix
noncomputable section

def v2 (p : ℝ × ℝ) : Fin 2 → ℝ := ![p.1, p.2]

theorem v2_eq (p q : ℝ × ℝ) : v2 p = v2 q ↔ p = q := by
  simp [v2, funext_iff, Fin.forall_fin_two, Prod.ext_iff]

theorem v2_comb (p q : ℝ × ℝ) (s t : ℝ) :
    v2 (s • p + t • q) = s • v2 p + t • v2 q := by
  ext k; fin_cases k <;> rfl

theorem col2 (p q z : ℝ × ℝ) :
    Collinear ℝ ({v2 p, v2 q, v2 z} : Set (Fin 2 → ℝ)) ↔
    Collinear ℝ ({p,q,z} : Set (ℝ × ℝ)) := by
  rw [collinear_iff_of_mem (Set.mem_insert (v2 p) _),
      collinear_iff_of_mem (Set.mem_insert p _)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, vadd_eq_add]
  constructor
  · rintro ⟨v, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    refine ⟨(v 0, v 1), ⟨a, ?_⟩, ⟨b, ?_⟩, ⟨c, ?_⟩⟩
    all_goals apply Prod.ext
    all_goals first | exact congrFun ha 0 | exact congrFun ha 1 |
      exact congrFun hb 0 | exact congrFun hb 1 | exact congrFun hc 0 | exact congrFun hc 1
  · rintro ⟨v, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    refine ⟨v2 v, ⟨a, ?_⟩, ⟨b, ?_⟩, ⟨c, ?_⟩⟩
    · ext k; fin_cases k
      · exact congrArg Prod.fst ha
      · exact congrArg Prod.snd ha
    · rw [hb]; ext k; fin_cases k <;> rfl
    · rw [hc]; ext k; fin_cases k <;> rfl

theorem s11_RB (H : type_of% PaperK.prop31) : s11_thm1 := by
  intro X A A' P i hs hp ha ha' hv
  obtain ⟨hm, ⟨s,t,hst,he⟩, hc⟩ := H X i A A' P hs hp ha ha' hv
  refine ⟨hm, ⟨s,t,hst,?_⟩, (col2 (PaperK.pt P) (PaperK.pt A) (PaperK.pt A')).2 hc⟩
  change v2 (PaperK.pt P) = s • v2 (PaperK.pt A) + t • v2 (PaperK.pt A')
  rw [he, v2_comb]

theorem s11_BR (H : s11_thm1) : type_of% PaperK.prop31 := by
  intro X i A A' P hs hp ha ha' hv
  obtain ⟨hm, ⟨s,t,hst,he⟩, hc⟩ := H X A A' P i hs hp ha ha' hv
  refine ⟨hm, ⟨s,t,hst,?_⟩, (col2 (PaperK.pt P) (PaperK.pt A) (PaperK.pt A')).1 hc⟩
  apply (v2_eq (PaperK.pt P) (s • PaperK.pt A + t • PaperK.pt A')).1
  rw [v2_comb]
  exact he

/- s12: only the safe direction. The real conclusion is only Collinear. -/
theorem s12_BR (H : s12_thm1_cofactor) : type_of% PaperK.prop31_cofactor := by
  intro M i A A' hs ha ha' hv
  obtain ⟨_,s,t,hst,he⟩ := H M A A' i hs ha ha' hv
  apply (col2 (PaperK.pt (PaperK.G *ᵥ PaperK.cofactor M)) (PaperK.pt A) (PaperK.pt A')).1
  apply collinear_insert_of_mem_affineSpan_pair
  have e : ctr (gram *ᵥ cof M) = AffineMap.lineMap (ctr A) (ctr A') t := by
    rw [he, AffineMap.lineMap_apply_module, ← hst]; simp only [add_sub_cancel_right]
  rw [show v2 (PaperK.pt (PaperK.G *ᵥ PaperK.cofactor M)) = ctr (gram *ᵥ cof M) from rfl, e]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

def pack {n : ℕ} (X : LV n) : PaperKn.Cyc n := ⟨X.1,X.2.1,X.2.2.1,X.2.2.2⟩
def unpack {n : ℕ} (X : PaperKn.Cyc n) : LV n := (X.r,X.c,X.v,X.w)

theorem pack_comb {n : ℕ} (A A' : LV n) (a b : ℝ) :
    pack (a • A + b • A') = a • pack A + b • pack A' := rfl

/- s16: the real statement additionally returns an affine combination. -/
theorem s16_RB (H : ∀ n, type_of% (@PaperKn.prop31 n)) : s16_thm1_N := by
  intro n X A A' P i hs hp ha ha' hv
  have hs' : ∀ Y, (∀ j, j ≠ i → PaperKn.B Y (pack (X j)) = 0) →
      ∃ a b : ℝ, Y = a • pack A + b • pack A' := by
    intro Y hy
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.1 (hs (unpack Y) hy)
    refine ⟨a,b,?_⟩
    have e := congrArg pack he
    exact e.symm
  exact (H n (fun j => pack (X j)) i (pack A) (pack A') (pack P) hs' hp ha ha' hv).2

theorem s17_RB (H : type_of% PaperK.explicit_power) : s17_thm2 := by
  intro r a b
  dsimp only
  intro hd i
  simpa [lag, sqd, PaperK.sq, PaperK.det4, det4, Fin.sum_univ_two] using H r a b hd i

theorem s17_BR (H : s17_thm2) : type_of% PaperK.explicit_power := by
  intro r a b hd i
  simpa [lag, sqd, PaperK.sq, PaperK.det4, det4, Fin.sum_univ_two] using H r a b hd i

theorem s18_RB (H : type_of% PaperK.explicit_power_indep) : s18_thm2_indep := by
  intro r a b
  dsimp only
  intro hd i j
  simpa [lag, sqd, PaperK.sq, PaperK.det4, det4, Fin.sum_univ_two] using H r a b hd i j

theorem s18_BR (H : s18_thm2_indep) : type_of% PaperK.explicit_power_indep := by
  intro r a b hd i j
  simpa [lag, sqd, PaperK.sq, PaperK.det4, det4, Fin.sum_univ_two] using H r a b hd i j

/- s19 is not a single paired theorem. Its D != 0 restriction loses the
   singular-matrix cases of row_relation and cof0--cof4. No equivalence asserted. -/

theorem s21_RB (H : type_of% PaperK.power_eq_of_B_eq_zero) : s21_thm3 := by
  intro P Y hv hy hn ho
  simpa [lag, sqd, ctr, lie, PaperK.B, PaperK.power, PaperK.pt, Fin.sum_univ_two] using H P Y hv hy hn ho

theorem s21_BR (H : s21_thm3) : type_of% PaperK.power_eq_of_B_eq_zero := by
  intro P Y hv hy hn ho
  simpa [lag, sqd, ctr, lie, PaperK.B, PaperK.power, PaperK.pt, Fin.sum_univ_two] using H P Y hv hy hn ho

/- The blind family quantifies Type 0; the declaration is universe-polymorphic.
   The converse below is the exact Type 0 instance, not a universe generalization. -/
theorem s22_RB (H : ∀ (ι : Type), type_of% (@PaperK.equal_power ι)) : s22_thm3_family := by
  intro ι P Y hv hy hn ho i j
  simpa [lag, sqd, ctr, PaperK.power, PaperK.pt, Fin.sum_univ_two] using H ι Y P hv hy hn ho i j

theorem s22_BR (H : s22_thm3_family) : ∀ (ι : Type), type_of% (@PaperK.equal_power ι) := by
  intro ι Y P hv hy hn ho i j
  simpa [lag, sqd, ctr, PaperK.power, PaperK.pt, Fin.sum_univ_two] using H ι P Y hv hy hn ho i j

theorem s23_RB (H : type_of% PaperK2.power_eq_const) : s23_thm3_coord := by
  intro P r a b hv ho
  simpa [lag, sqd, ctr, PaperK2.pw, PaperK2.pconst, Fin.sum_univ_two, mul_div_assoc] using H P hv r a b ho

theorem s23_BR (H : s23_thm3_coord) : type_of% PaperK2.power_eq_const := by
  intro P hv r a b ho
  simpa [lag, sqd, ctr, PaperK2.pw, PaperK2.pconst, Fin.sum_univ_two, mul_div_assoc] using H P r a b hv ho

theorem constantN {n : ℕ} (P : PaperKn.Cyc n) (hv : P.v ≠ 0) :
    (∑ k, (P.c k / P.v)^2) - (P.r / P.v)^2 + 2 * P.w / P.v =
      -PaperKn.B P P / P.v^2 := by
  simp only [div_pow, ← Finset.sum_div, PaperKn.B, ← pow_two]
  field_simp
  ring

theorem s24_RB (H : ∀ n, type_of% (@PaperKn.power_eq_const n)) : s24_thm3_N := by
  intro n P r c hv ho
  have e := H n (pack P) (PaperKn.aff r c) hv rfl rfl ho
  rw [constantN (pack P) hv] at e
  exact e

theorem s24_BR (H : s24_thm3_N) : ∀ n, type_of% (@PaperKn.power_eq_const n) := by
  intro n P X hv hx hw ho
  have ex : PaperKn.aff X.r X.c = X := by
    cases X
    simp_all only [PaperKn.aff]
  have e := H n (unpack P) X.r X.c hv (by change PaperKn.B P (PaperKn.aff X.r X.c) = 0; rw [ex]; exact ho)
  rw [constantN P hv]
  exact e

/- s25: the listed real conclusions identify explicit Cramer coordinates.
   The blind conclusion instead characterizes a unique equidistant point.
   Identifying that point with the explicit coordinates requires an additional
   existence/calculation argument, not definition unfolding. Comparison stopped. -/

/- The actual equilateral declaration has NO null hypothesis on P. -/
theorem s26_RB (H : type_of% PaperK2.equilateral_PX) : s26_thm4 := by
  intro P _ hv h1 h2 h3
  have e := H P hv 1 0 0 h1 h2 h3 h1
  exact congrArg v2 e

theorem s27_RB (H : type_of% PaperK2.equilateral_PX) : s27_thm4_no_null := by
  intro P hv h1 h2 h3
  exact congrArg v2 (H P hv 1 0 0 h1 h2 h3 h1)

theorem s27_BR (H : s27_thm4_no_null) : type_of% PaperK2.equilateral_PX := by
  intro P hv r a b h1 h2 h3 _
  exact (v2_eq _ _).1 (H P hv h1 h2 h3)

theorem chart_tangent (r a b r' a' b' : ℝ) :
    lie (chart r a b) (chart r' a' b') = 0 ↔ PaperK2.Tangent a b r a' b' r' := by
  simp only [lie, chart, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, PaperK2.Tangent]
  constructor <;> intro h <;> linarith

/- The square is the same labelled configuration up to the explicit permutation
   blind -> real [0,3,1,2]; this is an index transport, not a new pairing. -/
def perm4 : Fin 4 → Fin 4 := ![0,3,1,2]
def inv4 : Fin 4 → Fin 4 := ![0,2,3,1]
theorem perm_inv (k : Fin 4) : perm4 (inv4 k) = k := by fin_cases k <;> rfl

theorem square_pred (k : Fin 4) (r a b : ℝ) :
    (∀ j, j ≠ k → lie (chart r a b) (sq j) = 0) ↔
    (∀ j, j ≠ perm4 k → PaperK2.Tangent a b r (PaperK2.sqa j) (PaperK2.sqb j) 1) := by
  fin_cases k <;>
    simp [Fin.forall_fin_succ, L13Blind.sq, perm4, PaperK2.sqa, PaperK2.sqb, chart_tangent,
      and_comm, and_left_comm]

theorem s28_RB (H : type_of% PaperK2.square_apollonius) : s28_thm5_apollonius := by
  intro k r a b
  exact (square_pred k r a b).trans (H (perm4 k) a b r)

theorem s28_BR (H : s28_thm5_apollonius) : type_of% PaperK2.square_apollonius := by
  intro k a b r
  have e := (square_pred (inv4 k) r a b).symm.trans (H (inv4 k) r a b)
  simpa only [perm_inv] using e

theorem s29_RB (H : type_of% PaperK2.square_apollonius_radii_ne) : s29_thm5_distinct := H
theorem s29_BR (H : s29_thm5_distinct) : type_of% PaperK2.square_apollonius_radii_ne := H

theorem square_all (P : Fin 5 → ℝ) :
    (∀ j, lie P (L13Blind.sq j) = 0) ↔
    (∀ j, PaperK2.B P (PaperK2.circ 1 (PaperK2.sqa j) (PaperK2.sqb j)) = 0) := by
  simp [Fin.forall_fin_succ, L13Blind.sq, PaperK2.sqa, PaperK2.sqb,
    PaperK2.B, PaperK2.circ, lie, chart, and_comm, and_left_comm, and_assoc]

def R30 : Prop := (type_of% PaperK2.square_null_space) ∧
    (type_of% PaperK2.square_null_span) ∧ (type_of% PaperK2.square_null_indep)

theorem s30_RB (H : R30) : s30_thm5_null_space := by
  have hi : LinearIndependent ℝ ![sqU,sqW] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hz := H.2.2 (g 0) (g 1) (by simpa only [sqU, sqW, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hg)
    fin_cases i
    · exact hz.1
    · exact hz.2
  refine ⟨?_,hi,?_⟩
  · intro P
    rw [square_all, H.2.1 P, Submodule.mem_span_pair]
    constructor <;> rintro ⟨s,t,h⟩ <;> exact ⟨s,t,h.symm⟩
  · have hr : Set.range ![sqU,sqW] = ({sqU,sqW} : Set (Fin 5 → ℝ)) := by
      ext x; simp [or_comm]
    have hd := finrank_span_eq_card hi
    change Module.finrank ℝ (Submodule.span ℝ (Set.range ![sqU,sqW])) = 2 at hd
    rw [hr] at hd
    exact hd

theorem s30_BR (H : s30_thm5_null_space) : R30 := by
  have hs : type_of% PaperK2.square_null_span := by
    intro P
    rw [← square_all, H.1 P, Submodule.mem_span_pair]
    constructor <;> rintro ⟨s,t,h⟩ <;> exact ⟨s,t,h.symm⟩
  refine ⟨?_,hs,?_⟩
  · intro P
    rw [hs P]
    constructor
    · rintro ⟨s,t,rfl⟩
      simp
      ring
    · rintro ⟨h1,h2,h4⟩
      refine ⟨P 0,P 3,?_⟩
      ext k; fin_cases k <;> simp [h1,h2,h4] <;> ring
  · intro s u he
    have hz := (Fintype.linearIndependent_iff.1 H.2.1) (![s,u])
      (by simpa only [sqU, sqW, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using he)
    exact ⟨hz 0,hz 1⟩

theorem s32_RB (H : type_of% PaperK2.square_PX) : s32_thm5_centre := by
  intro P ho hv
  simpa [v2, ctr] using congrArg v2 (H P hv ((square_all P).1 ho))

theorem s32_BR (H : s32_thm5_centre) : type_of% PaperK2.square_PX := by
  intro P hv ho
  apply (v2_eq _ _).1
  simpa [v2, ctr] using H P ((square_all P).2 ho) hv

theorem chart3_sph (r : ℝ) (c : Fin 3 → ℝ) :
    chart3 r c = PaperK3.sph r (c 0) (c 1) (c 2) := by
  ext k; fin_cases k <;> simp [chart3, PaperK3.sph] <;> ring

theorem tetra_all (P : Fin 6 → ℝ) (r : ℝ) (c : Fin 3 → ℝ) :
    ((∀ i, lie3 P (chart3 1 (tet i)) = 0) ∧ lie3 P (chart3 r c) = 0) ↔
    (∀ i, PaperK3.B P (PaperK3.tetraFam r (c 0) (c 1) (c 2) i) = 0) := by
  simp only [Fin.forall_fin_succ, tet, Matrix.cons_val_zero, Matrix.cons_val_succ,
    chart3_sph, PaperK3.tetraFam, lie3, PaperK3.B]
  simp [and_assoc]

/- Lean more general: no null hypothesis on P in tetra_PX_origin. -/
theorem s33_RB (H : type_of% PaperK3.tetra_PX_origin) : s33_tetra_centre := by
  intro P r c _ ho h5 hv
  obtain ⟨h1,h2,h3⟩ := H r (c 0) (c 1) (c 2) P ((tetra_all P r c).1 ⟨ho,h5⟩) hv
  ext k; fin_cases k <;> simp [ctr3,h1,h2,h3]

theorem s34_RB (H : type_of% PaperK3.tetra_equidistant_unique) : s34_tetra_equidistant := by
  intro x he
  obtain ⟨hx,hy,hz,hd⟩ := H (x 0) (x 1) (x 2) (sqd x (tet 0))
    (by simpa [sqd,tet,Fin.sum_univ_three] using he 0 0)
    (by simpa [sqd,tet,Fin.sum_univ_three] using he 1 0)
    (by simpa [sqd,tet,Fin.sum_univ_three] using he 2 0)
    (by simpa [sqd,tet,Fin.sum_univ_three] using he 3 0)
  refine ⟨?_,hd⟩
  ext k; fin_cases k <;> simp [hx,hy,hz]

theorem s34_BR (H : s34_tetra_equidistant) : type_of% PaperK3.tetra_equidistant_unique := by
  intro x y z d h0 h1 h2 h3
  have hd : ∀ i, sqd (![x,y,z]) (tet i) = d := by
    intro i
    fin_cases i <;> simpa [sqd, tet, Fin.sum_univ_three] using (by assumption)
  obtain ⟨he,hh⟩ := H (![x,y,z]) (fun i j => (hd i).trans (hd j).symm)
  refine ⟨congrFun he 0, congrFun he 1, congrFun he 2, ?_⟩
  exact (hd 0).symm.trans hh

def R35 : Prop := (type_of% PaperK3.tetra_tangent_B) ∧ (type_of% PaperK3.tetra_radii_metric)

theorem s35_RB (H : R35) : s35_tetra_apollonius := by
  intro i
  have hh := H.1 i
  fin_cases i <;> simpa [chart3_sph, tet, PaperK3.tetraFam, lie3, PaperK3.B] using hh

/- This is only the tangency component of the paired real conjunction. -/
theorem s35_BR_tangency (H : s35_tetra_apollonius) : type_of% PaperK3.tetra_tangent_B := by
  intro i
  have hh := H i
  fin_cases i <;> simpa [chart3_sph, tet, PaperK3.tetraFam, lie3, PaperK3.B] using hh

/- s36: STOP. Blind centres are fixed tet i, while tetraFamR centres are
   s * tet i. In addition, the blind statement requires P null; the real does not.
   These are different objects at the same parameter s, not an encoding bridge. -/

theorem s37_RB (H : type_of% PaperK3.tetra_affineIndependent) : s37_tetra_affind := H
theorem s37_BR (H : s37_tetra_affind) : type_of% PaperK3.tetra_affineIndependent := H

/- s38 UNPAIRED: the listed declarations concern distances from the origin
   and contact radii, not pairwise distances between distinct vertices. -/

theorem s39_RB (H : ∀ n m, type_of% (@PaperKn.simplex_E1 n m)) : s39_simplex := by
  intro n c P hi hs hn ho hv
  exact H n (n+1) rfl c hs hi (by simpa only [sqd, Pi.zero_apply, sub_zero] using hn)
    (PaperKn.aff 1 (c 0)) (pack P) hv ho (ho 0)

theorem s39_BR (H : s39_simplex) : ∀ n m, type_of% (@PaperKn.simplex_E1 n m) := by
  intro n m hm c hs hi hn X P hv ho _
  subst m
  exact H n c (unpack P) hi hs (by simpa only [sqd, Pi.zero_apply, sub_zero] using hn) ho hv

/- s40 STOP: the blind RHS is a Mathlib simplex circumradius; the real
   conclusion equates the squared vertex norm to an explicit power constant.
   Identifying that geometric circumradius requires genuine circumcentre theory. -/

/- Lean more general: arbitrary common radius and an explicit common value. -/
theorem s41_RB (H : ∀ n m, type_of% (@PaperKn.dist_sq_const n m)) : s41_dist_const := by
  intro n m c P ho hv i j
  exact (H n m c 1 (pack P) hv ho i).trans (H n m c 1 (pack P) hv ho j).symm

/- The real negative theorem locates failure specifically in dimension two;
   the blind negates the statement simultaneously over all dimensions. -/
theorem s42_RB (H : type_of% PaperKn.brief_E_false) : s42_thm6 := by
  intro hall
  apply H
  intro c hs hi X P hv ho hx
  exact hall 2 c (unpack X) (unpack P) hi hs ho hx hv

def R43 : Prop := (type_of% PaperKn.cex_sum) ∧ (type_of% PaperKn.cex_affInd) ∧
    (type_of% PaperKn.cex_orth) ∧ (type_of% PaperKn.cex_pt_ne)

theorem cex_form (r a b : ℝ) :
    lie cexP (chart r a b) = PaperKn.B PaperKn.cex_P (PaperKn.aff r ![a,b]) := by
  simp [lie, cexP, chart, PaperKn.B, PaperKn.cex_P, PaperKn.aff, Fin.sum_univ_two]
  ring

theorem s43_RB (H : R43) : s43_thm6_explicit := by
  refine ⟨H.1,H.2.1,?_,?_,?_,?_,?_⟩
  · intro i
    have e := H.2.2.1.1 i
    rw [cex_form]
    fin_cases i <;> exact e
  · rw [cex_form]; exact H.2.2.1.2
  · rfl
  · change ![(1/2 : ℝ)/1,(1/2 : ℝ)/1] = ![1/2,1/2]
    simp only [div_one]
  · have he : ctr cexP = PaperKn.pt PaperKn.cex_P := by ext k; fin_cases k <;> rfl
    rw [he]; exact H.2.2.2

theorem s43_BR (H : s43_thm6_explicit) : R43 := by
  refine ⟨H.1,H.2.1,⟨?_,?_⟩,?_⟩
  · intro i
    have e := H.2.2.1 i
    rw [cex_form] at e
    fin_cases i <;> exact e
  · rw [← cex_form]; exact H.2.2.2.1
  · have he : ctr cexP = PaperKn.pt PaperKn.cex_P := by ext k; fin_cases k <;> rfl
    rw [← he]; exact H.2.2.2.2.2.2

theorem s01_RB (H : type_of% PaperK.B_self_eq_zero_iff) : s01_null_iff := H
theorem s01_BR (H : s01_null_iff) : type_of% PaperK.B_self_eq_zero_iff := H

def R02 : Prop := (type_of% PaperK.B_eq_dot_G) ∧ (type_of% PaperK.G_mul_G)

theorem s02_RB (H : R02) : s02_gram := by
  refine ⟨PaperK.G,?_,H.2,H.1⟩
  change PaperK.G.transpose = PaperK.G
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [PaperK.G]

/- The converse identifies the witness entrywise by specializing its form
   equation at coordinate unit vectors; no matrix-uniqueness theorem is used. -/
theorem s02_BR (H : s02_gram) : R02 := by
  obtain ⟨G,_,hg,hb⟩ := H
  have he : G = PaperK.G := by
    ext i j
    have hh := hb (Pi.single i 1) (Pi.single j 1)
    fin_cases i <;> fin_cases j <;>
      norm_num [lie, PaperK.G, Matrix.mulVec, dotProduct, Fin.sum_univ_five, Pi.single_apply] at hh ⊢ <;>
      simp only [Fin.ext_iff] at hh <;> norm_num at hh <;>
      linarith
  subst G
  exact ⟨hb,hg⟩

theorem s04_RB (H : type_of% PaperK.tangency_identity) : s04_tangency := H
theorem s04_BR (H : s04_tangency) : type_of% PaperK.tangency_identity := H

/- s07 UNPAIRED with the supplied counterpart: an exact value identity on
   charts is not the homogeneous zero-locus iff in B_eq_zero_iff_tangent. -/

theorem tangent_normalize (X Y : Fin 5 → ℝ) (hv : X 3 ≠ 0) (hw : Y 3 ≠ 0) :
    ((X 0*Y 3-Y 0*X 3)^2 = (X 1*Y 3-Y 1*X 3)^2+(X 2*Y 3-Y 2*X 3)^2) ↔
    sqd (ctr X) (ctr Y) = (X 0/X 3-Y 0/Y 3)^2 := by
  simp only [sqd, ctr, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  constructor <;> intro h <;> linarith

theorem s08_RB (H : type_of% PaperK.B_eq_zero_iff_tangent) : s08_tangent_iff := by
  intro X Y hx hy hv hw
  exact (H X Y hx hy hv hw).trans (tangent_normalize X Y hv hw)

theorem s08_BR (H : s08_tangent_iff) : type_of% PaperK.B_eq_zero_iff_tangent := by
  intro X Y hx hy hv hw
  exact (H X Y hx hy hv hw).trans (tangent_normalize X Y hv hw).symm

theorem s09_RB (H : type_of% PaperK.mulVec_cofactor) : s09_cofactor_null := H
theorem s09_BR (H : s09_cofactor_null) : type_of% PaperK.mulVec_cofactor := H

theorem s10_RB (H : type_of% PaperK.B_G_cofactor_row) : s10_cofactor_orth := H
theorem s10_BR (H : s10_cofactor_orth) : type_of% PaperK.B_G_cofactor_row := H

/- Remaining paired general-n relations were not in the priority list; they
   are checked after the requested priority blocks, without changing pairing. -/
theorem s13_RB (H : ∀ n, type_of% (@PaperKn.B_self_eq_zero_iff n)) : s13_null_iff_N := by
  intro n X; exact H n (pack X)
theorem s13_BR (H : s13_null_iff_N) : ∀ n, type_of% (@PaperKn.B_self_eq_zero_iff n) := by
  intro n X; exact H n (unpack X)

theorem s14_RB (H : ∀ n, type_of% (@PaperKn.tangency_identity n)) : s14_tangency_N := by
  intro n X Y; exact H n (pack X) (pack Y)
theorem s14_BR (H : s14_tangency_N) : ∀ n, type_of% (@PaperKn.tangency_identity n) := by
  intro n X Y; exact H n (unpack X) (unpack Y)

theorem div_diff (a b v w : ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    a/v-b/w = (a*w-b*v)/(v*w) := by field_simp

theorem tangent_normalizeN {n : ℕ} (X Y : PaperKn.Cyc n) (hv : X.v ≠ 0) (hw : Y.v ≠ 0) :
    ((X.r*Y.v-Y.r*X.v)^2 = ∑ k, (X.c k*Y.v-Y.c k*X.v)^2) ↔
    sqd (ctrN (unpack X)) (ctrN (unpack Y)) = (X.r/X.v-Y.r/Y.v)^2 := by
  simp only [sqd, ctrN, unpack, div_diff _ _ X.v Y.v hv hw, div_pow, ← Finset.sum_div]
  rw [div_left_inj' (pow_ne_zero 2 (mul_ne_zero hv hw))]
  exact eq_comm

theorem s15_RB (H : ∀ n, type_of% (@PaperKn.B_eq_zero_iff_tangent n)) : s15_tangent_iff_N := by
  intro n X Y hx hy hv hw
  exact (H n (pack X) (pack Y) hx hy hv hw).trans (tangent_normalizeN (pack X) (pack Y) hv hw)

theorem s15_BR (H : s15_tangent_iff_N) : ∀ n, type_of% (@PaperKn.B_eq_zero_iff_tangent n) := by
  intro n X Y hx hy hv hw
  exact (H n (unpack X) (unpack Y) hx hy hv hw).trans (tangent_normalizeN X Y hv hw).symm

/- Supplementary certificate for the partially paired prose link. -/
def R19 : Prop := (type_of% PaperK.row_relation) ∧ (type_of% PaperK.cof0) ∧
    (type_of% PaperK.cof1) ∧ (type_of% PaperK.cof2) ∧
    (type_of% PaperK.cof3) ∧ (type_of% PaperK.cof4)

theorem s19_RB (H : R19) : s19_thm2_link := by
  intro r a b
  dsimp only
  intro hd
  let s := PaperK.sq r a b
  let D := PaperK.det4 r a b 1
  let q := PaperK.cofactor (PaperK.Mrow r a b)
  change (∀ i, lie (![q 0,-q 1,-q 2,2*q 3,-q 4]) (chart (r i) (a i) (b i)) = 0) ∧
    (![q 0,-q 1,-q 2,2*q 3,-q 4] : Fin 5 → ℝ) 3 = -2*D ∧
    ctr (![q 0,-q 1,-q 2,2*q 3,-q 4]) =
      ![-PaperK.det4 r b s 1/(2*D),PaperK.det4 r a s 1/(2*D)] ∧
    (![q 0,-q 1,-q 2,2*q 3,-q 4] : Fin 5 → ℝ) 0 /
      (![q 0,-q 1,-q 2,2*q 3,-q 4] : Fin 5 → ℝ) 3 = -PaperK.det4 a b s 1/(2*D)
  have h0 : q 0 = PaperK.det4 a b s 1 := H.2.1 r a b
  have h1 : q 1 = -PaperK.det4 r b s 1 := H.2.2.1 r a b
  have h2 : q 2 = PaperK.det4 r a s 1 := H.2.2.2.1 r a b
  have h3 : q 3 = -D := H.2.2.2.2.1 r a b
  have h4 : q 4 = PaperK.det4 r a b s := H.2.2.2.2.2 r a b
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    have hr := H.1 r a b i
    simp [lie,chart,h0,h1,h2,h3,h4]
    dsimp only [s,D]
    dsimp only [PaperK.sq] at hr
    linarith
  · change 2*q 3 = -2*D
    rw [h3]; ring
  · ext k; fin_cases k <;> simp [ctr,h1,h2,h3] <;> ring
  · change q 0 / (2*q 3) = -PaperK.det4 a b s 1/(2*D)
    rw [h0,h3]; ring

end
end L13Compare
