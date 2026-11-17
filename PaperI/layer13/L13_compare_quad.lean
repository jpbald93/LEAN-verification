import Quadrilaterals

/-!
# L13 comparison (J), quadrilaterals: blind statements (PaperIBlind.lean) vs `Quadrilaterals`.
No theorem of the `Quadrilaterals` library is used in any proof body; library names occur only
inside `type_of%` to state goals. Library *definitions* (`ConvexQuad`, `IsIncircle`, `Tangential`,
`triArea`, `quadArea`, `semiperimeter`, `quadSign`, `squareCenter`) are unfolded. All coordinate
facts needed are re-proved below from Mathlib.
-/

noncomputable section
open scoped RealInnerProductSpace
open Set Metric EuclideanGeometry

universe u v

set_option linter.unusedVariables false

namespace L13JQ

/-! ## Blind definitions (verbatim from Blind.lean) -/

def BlindPlane (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] : Prop :=
  Module.finrank ℝ V = 2

def BlindSideAB {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B : P) : ℝ :=
  dist A B

def BlindSideBC {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (B C : P) : ℝ :=
  dist B C

def BlindSideCD {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (C D : P) : ℝ :=
  dist C D

def BlindSideDA {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (D A : P) : ℝ :=
  dist D A

def BlindDiagonalAC {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A C : P) : ℝ :=
  dist A C

def BlindDiagonalBD {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (B D : P) : ℝ :=
  dist B D

def BlindSemiperimeter {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C D : P) : ℝ :=
  (1 / 2 : ℝ) * (dist A B + dist B C + dist C D + dist D A)

def BlindConvexQuad {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C D : P) : Prop :=
  BlindPlane V ∧
    ¬ Collinear ℝ ({A, B, C} : Set P) ∧
    ∃ (X : P) (t u : ℝ),
      t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1 ∧
      X = t • (C -ᵥ A) +ᵥ A ∧
      X = u • (D -ᵥ B) +ᵥ B

def BlindCross {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e : OrthonormalBasis (Fin 2) ℝ V) (v w : V) : ℝ :=
  inner ℝ v (e 0) * inner ℝ w (e 1) -
    inner ℝ v (e 1) * inner ℝ w (e 0)

def BlindTriangleAreaBAC {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C : P) : ℝ :=
  (1 / 2 : ℝ) * dist A B * dist A C *
    Real.sin (EuclideanGeometry.angle B A C)

def BlindTriangleAreaCAD {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A C D : P) : ℝ :=
  (1 / 2 : ℝ) * dist A C * dist A D *
    Real.sin (EuclideanGeometry.angle C A D)

def BlindQuadArea {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) : ℝ :=
  BlindTriangleAreaBAC A B C + BlindTriangleAreaCAD A C D

def BlindSideLine {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (X Y : P) : Set P :=
  (affineSpan ℝ ({X, Y} : Set P) : Set P)

def BlindLineDistance {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (X Y Z : P) : ℝ :=
  Metric.infDist Z (BlindSideLine X Y)

def BlindSameSide {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (X Y Z W : P) : Prop :=
  ∃ e : OrthonormalBasis (Fin 2) ℝ V,
    BlindCross e (Y -ᵥ X) (Z -ᵥ X) *
      BlindCross e (Y -ᵥ X) (W -ᵥ X) > 0

def BlindIncircle {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D I : P) (r : ℝ) : Prop :=
  BlindPlane V ∧ r > 0 ∧
    BlindLineDistance A B I = r ∧
    BlindLineDistance B C I = r ∧
    BlindLineDistance C D I = r ∧
    BlindLineDistance D A I = r ∧
    BlindSameSide A B I C ∧
    BlindSameSide B C I D ∧
    BlindSameSide C D I A ∧
    BlindSameSide D A I B

def BlindTangentialQuad {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) : Prop :=
  ∃ (I : P) (r : ℝ), BlindIncircle A B C D I r

def BlindVanAubelSign {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (e : OrthonormalBasis (Fin 2) ℝ V) (A B C D : P) : ℝ :=
  if BlindCross e (C -ᵥ A) (D -ᵥ B) > 0 then 1 else -1

def BlindVanAubelRotation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (e : OrthonormalBasis (Fin 2) ℝ V)
    (σ : ℝ) (v : V) : V :=
  (Real.cos (-σ * Real.pi / 2) * inner ℝ v (e 0) -
      Real.sin (-σ * Real.pi / 2) * inner ℝ v (e 1)) • e 0 +
    (Real.sin (-σ * Real.pi / 2) * inner ℝ v (e 0) +
      Real.cos (-σ * Real.pi / 2) * inner ℝ v (e 1)) • e 1

def BlindVanAubelCenter {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (e : OrthonormalBasis (Fin 2) ℝ V) (A B C D X Y : P) : P :=
  ((1 / 2 : ℝ) •
    BlindVanAubelRotation e (BlindVanAubelSign e A B C D) (Y -ᵥ X)) +ᵥ
      midpoint ℝ X Y

/-! ## Blind statements as closed propositions (verbatim; the proof placeholder dropped) -/

-- thm:bretschneider (blind_1)
def blind1_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D),
    BlindQuadArea A B C D ^ 2 =
      (BlindSemiperimeter A B C D - BlindSideAB A B) *
      (BlindSemiperimeter A B C D - BlindSideBC B C) *
      (BlindSemiperimeter A B C D - BlindSideCD C D) *
      (BlindSemiperimeter A B C D - BlindSideDA D A) -
      BlindSideAB A B * BlindSideBC B C * BlindSideCD C D * BlindSideDA D A *
        Real.cos ((EuclideanGeometry.angle A B C +
          EuclideanGeometry.angle C D A) / 2) ^ 2

-- thm:brahmagupta (blind_2)
def blind2_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D)
    (hcyclic : Cospherical ({A, B, C, D} : Set P)),
    BlindQuadArea A B C D =
      Real.sqrt
        ((BlindSemiperimeter A B C D - BlindSideAB A B) *
         (BlindSemiperimeter A B C D - BlindSideBC B C) *
         (BlindSemiperimeter A B C D - BlindSideCD C D) *
         (BlindSemiperimeter A B C D - BlindSideDA D A))

-- thm:pitot (blind_3)
def blind3_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D)
    (htangent : BlindTangentialQuad A B C D),
    BlindSideAB A B + BlindSideCD C D = BlindSideBC B C + BlindSideDA D A

-- thm:pitot converse (blind_4)
def blind4_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D)
    (hsides : BlindSideAB A B + BlindSideCD C D =
      BlindSideBC B C + BlindSideDA D A),
    BlindTangentialQuad A B C D

-- thm:euler4 (blind_5)
def blind5_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V),
    BlindSideAB A B ^ 2 + BlindSideBC B C ^ 2 +
      BlindSideCD C D ^ 2 + BlindSideDA D A ^ 2 =
      BlindDiagonalAC A C ^ 2 + BlindDiagonalBD B D ^ 2 +
        4 * dist (midpoint ℝ A C) (midpoint ℝ B D) ^ 2

-- thm:ptolemy2 (blind_6)
def blind6_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D)
    (hcyclic : Cospherical ({A, B, C, D} : Set P)),
    dist A C / dist B D =
      (dist A B * dist A D + dist C B * dist C D) /
        (dist B A * dist B C + dist D A * dist D C)

-- thm:vanaubel equal lengths (blind_7)
def blind7_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (e : OrthonormalBasis (Fin 2) ℝ V)
    (hplane : BlindPlane V),
    dist (BlindVanAubelCenter e A B C D A B)
        (BlindVanAubelCenter e A B C D C D) =
      dist (BlindVanAubelCenter e A B C D B C)
        (BlindVanAubelCenter e A B C D D A)

-- thm:vanaubel perpendicularity (blind_8)
def blind8_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (e : OrthonormalBasis (Fin 2) ℝ V)
    (hplane : BlindPlane V),
    inner ℝ
      (BlindVanAubelCenter e A B C D C D -ᵥ BlindVanAubelCenter e A B C D A B)
      (BlindVanAubelCenter e A B C D D A -ᵥ BlindVanAubelCenter e A B C D B C) =
        0

-- thm:newton (blind_9)
def blind9_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D I : P) (r : ℝ) (hplane : BlindPlane V)
    (hconvex : BlindConvexQuad A B C D) (hincircle : BlindIncircle A B C D I r),
    Collinear ℝ ({midpoint ℝ A C, midpoint ℝ B D, I} : Set P)

-- thm:fuss (blind_10)
def blind10_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D O I : P) (R r : ℝ) (hplane : BlindPlane V)
    (hconvex : BlindConvexQuad A B C D)
    (hA : dist A O = R) (hB : dist B O = R)
    (hC : dist C O = R) (hD : dist D O = R)
    (hincircle : BlindIncircle A B C D I r),
    1 / (R - dist O I) ^ 2 + 1 / (R + dist O I) ^ 2 = 1 / r ^ 2

/-! ## Coordinate facts (re-proved from Mathlib) -/

section Coord
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (e : OrthonormalBasis (Fin 2) ℝ V)

theorem onb_exists (h : Module.finrank ℝ V = 2) : Nonempty (OrthonormalBasis (Fin 2) ℝ V) := by
  have : Fact (Module.finrank ℝ V = 2) := ⟨h⟩
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  exact ⟨(stdOrthonormalBasis ℝ V).reindex (finCongr h)⟩

theorem eqc (w : V) : w = ⟪w, e 0⟫ • e 0 + ⟪w, e 1⟫ • e 1 := by
  have h := e.sum_repr' w
  rw [Fin.sum_univ_two] at h
  rw [real_inner_comm w (e 0), real_inner_comm w (e 1)] at h
  exact h.symm

theorem extc {w z : V} (h0 : ⟪w, e 0⟫ = ⟪z, e 0⟫) (h1 : ⟪w, e 1⟫ = ⟪z, e 1⟫) : w = z := by
  rw [eqc e w, eqc e z, h0, h1]

theorem innerc (w z : V) : ⟪w, z⟫ = ⟪w, e 0⟫ * ⟪z, e 0⟫ + ⟪w, e 1⟫ * ⟪z, e 1⟫ := by
  have h := e.sum_inner_mul_inner w z
  rw [Fin.sum_univ_two] at h
  rw [← h, real_inner_comm (e 0) z, real_inner_comm (e 1) z]

theorem normc (w : V) : ‖w‖ ^ 2 = ⟪w, e 0⟫ ^ 2 + ⟪w, e 1⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, innerc e]; ring

theorem bc_smul_right (w z : V) (r : ℝ) : BlindCross e w (r • z) = r * BlindCross e w z := by
  simp only [BlindCross, real_inner_smul_left]; ring

theorem bc_sub_right (w z y : V) : BlindCross e w (z - y) = BlindCross e w z - BlindCross e w y := by
  simp only [BlindCross, inner_sub_left]; ring

theorem bc_self (w : V) : BlindCross e w w = 0 := by simp only [BlindCross]; ring

theorem bc_zero_left (w : V) : BlindCross e 0 w = 0 := by simp [BlindCross]

theorem eq_smul_of_bc {w z : V} (hw : w ≠ 0) (h : BlindCross e w z = 0) :
    ∃ r : ℝ, z = r • w := by
  have hn : ‖w‖ ^ 2 ≠ 0 := by positivity
  rw [normc e] at hn
  refine ⟨(⟪w, e 0⟫ * ⟪z, e 0⟫ + ⟪w, e 1⟫ * ⟪z, e 1⟫) / (⟪w, e 0⟫ ^ 2 + ⟪w, e 1⟫ ^ 2), ?_⟩
  unfold BlindCross at h
  apply extc e
  · rw [real_inner_smul_left]; field_simp; linear_combination (-⟪w, e 1⟫) * h
  · rw [real_inner_smul_left]; field_simp; linear_combination (⟪w, e 0⟫) * h

end Coord

section Affine
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] (e : OrthonormalBasis (Fin 2) ℝ V)

theorem mem_line_iff' {X Y Z : P} (h : X ≠ Y) :
    Z ∈ line[ℝ, X, Y] ↔ BlindCross e (Y -ᵥ X) (Z -ᵥ X) = 0 := by
  constructor
  · intro hZ
    obtain ⟨r, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hZ
    rw [AffineMap.lineMap_vsub_left, bc_smul_right, bc_self, mul_zero]
  · intro hc
    obtain ⟨r, hr⟩ := eq_smul_of_bc e (vsub_ne_zero.2 h.symm) hc
    rw [← vsub_vadd Z X, hr]
    exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

theorem sSameSide_iff' {X Y : P} (h : X ≠ Y) (Z W : P) :
    line[ℝ, X, Y].SSameSide Z W ↔
      0 < BlindCross e (Y -ᵥ X) (Z -ᵥ X) * BlindCross e (Y -ᵥ X) (W -ᵥ X) := by
  rw [AffineSubspace.sSameSide_iff_exists_left (left_mem_affineSpan_pair ℝ X Y)]
  constructor
  · rintro ⟨hZ, hW, p₂, hp₂, hray⟩
    have cZ : BlindCross e (Y -ᵥ X) (Z -ᵥ X) ≠ 0 := fun h0 => hZ ((mem_line_iff' e h).2 h0)
    have cW : BlindCross e (Y -ᵥ X) (W -ᵥ X) ≠ 0 := fun h0 => hW ((mem_line_iff' e h).2 h0)
    have c2 := (mem_line_iff' e h).1 hp₂
    rcases hray with h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, heq⟩
    · exact absurd (by rw [h0]; simp [BlindCross]) cZ
    · rw [vsub_eq_zero_iff_eq] at h0
      exact absurd (h0 ▸ hp₂) hW
    · have := congrArg (BlindCross e (Y -ᵥ X)) heq
      rw [bc_smul_right, bc_smul_right, ← vsub_sub_vsub_cancel_right W p₂ X,
        bc_sub_right, c2, sub_zero] at this
      have hpos : 0 < r₂ * BlindCross e (Y -ᵥ X) (W -ᵥ X) ^ 2 := by positivity
      have : 0 < r₁ * (BlindCross e (Y -ᵥ X) (Z -ᵥ X) * BlindCross e (Y -ᵥ X) (W -ᵥ X)) := by
        rw [← mul_assoc, this]; linarith [hpos]
      exact (mul_pos_iff_of_pos_left hr₁).1 this
  · intro hpos
    have cZ : BlindCross e (Y -ᵥ X) (Z -ᵥ X) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hpos; exact lt_irrefl _ hpos
    have cW : BlindCross e (Y -ᵥ X) (W -ᵥ X) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
    refine ⟨fun h0 => cZ ((mem_line_iff' e h).1 h0), fun h0 => cW ((mem_line_iff' e h).1 h0), ?_⟩
    set s := BlindCross e (Y -ᵥ X) (W -ᵥ X) / BlindCross e (Y -ᵥ X) (Z -ᵥ X)
    have hs : 0 < s := by
      have : s = BlindCross e (Y -ᵥ X) (Z -ᵥ X) * BlindCross e (Y -ᵥ X) (W -ᵥ X) /
          BlindCross e (Y -ᵥ X) (Z -ᵥ X) ^ 2 := by
        simp only [s]; field_simp
      rw [this]; positivity
    refine ⟨(-s) • (Z -ᵥ X) +ᵥ W, (mem_line_iff' e h).2 ?_, ?_⟩
    · rw [vadd_vsub_assoc]
      have : BlindCross e (Y -ᵥ X) ((-s) • (Z -ᵥ X) + (W -ᵥ X)) =
          -s * BlindCross e (Y -ᵥ X) (Z -ᵥ X) + BlindCross e (Y -ᵥ X) (W -ᵥ X) := by
        simp only [BlindCross, inner_add_left, real_inner_smul_left]; ring
      rw [this]; simp only [s]; field_simp; ring
    · rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, ← neg_smul, neg_neg]
      exact SameRay.sameRay_pos_smul_right _ hs

/-- The blind same-side predicate is the strict same side of Mathlib, for a proper side line. -/
theorem sameSide_iff {X Y : P} (hV : Module.finrank ℝ V = 2) (h : X ≠ Y) (Z W : P) :
    line[ℝ, X, Y].SSameSide Z W ↔ BlindSameSide X Y Z W := by
  obtain ⟨e⟩ := onb_exists hV (V := V)
  constructor
  · intro hs; exact ⟨e, (sSameSide_iff' e h Z W).1 hs⟩
  · rintro ⟨e', he'⟩; exact (sSameSide_iff' e' h Z W).2 he'

theorem ne_of_blindSameSide {X Y Z W : P} (h : BlindSameSide X Y Z W) : X ≠ Y := by
  rintro rfl
  obtain ⟨e, he⟩ := h
  rw [vsub_self, bc_zero_left, zero_mul] at he
  exact lt_irrefl _ he

theorem sSameSide_of_blind {X Y Z W : P} (h : BlindSameSide X Y Z W) :
    line[ℝ, X, Y].SSameSide Z W := by
  obtain ⟨e, he⟩ := h
  exact (sSameSide_iff' e (ne_of_blindSameSide ⟨e, he⟩) Z W).2 he

theorem not_col_ne {A B C : P} (h : ¬ Collinear ℝ ({A, B, C} : Set P)) :
    A ≠ B ∧ B ≠ C ∧ A ≠ C := by
  refine ⟨?_, ?_, ?_⟩ <;> intro he <;> apply h
  · rw [he, Set.insert_eq_of_mem (Set.mem_insert _ _)]; exact collinear_pair ℝ _ _
  · rw [he, Set.pair_eq_singleton]; exact collinear_pair ℝ _ _
  · rw [he, Set.insert_eq_of_mem (Set.mem_insert_of_mem _ (Set.mem_singleton _))]
    exact collinear_pair ℝ _ _

omit [MetricSpace P] in
theorem set3_eq₁ (A B C : P) : ({B, A, C} : Set P) = {A, B, C} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

omit [MetricSpace P] in
theorem set3_eq₂ (A B C : P) : ({C, A, B} : Set P) = {A, B, C} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- Convexity: the blind definition (with the plane hypothesis) is the library's `ConvexQuad`. -/
theorem convex_iff {A B C D : P} (hV : Module.finrank ℝ V = 2) :
    BlindConvexQuad A B C D ↔ Quadrilaterals.ConvexQuad A B C D := by
  unfold BlindConvexQuad Quadrilaterals.ConvexQuad
  constructor
  · rintro ⟨-, hnc, X, t, u, ht, hu, hX1, hX2⟩
    obtain ⟨-, -, hAC⟩ := not_col_ne hnc
    have hBD : B ≠ D := by
      rintro rfl
      rw [vsub_self, smul_zero, zero_vadd] at hX2
      subst hX2
      apply hnc
      rw [← set3_eq₁]
      apply collinear_insert_of_mem_affineSpan_pair
      rw [hX1]; exact smul_vsub_vadd_mem_affineSpan_pair _ _ _
    refine ⟨⟨X, ?_, ?_⟩, hnc⟩
    · rw [sbtw_iff_mem_image_Ioo_and_ne]
      exact ⟨⟨t, ht, by rw [AffineMap.lineMap_apply, hX1]⟩, hAC⟩
    · rw [sbtw_iff_mem_image_Ioo_and_ne]
      exact ⟨⟨u, hu, by rw [AffineMap.lineMap_apply, hX2]⟩, hBD⟩
  · rintro ⟨⟨X, h1, h2⟩, hnc⟩
    rw [sbtw_iff_mem_image_Ioo_and_ne] at h1 h2
    obtain ⟨⟨t, ht, hX1⟩, -⟩ := h1
    obtain ⟨⟨u, hu, hX2⟩, -⟩ := h2
    rw [AffineMap.lineMap_apply] at hX1 hX2
    exact ⟨hV, hnc, X, t, u, ht, hu, hX1.symm, hX2.symm⟩

/-- The four sides of a convex quadrilateral are non-degenerate (pure affine algebra). -/
theorem convex_sides_ne {A B C D : P} (h : Quadrilaterals.ConvexQuad A B C D) :
    A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A := by
  obtain ⟨⟨X, h1, h2⟩, hnc⟩ := h
  obtain ⟨hAB, hBC, -⟩ := not_col_ne hnc
  rw [sbtw_iff_mem_image_Ioo_and_ne] at h1 h2
  obtain ⟨⟨t, ⟨ht0, ht1⟩, hX1⟩, -⟩ := h1
  obtain ⟨⟨u, ⟨hu0, hu1⟩, hX2⟩, -⟩ := h2
  rw [AffineMap.lineMap_apply] at hX1 hX2
  have e1 : X -ᵥ A = t • (C -ᵥ A) := by rw [← hX1, vadd_vsub]
  have e2 : X -ᵥ A = u • ((D -ᵥ A) - (B -ᵥ A)) + (B -ᵥ A) := by
    rw [← hX2, vadd_vsub_assoc, vsub_sub_vsub_cancel_right]
  refine ⟨hAB, hBC, ?_, ?_⟩
  · intro hCD
    rw [← hCD] at e2
    have h1u : (1 - u) ≠ 0 := by linarith
    have key : (1 - u) • (B -ᵥ A) = (t - u) • (C -ᵥ A) := by
      rw [sub_smul, sub_smul, one_smul, ← e1, e2]; module
    have hb : B -ᵥ A = ((t - u) / (1 - u)) • (C -ᵥ A) := by
      rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ h1u, one_smul]
    have hm : B ∈ line[ℝ, A, C] := by
      rw [← vsub_vadd B A, hb]; exact smul_vsub_vadd_mem_affineSpan_pair _ _ _
    apply hnc
    rw [← set3_eq₁]; exact collinear_insert_of_mem_affineSpan_pair hm
  · intro hDA
    rw [hDA, vsub_self, zero_sub] at e2
    have ht : t ≠ 0 := ht0.ne'
    have key : t • (C -ᵥ A) = (1 - u) • (B -ᵥ A) := by
      rw [← e1, e2]; module
    have hc : C -ᵥ A = ((1 - u) / t) • (B -ᵥ A) := by
      rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ ht, one_smul]
    have hm : C ∈ line[ℝ, A, B] := by
      rw [← vsub_vadd C A, hc]; exact smul_vsub_vadd_mem_affineSpan_pair _ _ _
    apply hnc
    rw [← set3_eq₂]; exact collinear_insert_of_mem_affineSpan_pair hm

/-- Incircle: with non-degenerate sides, the blind definition is the library's `IsIncircle`. -/
theorem incircle_iff {A B C D I : P} {r : ℝ} (hV : Module.finrank ℝ V = 2)
    (hs : A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A) :
    BlindIncircle A B C D I r ↔ Quadrilaterals.IsIncircle A B C D I r := by
  obtain ⟨n1, n2, n3, n4⟩ := hs
  unfold BlindIncircle Quadrilaterals.IsIncircle BlindLineDistance BlindSideLine
  rw [← sameSide_iff hV n1, ← sameSide_iff hV n2, ← sameSide_iff hV n3, ← sameSide_iff hV n4]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨hV, h⟩

theorem quadArea_eq (A B C D : P) :
    BlindQuadArea A B C D = Quadrilaterals.quadArea A B C D := by
  simp only [BlindQuadArea, BlindTriangleAreaBAC, BlindTriangleAreaCAD, Quadrilaterals.quadArea,
    Quadrilaterals.triArea]
  ring

theorem semi_eq (A B C D : P) :
    BlindSemiperimeter A B C D = Quadrilaterals.semiperimeter A B C D := by
  simp only [BlindSemiperimeter, Quadrilaterals.semiperimeter]; ring

/-! Van Aubel: orientation ↔ orthonormal basis. -/

theorem areaForm_eq [Fact (Module.finrank ℝ V = 2)] (x y : V) :
    (e.toBasis.orientation).areaForm x y = BlindCross e x y := by
  rw [Orientation.areaForm_to_volumeForm, Orientation.volumeForm_robust _ e rfl,
    Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    BlindCross, real_inner_comm (e 0), real_inner_comm (e 1)]
  ring

theorem rot_eq [Fact (Module.finrank ℝ V = 2)] (σ : ℝ) (x : V) :
    (e.toBasis.orientation).rotation ((-(σ * (Real.pi / 2)) : ℝ) : Real.Angle) x =
      BlindVanAubelRotation e σ x := by
  have h : -σ * Real.pi / 2 = -(σ * (Real.pi / 2)) := by ring
  rw [BlindVanAubelRotation, h, Orientation.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
  apply extc e
  · simp only [inner_add_left, real_inner_smul_left, Orientation.inner_rightAngleRotation_left,
      areaForm_eq, BlindCross, OrthonormalBasis.inner_eq_ite]
    simp
  · simp only [inner_add_left, real_inner_smul_left, Orientation.inner_rightAngleRotation_left,
      areaForm_eq, BlindCross, OrthonormalBasis.inner_eq_ite]
    simp
    ring

theorem center_eq [Fact (Module.finrank ℝ V = 2)] (A B C D X Y : P) :
    Quadrilaterals.squareCenter e.toBasis.orientation A B C D X Y =
      BlindVanAubelCenter e A B C D X Y := by
  have hs : Quadrilaterals.quadSign e.toBasis.orientation A B C D = BlindVanAubelSign e A B C D := by
    simp only [Quadrilaterals.quadSign, BlindVanAubelSign, areaForm_eq, gt_iff_lt]
  rw [Quadrilaterals.squareCenter, BlindVanAubelCenter, hs, rot_eq]

end Affine

/-! ## Comparisons -/

section Comparisons

-- thm:bretschneider : blind_1 ↔ bretschneider
theorem r1_to_b : type_of% @Quadrilaterals.bretschneider.{u, v} → blind1_stmt.{u, v} := by
  intro hR V P _ _ _ _ A B C D hplane hconv
  have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
  have := hR ((convex_iff hplane).1 hconv)
  simpa only [quadArea_eq, semi_eq, BlindSideAB, BlindSideBC, BlindSideCD, BlindSideDA] using this

theorem b1_to_r : blind1_stmt.{u, v} → type_of% @Quadrilaterals.bretschneider.{u, v} := by
  intro hB V P _ _ _ _ hF A B C D hconv
  have := hB A B C D hF.out ((convex_iff hF.out).2 hconv)
  simpa only [quadArea_eq, semi_eq, BlindSideAB, BlindSideBC, BlindSideCD, BlindSideDA] using this

-- thm:brahmagupta : blind_2 ↔ brahmagupta
theorem r2_to_b : type_of% @Quadrilaterals.brahmagupta.{u, v} → blind2_stmt.{u, v} := by
  intro hR V P _ _ _ _ A B C D hplane hconv hcyc
  have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
  have := hR ((convex_iff hplane).1 hconv) hcyc
  simpa only [quadArea_eq, semi_eq, BlindSideAB, BlindSideBC, BlindSideCD, BlindSideDA] using this

theorem b2_to_r : blind2_stmt.{u, v} → type_of% @Quadrilaterals.brahmagupta.{u, v} := by
  intro hB V P _ _ _ _ hF A B C D hconv hcyc
  have := hB A B C D hF.out ((convex_iff hF.out).2 hconv) hcyc
  simpa only [quadArea_eq, semi_eq, BlindSideAB, BlindSideBC, BlindSideCD, BlindSideDA] using this

-- thm:pitot : blind_3 ↔ pitot
theorem r3_to_b : type_of% @Quadrilaterals.pitot.{u, v} → blind3_stmt.{u, v} := by
  intro hR V P _ _ _ _ A B C D hplane hconv htan
  have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
  have hc := (convex_iff hplane).1 hconv
  obtain ⟨I, r, hI⟩ := htan
  exact hR hc ⟨I, r, (incircle_iff hplane (convex_sides_ne hc)).1 hI⟩

theorem b3_to_r : blind3_stmt.{u, v} → type_of% @Quadrilaterals.pitot.{u, v} := by
  intro hB V P _ _ _ _ hF A B C D hconv htan
  obtain ⟨I, r, hI⟩ := htan
  exact hB A B C D hF.out ((convex_iff hF.out).2 hconv)
    ⟨I, r, (incircle_iff hF.out (convex_sides_ne hconv)).2 hI⟩

-- thm:pitot (converse) : blind_4 ↔ pitot_converse
theorem r4_to_b : type_of% @Quadrilaterals.pitot_converse.{u, v} → blind4_stmt.{u, v} := by
  intro hR V P _ _ _ _ A B C D hplane hconv hsides
  have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
  have hc := (convex_iff hplane).1 hconv
  obtain ⟨I, r, hI⟩ := hR hc hsides
  exact ⟨I, r, (incircle_iff hplane (convex_sides_ne hc)).2 hI⟩

theorem b4_to_r : blind4_stmt.{u, v} → type_of% @Quadrilaterals.pitot_converse.{u, v} := by
  intro hB V P _ _ _ _ hF A B C D hconv hsides
  obtain ⟨I, r, hI⟩ := hB A B C D hF.out ((convex_iff hF.out).2 hconv) hsides
  exact ⟨I, r, (incircle_iff hF.out (convex_sides_ne hconv)).1 hI⟩

-- thm:euler4 : blind_5 ↔ euler_quadrilateral
theorem r5_to_b : type_of% @Quadrilaterals.euler_quadrilateral.{u, v} → blind5_stmt.{u, v} := by
  intro hR V P _ _ _ _ A B C D hplane
  have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
  exact hR A B C D

theorem b5_to_r : blind5_stmt.{u, v} → type_of% @Quadrilaterals.euler_quadrilateral.{u, v} := by
  intro hB V P _ _ _ _ hF A B C D
  exact hB A B C D hF.out

-- thm:ptolemy2 : blind_6 ↔ ptolemy_second
theorem r6_to_b : type_of% @Quadrilaterals.ptolemy_second.{u, v} → blind6_stmt.{u, v} := by
  intro hR V P _ _ _ _ A B C D hplane hconv hcyc
  have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
  exact hR ((convex_iff hplane).1 hconv) hcyc

theorem b6_to_r : blind6_stmt.{u, v} → type_of% @Quadrilaterals.ptolemy_second.{u, v} := by
  intro hB V P _ _ _ _ hF A B C D hconv hcyc
  exact hB A B C D hF.out ((convex_iff hF.out).2 hconv) hcyc

-- thm:vanaubel : blind_7 ∧ blind_8 ↔ van_aubel
theorem r78_to_b : type_of% @Quadrilaterals.van_aubel.{u, v} → blind7_stmt.{u, v} ∧ blind8_stmt.{u, v} := by
  intro hR
  constructor
  · intro V P _ _ _ _ A B C D e hplane
    have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
    have := (hR e.toBasis.orientation A B C D).1
    simpa only [center_eq] using this
  · intro V P _ _ _ _ A B C D e hplane
    have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
    have := (hR e.toBasis.orientation A B C D).2
    simpa only [center_eq] using this

theorem b78_to_r : blind7_stmt.{u, v} ∧ blind8_stmt.{u, v} → type_of% @Quadrilaterals.van_aubel.{u, v} := by
  rintro ⟨h7, h8⟩ V P _ _ _ _ hF o A B C D
  set e := o.finOrthonormalBasis (by norm_num) hF.out
  have ho : e.toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
  rw [← ho]
  simp only [center_eq]
  exact ⟨h7 A B C D e hF.out, h8 A B C D e hF.out⟩

-- thm:newton : blind_9 ↔ newton_line
theorem r9_to_b : type_of% @Quadrilaterals.newton_line.{u, v} → blind9_stmt.{u, v} := by
  intro hR V P _ _ _ _ A B C D I r hplane hconv hI
  have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
  have hc := (convex_iff hplane).1 hconv
  exact hR hc ((incircle_iff hplane (convex_sides_ne hc)).1 hI)

theorem b9_to_r : blind9_stmt.{u, v} → type_of% @Quadrilaterals.newton_line.{u, v} := by
  intro hB V P _ _ _ _ hF A B C D I r hconv hI
  exact hB A B C D I r hF.out ((convex_iff hF.out).2 hconv)
    ((incircle_iff hF.out (convex_sides_ne hconv)).2 hI)

-- thm:fuss : blind_10 ↔ fuss
theorem r10_to_b : type_of% @Quadrilaterals.fuss.{u, v} → blind10_stmt.{u, v} := by
  intro hR V P _ _ _ _ A B C D O I R r hplane hconv hA hB hC hD hI
  have : Fact (Module.finrank ℝ V = 2) := ⟨hplane⟩
  have hc := (convex_iff hplane).1 hconv
  exact hR hc hA hB hC hD ((incircle_iff hplane (convex_sides_ne hc)).1 hI)

theorem b10_to_r : blind10_stmt.{u, v} → type_of% @Quadrilaterals.fuss.{u, v} := by
  intro hB V P _ _ _ _ hF A B C D O I R r hconv hA hB' hC hD hI
  exact hB A B C D O I R r hF.out ((convex_iff hF.out).2 hconv) hA hB' hC hD
    ((incircle_iff hF.out (convex_sides_ne hconv)).2 hI)

end Comparisons


end L13JQ

/-! ## Audit: no theorem of the paper's library occurs in any proof term of this file.
Collects, for every declaration of namespace `NS` defined in this file, all constants occurring
(transitively through other declarations of this file) in its value, and reports those that are
theorems of the library namespace `LIB`. The `type_of%` goals are types, not values, so library
theorem names there are not counted. Expected output: `library theorems used: []`. (Self-tested: a
declaration `(CircleSystems.johnson_reflection H O₁ O₂ O₃).1` IS reported.) -/
open Lean Meta Elab Command in
elab "#audit_lib " ns:ident lib:ident : command => do
  let env ← getEnv
  let nsN := ns.getId
  let libN := lib.getId
  let mine := env.constants.map₂.foldl (fun acc n _ => if nsN.isPrefixOf n then acc.push n else acc) #[]
  let mut bad : Array (Name × Name) := #[]
  let mut aux : Array Name := #[]
  for n in mine do
    let some ci := env.find? n | continue
    let some v := ci.value? (allowOpaque := true) | continue
    for c in v.getUsedConstants do
      if libN.isPrefixOf c then
        if let some (.thmInfo _) := env.find? c then
          -- compiler-generated pieces of a library *definition* (side proofs `_proof_N`,
          -- equation lemmas `eq_N` / `eq_def` used by `rw [def]`) count as unfolding it.
          let isDefAux : Bool := match c with
            | .str p s =>
              (s.startsWith "_proof_" || s.startsWith "eq_") &&
                (match env.find? p with | some (.defnInfo _) => true | _ => false)
            | _ => false
          if isDefAux then aux := aux.push c else bad := bad.push (n, c)
  logInfo m!"checked {mine.size} declarations; definition auxiliaries (unfolding only): {aux.toList.eraseDups}; library theorems used: {bad.toList}"

#audit_lib L13JQ Quadrilaterals

#print axioms L13JQ.r1_to_b
#print axioms L13JQ.b1_to_r
#print axioms L13JQ.r2_to_b
#print axioms L13JQ.b2_to_r
#print axioms L13JQ.r3_to_b
#print axioms L13JQ.b3_to_r
#print axioms L13JQ.r4_to_b
#print axioms L13JQ.b4_to_r
#print axioms L13JQ.r5_to_b
#print axioms L13JQ.b5_to_r
#print axioms L13JQ.r6_to_b
#print axioms L13JQ.b6_to_r
#print axioms L13JQ.r78_to_b
#print axioms L13JQ.b78_to_r
#print axioms L13JQ.r9_to_b
#print axioms L13JQ.b9_to_r
#print axioms L13JQ.r10_to_b
#print axioms L13JQ.b10_to_r
