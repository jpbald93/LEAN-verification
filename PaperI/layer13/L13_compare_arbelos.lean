import Arbelos

/-!
# Layer 13 comparison (machine john): blind statements vs the `Arbelos` library

Blind definitions are copied verbatim from `PaperIBlind.lean` (namespace `L13CmpArb`).
Each `blindK_stmt` is the blind theorem `blind_K` with its proof placeholder removed and the
proposition and all variables universally quantified. Real statements are referenced via
`type_of%` only; no library theorem is used in any proof body (library *definitions* are
unfolded where needed).
-/

noncomputable section
open scoped RealInnerProductSpace
open Set Metric MeasureTheory EuclideanGeometry

namespace L13CmpArb

/-! ## Verbatim blind definitions -/

def BlindCircle : Type := ℂ × ℝ

def BlindCirclePoints (c : BlindCircle) : Set ℂ :=
  {z | dist z c.1 = c.2}

def BlindDisk (c : BlindCircle) : Set ℂ :=
  {z | dist z c.1 ≤ c.2}

def BlindCircleInterior (c : BlindCircle) : Set ℂ :=
  {z | dist z c.1 < c.2}

def BlindPower (z : ℂ) (c : BlindCircle) : ℝ :=
  dist z c.1 ^ 2 - c.2 ^ 2

def BlindExternallyTangent (c d : BlindCircle) : Prop :=
  c.2 > 0 ∧ d.2 > 0 ∧ dist c.1 d.1 = c.2 + d.2

def BlindInternallyTangent (inner outer : BlindCircle) : Prop :=
  inner.2 > 0 ∧ outer.2 > 0 ∧
    dist inner.1 outer.1 + inner.2 = outer.2

def BlindDiameterCircle (a b : ℝ) : BlindCircle :=
  ((((a + b) / 2 : ℝ) : ℂ), (b - a) / 2)

def BlindArbelosOuterCircle (a c : ℝ) : BlindCircle :=
  BlindDiameterCircle a c

def BlindArbelosLeftCircle (a b : ℝ) : BlindCircle :=
  BlindDiameterCircle a b

def BlindArbelosRightCircle (b c : ℝ) : BlindCircle :=
  BlindDiameterCircle b c

def BlindArbelos (a b c : ℝ) : Set ℂ :=
  {z | a < b ∧ b < c ∧ 0 ≤ z.im ∧
    z ∈ BlindDisk (BlindArbelosOuterCircle a c) ∧
    z ∉ BlindCircleInterior (BlindArbelosLeftCircle a b) ∧
    z ∉ BlindCircleInterior (BlindArbelosRightCircle b c)}

def BlindArchimedesTwinCircle (a b c : ℝ) (left : Bool)
    (circle : BlindCircle) : Prop :=
  a < b ∧ b < c ∧ circle.1.im > 0 ∧
    BlindInternallyTangent circle (BlindArbelosOuterCircle a c) ∧
    BlindExternallyTangent circle
      (if left then BlindArbelosLeftCircle a b
       else BlindArbelosRightCircle b c) ∧
    |circle.1.re - b| = circle.2

def BlindArchimedesTwins (a b c : ℝ) (left right : BlindCircle) : Prop :=
  BlindArchimedesTwinCircle a b c true left ∧
    BlindArchimedesTwinCircle a b c false right

def BlindSteinerChain (inner outer : BlindCircle) (n : ℕ)
    (chain : ℕ → BlindCircle) : Prop :=
  0 < n ∧ inner.2 > 0 ∧ outer.2 > 0 ∧
    dist inner.1 outer.1 + inner.2 < outer.2 ∧
    (∀ i, chain (i + n) = chain i) ∧
    (∀ i, i < n →
      BlindInternallyTangent (chain i) outer ∧
      BlindExternallyTangent (chain i) inner ∧
      BlindExternallyTangent (chain i) (chain ((i + 1) % n)))

def BlindSimpleSteinerChain (inner outer : BlindCircle) (n : ℕ)
    (chain : ℕ → BlindCircle) : Prop :=
  BlindSteinerChain inner outer n chain ∧
    ∀ i j, i < n → j < n → i ≠ j → chain i ≠ chain j

def BlindDisjointSteinerChain (inner outer : BlindCircle) (n : ℕ)
    (chain : ℕ → BlindCircle) : Prop :=
  BlindSteinerChain inner outer n chain ∧
    ∀ i j, i < n → j < n → i ≠ j →
      Disjoint (BlindCircleInterior (chain i)) (BlindCircleInterior (chain j))

def BlindInversion (center : ℂ) (radius : ℝ) (z : ℂ) : ℂ :=
  center + ((radius ^ 2 / ‖z - center‖ ^ 2 : ℝ) : ℂ) * (z - center)

def BlindPappusDenominator (a b t : ℝ) : ℝ :=
  a * (a + b) + t ^ 2 * b ^ 2

def BlindPhi (a b t : ℝ) : BlindCircle :=
  (Complex.mk
      (a * (a + b) * (2 * a + b) / BlindPappusDenominator a b t)
      (2 * a * b * (a + b) * t / BlindPappusDenominator a b t),
    a * b * (a + b) / BlindPappusDenominator a b t)

def BlindPappusCircle (a b : ℝ) (n : ℕ) : BlindCircle :=
  BlindPhi a b n

def BlindInvertedCircle (center : ℂ) (radius : ℝ) (c : BlindCircle) :
    BlindCircle :=
  (center + ((radius ^ 2 / BlindPower center c : ℝ) : ℂ) * (c.1 - center),
    radius ^ 2 * c.2 / BlindPower center c)

/-! ## Bridge lemmas (proved from Mathlib only) -/

/-- A blind circle as a Mathlib sphere. -/
def toS (c : BlindCircle) : Sphere ℂ := ⟨c.1, c.2⟩

theorem bExt_iff (c d : BlindCircle) :
    BlindExternallyTangent c d ↔ 0 < c.2 ∧ 0 < d.2 ∧ (toS c).IsExtTangent (toS d) := by
  rw [Sphere.isExtTangent_iff_dist_center]
  simp only [BlindExternallyTangent, toS, gt_iff_lt]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3, h1.le, h2.le⟩
  · rintro ⟨h1, h2, h3, -, -⟩; exact ⟨h1, h2, h3⟩

theorem bInt_iff (c d : BlindCircle) :
    BlindInternallyTangent c d ↔ 0 < c.2 ∧ 0 < d.2 ∧ (toS c).IsIntTangent (toS d) := by
  rw [Sphere.isIntTangent_iff_dist_center]
  simp only [BlindInternallyTangent, toS, gt_iff_lt]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith, h1.le, h2.le⟩
  · rintro ⟨h1, h2, h3, -, -⟩; exact ⟨h1, h2, by linarith⟩

/-- A Mathlib sphere as a blind circle. -/
def ofS (s : Sphere ℂ) : BlindCircle := (s.center, s.radius)

@[simp] theorem toS_ofS (s : Sphere ℂ) : toS (ofS s) = s := rfl
@[simp] theorem ofS_fst (s : Sphere ℂ) : (ofS s).1 = s.center := rfl
@[simp] theorem ofS_snd (s : Sphere ℂ) : (ofS s).2 = s.radius := rfl
@[simp] theorem toS_center (c : BlindCircle) : (toS c).center = c.1 := rfl
@[simp] theorem toS_radius (c : BlindCircle) : (toS c).radius = c.2 := rfl

theorem diam_big (a b : ℝ) : toS (BlindDiameterCircle 0 (2 * (a + b))) = Arbelos.bigS a b := by
  refine Sphere.ext ?_ ?_
  · show (((0 + 2 * (a + b)) / 2 : ℝ) : ℂ) = ((a + b : ℝ) : ℂ); congr 1; ring
  · show (2 * (a + b) - 0) / 2 = a + b; ring

theorem diam_left (a b : ℝ) : toS (BlindDiameterCircle 0 (2 * a)) = Arbelos.leftS a b := by
  refine Sphere.ext ?_ ?_
  · show (((0 + 2 * a) / 2 : ℝ) : ℂ) = ((a : ℝ) : ℂ); congr 1; ring
  · show (2 * a - 0) / 2 = a; ring

theorem diam_right (a b : ℝ) :
    toS (BlindDiameterCircle (2 * a) (2 * (a + b))) = Arbelos.rightS a b := by
  refine Sphere.ext ?_ ?_
  · show (((2 * a + 2 * (a + b)) / 2 : ℝ) : ℂ) = ((2 * a + b : ℝ) : ℂ); congr 1; ring
  · show (2 * (a + b) - 2 * a) / 2 = b; ring

/-- Re-proof (Mathlib only) of membership in the vertical line. -/
theorem cmp_mem_vline_iff {x₀ : ℝ} {z : ℂ} :
    z ∈ AffineSubspace.mk' (x₀ : ℂ) (ℝ ∙ Complex.I) ↔ z.re = x₀ := by
  rw [AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    have := congrArg Complex.re ht
    simp at this
    linarith
  · intro h
    refine ⟨z.im, ?_⟩
    apply Complex.ext <;> simp [h]

/-- Re-proof (Mathlib only) of tangency of a circle to a vertical line. -/
theorem cmp_isTangent_vline_iff (s : Sphere ℂ) (x₀ : ℝ) :
    s.IsTangent (AffineSubspace.mk' (x₀ : ℂ) (ℝ ∙ Complex.I)) ↔ |s.center.re - x₀| = s.radius := by
  constructor
  · rintro ⟨p, hs, hm, hle⟩
    rw [cmp_mem_vline_iff] at hm
    have hpI : p + Complex.I ∈ AffineSubspace.mk' (x₀ : ℂ) (ℝ ∙ Complex.I) := by
      rw [cmp_mem_vline_iff]; simpa using hm
    have h0 := Sphere.mem_orthRadius_iff_inner_left.1 (hle hpI)
    rw [vsub_eq_sub, vsub_eq_sub, Complex.inner] at h0
    simp at h0
    have hd : dist p s.center = s.radius := hs
    rw [Complex.dist_eq_re_im, hm, show p.im - s.center.im = 0 by linarith, zero_pow two_ne_zero,
      add_zero, Real.sqrt_sq_eq_abs, abs_sub_comm] at hd
    exact hd
  · intro h
    refine ⟨⟨x₀, s.center.im⟩, ?_, ?_, ?_⟩
    · show dist _ _ = _
      rw [Complex.dist_eq_re_im]
      simp [Real.sqrt_sq_eq_abs]
      rw [abs_sub_comm]; exact h
    · rw [cmp_mem_vline_iff]
    · intro x hx
      rw [cmp_mem_vline_iff] at hx
      rw [Sphere.mem_orthRadius_iff_inner_left, vsub_eq_sub, vsub_eq_sub, Complex.inner]
      simp [hx]

theorem perpC_tangent_iff (a b : ℝ) (s : Sphere ℂ) :
    s.IsTangent (Arbelos.perpC a b) ↔ |s.center.re - 2 * a| = s.radius := by
  have : Arbelos.perpC a b = AffineSubspace.mk' (((2 * a : ℝ)) : ℂ) (ℝ ∙ Complex.I) := rfl
  rw [this, cmp_isTangent_vline_iff]

/-! ## thm:twin — `twin_left`, `twin_right` vs `blind_14`, `blind_15` -/

def blind14_stmt : Prop :=
  ∀ (a b : ℝ) (s : BlindCircle), 0 < a → 0 < b → 0 < s.2 →
    |s.1.re - 2 * a| = s.2 → s.1.re < 2 * a →
    BlindInternallyTangent s (BlindDiameterCircle 0 (2 * (a + b))) →
    BlindExternallyTangent s (BlindDiameterCircle 0 (2 * a)) →
    s.2 = a * b / (a + b)

def blind15_stmt : Prop :=
  ∀ (a b : ℝ) (s : BlindCircle), 0 < a → 0 < b → 0 < s.2 →
    |s.1.re - 2 * a| = s.2 → 2 * a < s.1.re →
    BlindInternallyTangent s (BlindDiameterCircle 0 (2 * (a + b))) →
    BlindExternallyTangent s (BlindDiameterCircle (2 * a) (2 * (a + b))) →
    s.2 = a * b / (a + b)

theorem twinL_R_to_B : type_of% @Arbelos.twin_left → blind14_stmt := by
  intro h a b s ha hb hs hl hlt hout hin
  rw [bInt_iff, diam_big] at hout
  rw [bExt_iff, diam_left a b] at hin
  exact h ha hb (toS s) hlt ((perpC_tangent_iff a b _).2 hl) hout.2.2 hin.2.2.symm

theorem twinL_B_to_R : blind14_stmt → type_of% @Arbelos.twin_left := by
  intro h a b ha hb s hside hperp hbig hsmall
  rw [perpC_tangent_iff] at hperp
  have hr : 0 < s.radius := by rw [← hperp, abs_of_neg (by linarith)]; linarith
  have hR : 0 < a + b := by linarith
  refine h a b (ofS s) ha hb hr hperp hside ?_ ?_
  · refine (bInt_iff _ _).2 ⟨hr, by show 0 < (2 * (a + b) - 0) / 2; linarith, ?_⟩
    rw [diam_big, toS_ofS]; exact hbig
  · refine (bExt_iff _ _).2 ⟨hr, by show 0 < (2 * a - 0) / 2; linarith, ?_⟩
    rw [diam_left a b, toS_ofS]; exact hsmall.symm

theorem twinR_R_to_B : type_of% @Arbelos.twin_right → blind15_stmt := by
  intro h a b s ha hb hs hl hlt hout hin
  rw [bInt_iff, diam_big] at hout
  rw [bExt_iff, diam_right] at hin
  exact h ha hb (toS s) hlt ((perpC_tangent_iff a b _).2 hl) hout.2.2 hin.2.2.symm

theorem twinR_B_to_R : blind15_stmt → type_of% @Arbelos.twin_right := by
  intro h a b ha hb s hside hperp hbig hsmall
  rw [perpC_tangent_iff] at hperp
  have hr : 0 < s.radius := by rw [← hperp, abs_of_pos (by linarith)]; linarith
  have hR : 0 < a + b := by linarith
  refine h a b (ofS s) ha hb hr hperp hside ?_ ?_
  · refine (bInt_iff _ _).2 ⟨hr, by show 0 < (2 * (a + b) - 0) / 2; linarith, ?_⟩
    rw [diam_big, toS_ofS]; exact hbig
  · refine (bExt_iff _ _).2 ⟨hr, by show 0 < (2 * (a + b) - 2 * a) / 2; linarith, ?_⟩
    rw [diam_right, toS_ofS]; exact hsmall.symm


/-! ## thm:twin — `twin_left_exists`, `twin_right_exists` vs `blind_16` -/

def blind16_stmt : Prop :=
  ∀ (a b : ℝ), 0 < a → 0 < b →
    ∃ left right : BlindCircle,
      BlindArchimedesTwins 0 (2 * a) (2 * (a + b)) left right ∧
      left.1.re < 2 * a ∧ 2 * a < right.1.re

theorem twinEx_R_to_B :
    (type_of% @Arbelos.twin_left_exists ∧ type_of% @Arbelos.twin_right_exists) →
      blind16_stmt := by
  rintro ⟨hL, hR⟩ a b ha hb
  obtain ⟨sL, hL0, hL1, hL2, hL3, hL4⟩ := hL ha hb
  obtain ⟨sR, hR0, hR1, hR2, hR3, hR4⟩ := hR ha hb
  rw [perpC_tangent_iff] at hL2 hR2
  have hrL : 0 < sL.radius := by rw [← hL2, abs_of_neg (by linarith)]; linarith
  have hrR : 0 < sR.radius := by rw [← hR2, abs_of_pos (by linarith)]; linarith
  have hab : 0 < a + b := by linarith
  refine ⟨ofS sL, ofS sR, ⟨?_, ?_⟩, hL1, hR1⟩
  · simp only [BlindArchimedesTwinCircle, BlindArbelosOuterCircle, BlindArbelosLeftCircle,
      ↓reduceIte]
    refine ⟨by linarith, by linarith, hL0, ?_, ?_, hL2⟩
    · refine (bInt_iff _ _).2 ⟨hrL, by show 0 < (2 * (a + b) - 0) / 2; linarith, ?_⟩
      rw [diam_big, toS_ofS]; exact hL3
    · refine (bExt_iff _ _).2 ⟨hrL, by show 0 < (2 * a - 0) / 2; linarith, ?_⟩
      rw [diam_left a b, toS_ofS]; exact hL4.symm
  · simp only [BlindArchimedesTwinCircle, BlindArbelosOuterCircle, BlindArbelosRightCircle,
      Bool.false_eq_true, ↓reduceIte]
    refine ⟨by linarith, by linarith, hR0, ?_, ?_, hR2⟩
    · refine (bInt_iff _ _).2 ⟨hrR, by show 0 < (2 * (a + b) - 0) / 2; linarith, ?_⟩
      rw [diam_big, toS_ofS]; exact hR3
    · refine (bExt_iff _ _).2 ⟨hrR, by show 0 < (2 * (a + b) - 2 * a) / 2; linarith, ?_⟩
      rw [diam_right, toS_ofS]; exact hR4.symm

theorem twinEx_B_to_R :
    blind16_stmt →
      (type_of% @Arbelos.twin_left_exists ∧ type_of% @Arbelos.twin_right_exists) := by
  intro h
  refine ⟨fun {a b} ha hb ↦ ?_, fun {a b} ha hb ↦ ?_⟩
  · obtain ⟨L, R, ⟨hL, -⟩, hlt, -⟩ := h a b ha hb
    simp only [BlindArchimedesTwinCircle, BlindArbelosOuterCircle, BlindArbelosLeftCircle,
      ↓reduceIte] at hL
    obtain ⟨-, -, h0, hi, he, hab⟩ := hL
    rw [bInt_iff, diam_big] at hi
    rw [bExt_iff, diam_left a b] at he
    exact ⟨toS L, h0, hlt, (perpC_tangent_iff a b _).2 hab, hi.2.2, he.2.2.symm⟩
  · obtain ⟨L, R, ⟨-, hR⟩, -, hlt⟩ := h a b ha hb
    simp only [BlindArchimedesTwinCircle, BlindArbelosOuterCircle, BlindArbelosRightCircle,
      Bool.false_eq_true, ↓reduceIte] at hR
    obtain ⟨-, -, h0, hi, he, hab⟩ := hR
    rw [bInt_iff, diam_big] at hi
    rw [bExt_iff, diam_right] at he
    exact ⟨toS R, h0, hlt, (perpC_tangent_iff a b _).2 hab, hi.2.2, he.2.2.symm⟩

/-! ## thm:area — `arbelos_area` vs `blind_17` -/

def blind17_stmt : Prop :=
  ∀ (a b : ℝ) (D : ℂ), 0 < a → 0 < b →
    D ∈ BlindCirclePoints (BlindDiameterCircle 0 (2 * (a + b))) →
    D.re = 2 * a →
    volume (BlindArbelos 0 (2 * a) (2 * (a + b))) =
      volume (Metric.ball ((((2 * a : ℝ) : ℂ) + D) / 2)
        (dist ((2 * a : ℝ) : ℂ) D / 2))

/-- Mathlib-only: the real axis is Lebesgue-null. -/
theorem cmp_volume_realAxis : volume {z : ℂ | z.im = 0} = 0 := by
  have h : {z : ℂ | z.im = 0} = (LinearMap.ker Complex.imLm : Set ℂ) := by
    ext z; simp
  rw [h]
  refine Measure.addHaar_submodule volume _ ?_
  intro htop
  have : Complex.I ∈ LinearMap.ker Complex.imLm := htop ▸ Submodule.mem_top
  simp at this

/-- The blind (closed, `0 ≤ im`) arbelos and the library's (`0 < im`) region differ by a subset
of the real axis, so they have the same area. -/
theorem volume_blindArbelos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume (BlindArbelos 0 (2 * a) (2 * (a + b))) = volume (Arbelos.arbelosRegion a b) := by
  have e1 : ((0 + 2 * (a + b)) / 2 : ℝ) = a + b := by ring
  have e2 : (2 * (a + b) - 0) / 2 = a + b := by ring
  have e3 : ((0 + 2 * a) / 2 : ℝ) = a := by ring
  have e4 : (2 * a - 0) / 2 = a := by ring
  have e5 : ((2 * a + 2 * (a + b)) / 2 : ℝ) = 2 * a + b := by ring
  have e6 : (2 * (a + b) - 2 * a) / 2 = b := by ring
  have hset : ∀ z, z ∈ BlindArbelos 0 (2 * a) (2 * (a + b)) ↔
      0 ≤ z.im ∧ dist z ((a + b : ℝ) : ℂ) ≤ a + b ∧ a ≤ dist z ((a : ℝ) : ℂ) ∧
        b ≤ dist z ((2 * a + b : ℝ) : ℂ) := by
    intro z
    simp only [BlindArbelos, BlindDisk, BlindCircleInterior, BlindArbelosOuterCircle,
      BlindArbelosLeftCircle, BlindArbelosRightCircle, BlindDiameterCircle, Set.mem_ofPred_eq,
      e1, e2, e3, e4, e5, e6, not_lt]
    constructor
    · rintro ⟨-, -, h⟩; exact h
    · intro h; exact ⟨by linarith, by linarith, h⟩
  have hreg : ∀ z, z ∈ Arbelos.arbelosRegion a b ↔
      0 < z.im ∧ dist z ((a + b : ℝ) : ℂ) ≤ a + b ∧ a ≤ dist z ((a : ℝ) : ℂ) ∧
        b ≤ dist z ((2 * a + b : ℝ) : ℂ) := fun z ↦ Iff.rfl
  apply le_antisymm
  · calc volume (BlindArbelos 0 (2 * a) (2 * (a + b)))
        ≤ volume (Arbelos.arbelosRegion a b ∪ {z : ℂ | z.im = 0}) := by
          apply measure_mono
          intro z hz
          rw [hset] at hz
          rcases hz.1.lt_or_eq with h | h
          · exact Or.inl ((hreg z).2 ⟨h, hz.2⟩)
          · exact Or.inr h.symm
      _ ≤ volume (Arbelos.arbelosRegion a b) + volume {z : ℂ | z.im = 0} := measure_union_le _ _
      _ = volume (Arbelos.arbelosRegion a b) := by rw [cmp_volume_realAxis, add_zero]
  · apply measure_mono
    intro z hz
    rw [hreg] at hz
    exact (hset z).2 ⟨hz.1.le, hz.2⟩

theorem midpoint_eq_div (x y : ℂ) : midpoint ℝ x y = (x + y) / 2 := by
  rw [midpoint_eq_smul_add]
  apply Complex.ext <;> simp <;> ring

theorem area_hyps {a b : ℝ} (D : ℂ) :
    (D ∈ BlindCirclePoints (BlindDiameterCircle 0 (2 * (a + b))) ↔ D ∈ Arbelos.bigS a b) ∧
      (D.re = 2 * a ↔ D ∈ Arbelos.perpC a b) := by
  have e1 : ((0 + 2 * (a + b)) / 2 : ℝ) = a + b := by ring
  have e2 : (2 * (a + b) - 0) / 2 = a + b := by ring
  refine ⟨?_, ?_⟩
  · simp only [BlindCirclePoints, BlindDiameterCircle, Set.mem_ofPred_eq, e1, e2,
      EuclideanGeometry.mem_sphere, Arbelos.bigS]
  · exact (cmp_mem_vline_iff).symm

theorem area_R_to_B : type_of% @Arbelos.arbelos_area → blind17_stmt := by
  intro h a b D ha hb hD hre
  rw [volume_blindArbelos ha hb, h ha hb D ((area_hyps D).1.1 hD) ((area_hyps D).2.1 hre),
    Arbelos.ptC, midpoint_eq_div]

theorem area_B_to_R : blind17_stmt → type_of% @Arbelos.arbelos_area := by
  intro h a b ha hb D hD hDp
  rw [← volume_blindArbelos ha hb, h a b D ha hb ((area_hyps D).1.2 hD) ((area_hyps D).2.2 hDp),
    Arbelos.ptC, midpoint_eq_div]

/-! ## thm:pappus — `pappus_chain` vs `blind_22` / `blind_26` -/

def blind22_stmt : Prop :=
  ∀ (a b : ℝ) (n : ℕ), 0 < a → 0 < b →
    (BlindPappusCircle a b n).1.im = (n : ℝ) * (2 * (BlindPappusCircle a b n).2)

def blind26_stmt : Prop :=
  ∀ (a b t : ℝ), (BlindPhi a b t).1.im = t * (2 * (BlindPhi a b t).2)

theorem pappusChain_R_to_B22 : type_of% @Arbelos.pappus_chain → blind22_stmt :=
  fun h a b n _ _ ↦ h (a := a) (b := b) n

theorem pappusChain_B26_to_R : blind26_stmt → type_of% @Arbelos.pappus_chain :=
  fun h {a b} n ↦ h a b n

/-! ## thm:pappus — `pappus_tangent_big/left/succ` vs `blind_19/20/21` -/

def blind19_stmt : Prop :=
  ∀ (a b : ℝ) (n : ℕ), 0 < a → 0 < b →
    BlindInternallyTangent (BlindPappusCircle a b n) (BlindDiameterCircle 0 (2 * (a + b)))

def blind20_stmt : Prop :=
  ∀ (a b : ℝ) (n : ℕ), 0 < a → 0 < b →
    BlindExternallyTangent (BlindPappusCircle a b n) (BlindDiameterCircle 0 (2 * a))

def blind21_stmt : Prop :=
  ∀ (a b : ℝ) (n : ℕ), 0 < a → 0 < b →
    BlindExternallyTangent (BlindPappusCircle a b n) (BlindPappusCircle a b (n + 1))

theorem toS_pappus (a b : ℝ) (n : ℕ) :
    toS (BlindPappusCircle a b n) = Arbelos.pappusCircle a b n := rfl

/-- Side condition of the blind tangency convention (radii > 0), by unfolding + `positivity`. -/
theorem pappus_rad_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    0 < (BlindPappusCircle a b n).2 := by
  show 0 < a * b * (a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)
  positivity

theorem pappusT_R_to_B :
    (type_of% @Arbelos.pappus_tangent_big ∧ type_of% @Arbelos.pappus_tangent_left ∧
      type_of% @Arbelos.pappus_tangent_succ) →
      (blind19_stmt ∧ blind20_stmt ∧ blind21_stmt) := by
  rintro ⟨h1, h2, h3⟩
  refine ⟨fun a b n ha hb ↦ ?_, fun a b n ha hb ↦ ?_, fun a b n ha hb ↦ ?_⟩
  · refine (bInt_iff _ _).2 ⟨pappus_rad_pos ha hb n,
      by show 0 < (2 * (a + b) - 0) / 2; linarith, ?_⟩
    rw [diam_big, toS_pappus]; exact h1 ha hb n
  · refine (bExt_iff _ _).2 ⟨pappus_rad_pos ha hb n, by show 0 < (2 * a - 0) / 2; linarith, ?_⟩
    rw [diam_left a b, toS_pappus]; exact (h2 ha hb n).symm
  · refine (bExt_iff _ _).2 ⟨pappus_rad_pos ha hb n, pappus_rad_pos ha hb (n + 1), ?_⟩
    rw [toS_pappus, toS_pappus]; exact h3 ha hb n

theorem pappusT_B_to_R :
    (blind19_stmt ∧ blind20_stmt ∧ blind21_stmt) →
      (type_of% @Arbelos.pappus_tangent_big ∧ type_of% @Arbelos.pappus_tangent_left ∧
        type_of% @Arbelos.pappus_tangent_succ) := by
  rintro ⟨h1, h2, h3⟩
  refine ⟨fun {a b} ha hb n ↦ ?_, fun {a b} ha hb n ↦ ?_, fun {a b} ha hb n ↦ ?_⟩
  · have := ((bInt_iff _ _).1 (h1 a b n ha hb)).2.2
    rwa [diam_big, toS_pappus] at this
  · have := ((bExt_iff _ _).1 (h2 a b n ha hb)).2.2
    rw [diam_left a b, toS_pappus] at this; exact this.symm
  · have := ((bExt_iff _ _).1 (h3 a b n ha hb)).2.2
    rwa [toS_pappus, toS_pappus] at this

/-! ## thm:pappus — `pappus_unique` vs `blind_24` -/

def blind24_stmt : Prop :=
  ∀ (a b : ℝ) (chain : ℕ → BlindCircle), 0 < a → 0 < b →
    (∀ n, 0 < (chain n).2) →
    chain 0 = BlindDiameterCircle (2 * a) (2 * (a + b)) →
    (∀ n, BlindInternallyTangent (chain n) (BlindDiameterCircle 0 (2 * (a + b)))) →
    (∀ n, BlindExternallyTangent (chain n) (BlindDiameterCircle 0 (2 * a))) →
    (∀ n, BlindExternallyTangent (chain n) (chain (n + 1))) →
    (∀ n, chain (n + 2) ≠ chain n) →
    0 < (chain 1).1.im →
    ∀ n, chain n = BlindPappusCircle a b n

theorem toS_inj {c d : BlindCircle} (h : toS c = toS d) : c = d := by
  have := congrArg ofS h; exact this

theorem ofS_inj {s t : Sphere ℂ} (h : ofS s = ofS t) : s = t := by
  have := congrArg toS h; exact this

theorem pappusU_R_to_B : type_of% @Arbelos.pappus_unique → blind24_stmt := by
  intro h a b c ha hb hpos h0 hbig hleft hsucc hne hup n
  apply toS_inj
  rw [toS_pappus]
  refine h ha hb (fun k ↦ toS (c k)) ?_ hpos (fun k ↦ ?_) (fun k ↦ ?_) (fun k ↦ ?_) (fun k e ↦ ?_)
    hup n
  · show toS (c 0) = _; rw [h0, diam_right]
  · have := ((bInt_iff _ _).1 (hbig k)).2.2; rwa [diam_big] at this
  · have := ((bExt_iff _ _).1 (hleft k)).2.2; rw [diam_left a b] at this; exact this.symm
  · exact ((bExt_iff _ _).1 (hsucc k)).2.2
  · exact hne k (toS_inj e)

theorem pappusU_B_to_R : blind24_stmt → type_of% @Arbelos.pappus_unique := by
  intro h a b ha hb c h0 hpos hbig hleft hsucc hne hup n
  have hab : 0 < a + b := by linarith
  have := h a b (fun k ↦ ofS (c k)) ha hb hpos ?_ (fun k ↦ ?_) (fun k ↦ ?_) (fun k ↦ ?_)
    (fun k e ↦ hne k (ofS_inj e)) hup n
  · exact ofS_inj this
  · apply toS_inj; show c 0 = _; rw [h0, diam_right]
  · refine (bInt_iff _ _).2 ⟨hpos k, by show 0 < (2 * (a + b) - 0) / 2; linarith, ?_⟩
    rw [diam_big]; exact hbig k
  · refine (bExt_iff _ _).2 ⟨hpos k, by show 0 < (2 * a - 0) / 2; linarith, ?_⟩
    rw [diam_left a b]; exact (hleft k).symm
  · exact (bExt_iff _ _).2 ⟨hpos k, hpos (k + 1), hsucc k⟩

/-! ## thm:bankoff — `incircle_eq` vs `blind_30` -/

def blind30_stmt : Prop :=
  ∀ (a b : ℝ) (s : BlindCircle), 0 < a → 0 < b →
    BlindInternallyTangent s (BlindDiameterCircle 0 (2 * (a + b))) →
    BlindExternallyTangent s (BlindDiameterCircle 0 (2 * a)) →
    BlindExternallyTangent s (BlindDiameterCircle (2 * a) (2 * (a + b))) →
    0 < s.1.im →
    s = BlindPappusCircle a b 1

theorem incircle_R_to_B : type_of% @Arbelos.incircle_eq → blind30_stmt := by
  intro h a b s ha hb hbig hl hr hup
  apply toS_inj
  rw [show BlindPappusCircle a b 1 = BlindPappusCircle a b (1 : ℕ) from rfl, toS_pappus]
  have h1 := ((bInt_iff _ _).1 hbig).2.2; rw [diam_big] at h1
  have h2 := ((bExt_iff _ _).1 hl).2.2; rw [diam_left a b] at h2
  have h3 := ((bExt_iff _ _).1 hr).2.2; rw [diam_right] at h3
  exact h ha hb (toS s) h1 h2.symm h3.symm hup

/-- Degenerate-radius exclusion needed for B→R: a point-circle cannot lie on all three
arbelos circles (elementary coordinate algebra, Mathlib only). -/
theorem incircle_rad_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hbig : s.IsIntTangent (Arbelos.bigS a b)) (hleft : (Arbelos.leftS a b).IsExtTangent s)
    (hright : (Arbelos.rightS a b).IsExtTangent s) : 0 < s.radius := by
  rw [Sphere.isIntTangent_iff_dist_center] at hbig
  rw [Sphere.isExtTangent_iff_dist_center] at hleft hright
  obtain ⟨h1, hr0, -⟩ := hbig
  obtain ⟨h2, -, -⟩ := hleft
  obtain ⟨h3, -, -⟩ := hright
  rcases hr0.lt_or_eq with h | h
  · exact h
  exfalso
  simp only [Arbelos.bigS, Arbelos.leftS, Arbelos.rightS, ← h, sub_zero, add_zero] at h1 h2 h3
  have q1 := congrArg (· ^ 2) h1
  have q2 := congrArg (· ^ 2) h2
  have q3 := congrArg (· ^ 2) h3
  simp only [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im] at q1 q2 q3
  rw [Real.sq_sqrt (by positivity)] at q1 q2 q3
  have hx : s.center.re = 0 := by nlinarith
  have hy : s.center.im = 0 := by nlinarith
  rw [hx, hy] at q3
  nlinarith

theorem incircle_B_to_R : blind30_stmt → type_of% @Arbelos.incircle_eq := by
  intro h a b ha hb s hbig hleft hright hup
  have hr := incircle_rad_pos ha hb s hbig hleft hright
  have hab : 0 < a + b := by linarith
  have := h a b (ofS s) ha hb ?_ ?_ ?_ hup
  · have e := congrArg toS this
    rw [show BlindPappusCircle a b 1 = BlindPappusCircle a b (1 : ℕ) from rfl, toS_pappus] at e
    exact e
  · refine (bInt_iff _ _).2 ⟨hr, by show 0 < (2 * (a + b) - 0) / 2; linarith, ?_⟩
    rw [diam_big]; exact hbig
  · refine (bExt_iff _ _).2 ⟨hr, by show 0 < (2 * a - 0) / 2; linarith, ?_⟩
    rw [diam_left a b]; exact hleft.symm
  · refine (bExt_iff _ _).2 ⟨hr, by show 0 < (2 * (a + b) - 2 * a) / 2; linarith, ?_⟩
    rw [diam_right]; exact hright.symm


/-- `blind_26` is an unconditional field identity (proved here by unfolding + `ring`, Mathlib
only); it is the real-parameter form of `pappus_chain`. -/
theorem blind26_holds : blind26_stmt := by
  intro a b t
  simp only [BlindPhi, BlindPappusDenominator]
  ring

/-! ## thm:steiner — chain transfer between `ZMod n`-indexed spheres and `ℕ`-periodic pairs -/

section Transfer

variable {n : ℕ} [NeZero n]

theorem val_succ (i : ZMod n) : (i + 1).val = (i.val + 1) % n := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]

theorem cast_succ_mod (i : ℕ) : (((i + 1) % n : ℕ) : ZMod n) = (i : ZMod n) + 1 := by
  rw [ZMod.natCast_mod]; push_cast; ring

theorem cast_add_n (i : ℕ) : (((i + n) : ℕ) : ZMod n) = (i : ZMod n) := by
  push_cast; rw [ZMod.natCast_self, add_zero]

theorem toReal_chain {S₁ S₂ : BlindCircle} {c : ℕ → BlindCircle}
    (h : BlindSteinerChain S₁ S₂ n c) :
    Arbelos.IsSteinerChain (toS S₁) (toS S₂) n (fun i ↦ toS (c i.val)) := by
  unfold Arbelos.IsSteinerChain
  intro i
  obtain ⟨hi, he, hs⟩ := h.2.2.2.2.2 i.val (ZMod.val_lt i)
  rw [bInt_iff] at hi
  rw [bExt_iff] at he hs
  refine ⟨hi.1, he.2.2.symm, hi.2.2, ?_⟩
  show (toS (c i.val)).IsExtTangent (toS (c (i + 1).val))
  rw [val_succ]; exact hs.2.2

theorem ofReal_chain {S₁ S₂ : BlindCircle} (h1 : 0 < S₁.2) (hin : dist S₁.1 S₂.1 < S₂.2 - S₁.2)
    (hn : 0 < n) {d : ZMod n → Sphere ℂ} (h : Arbelos.IsSteinerChain (toS S₁) (toS S₂) n d) :
    BlindSteinerChain S₁ S₂ n (fun k ↦ ofS (d (k : ZMod n))) := by
  have h2 : 0 < S₂.2 := by linarith [dist_nonneg (x := S₁.1) (y := S₂.1)]
  unfold Arbelos.IsSteinerChain at h
  refine ⟨hn, h1, h2, by linarith, fun i ↦ ?_, fun i _ ↦ ?_⟩
  · show ofS (d ((i + n : ℕ) : ZMod n)) = ofS (d (i : ZMod n)); rw [cast_add_n]
  · obtain ⟨hp, he, hi, hs⟩ := h (i : ZMod n)
    have hp' := (h ((i : ZMod n) + 1)).1
    refine ⟨(bInt_iff _ _).2 ⟨hp, h2, hi⟩, (bExt_iff _ _).2 ⟨hp, h1, he.symm⟩,
      (bExt_iff _ _).2 ⟨hp, ?_, ?_⟩⟩
    · show 0 < (d (((i + 1) % n : ℕ) : ZMod n)).radius; rw [cast_succ_mod]; exact hp'
    · show (d (i : ZMod n)).IsExtTangent (d (((i + 1) % n : ℕ) : ZMod n))
      rw [cast_succ_mod]; exact hs

theorem inj_toReal {c : ℕ → BlindCircle} (h : ∀ i j, i < n → j < n → i ≠ j → c i ≠ c j) :
    Function.Injective (fun i : ZMod n ↦ toS (c i.val)) := by
  intro i j e
  by_contra hne
  exact h _ _ (ZMod.val_lt i) (ZMod.val_lt j) (fun hv ↦ hne (ZMod.val_injective n hv))
    (toS_inj e)

theorem inj_ofReal {d : ZMod n → Sphere ℂ} (h : Function.Injective d) :
    ∀ i j, i < n → j < n → i ≠ j → ofS (d (i : ZMod n)) ≠ ofS (d (j : ZMod n)) := by
  intro i j hi hj hne e
  have := congrArg ZMod.val (h (ofS_inj e))
  rw [ZMod.val_cast_of_lt hi, ZMod.val_cast_of_lt hj] at this
  exact hne this

theorem disj_toReal {c : ℕ → BlindCircle}
    (h : ∀ i j, i < n → j < n → i ≠ j →
      Disjoint (BlindCircleInterior (c i)) (BlindCircleInterior (c j))) :
    Arbelos.HasDisjointDiscs (fun i : ZMod n ↦ toS (c i.val)) := by
  intro i j hij
  exact h _ _ (ZMod.val_lt i) (ZMod.val_lt j) (fun hv ↦ hij (ZMod.val_injective n hv))

theorem disj_ofReal {d : ZMod n → Sphere ℂ} (h : Arbelos.HasDisjointDiscs d) :
    ∀ i j, i < n → j < n → i ≠ j →
      Disjoint (BlindCircleInterior (ofS (d (i : ZMod n))))
        (BlindCircleInterior (ofS (d (j : ZMod n)))) := by
  intro i j hi hj hne
  refine h (fun e ↦ hne ?_)
  have := congrArg ZMod.val e
  rwa [ZMod.val_cast_of_lt hi, ZMod.val_cast_of_lt hj] at this

theorem d0_ofReal {d : ZMod n → Sphere ℂ} {s₀ : BlindCircle} (h : d 0 = toS s₀) :
    (fun k : ℕ ↦ ofS (d (k : ZMod n))) 0 = s₀ := by
  show ofS (d ((0 : ℕ) : ZMod n)) = s₀
  rw [Nat.cast_zero, h]; rfl

theorem d0_toReal {d : ℕ → BlindCircle} {s₀ : Sphere ℂ} (h : d 0 = ofS s₀) :
    (fun i : ZMod n ↦ toS (d i.val)) 0 = s₀ := by
  show toS (d (0 : ZMod n).val) = s₀
  rw [ZMod.val_zero, h]; rfl

end Transfer

/-- Mathlib-only: with strictly nested `S₁ ⊂ S₂`, a circle tangent to both has positive radius. -/
theorem s0_pos {S₁ S₂ s₀ : Sphere ℂ} (hin : dist S₁.center S₂.center < S₂.radius - S₁.radius)
    (h₁ : S₁.IsExtTangent s₀) (h₂ : s₀.IsIntTangent S₂) : 0 < s₀.radius := by
  rw [Sphere.isExtTangent_iff_dist_center] at h₁
  rw [Sphere.isIntTangent_iff_dist_center] at h₂
  have := dist_triangle s₀.center S₁.center S₂.center
  rw [dist_comm s₀.center S₁.center] at this
  linarith [h₁.1, h₂.1]

/-! ## thm:steiner — `steiner_porism` vs `blind_31` -/

def blind31_stmt : Prop :=
  ∀ (S₁ S₂ s₀ : BlindCircle) (n : ℕ) (c : ℕ → BlindCircle),
    0 < S₁.2 → dist S₁.1 S₂.1 < S₂.2 - S₁.2 →
    BlindSteinerChain S₁ S₂ n c → 0 < s₀.2 →
    BlindExternallyTangent s₀ S₁ → BlindInternallyTangent s₀ S₂ →
    ∃ d : ℕ → BlindCircle, BlindSteinerChain S₁ S₂ n d ∧ d 0 = s₀

/-- `steiner_porism` with the extra hypothesis `0 < n` (the only part `blind_31` can reach:
for `n = 0` the library's `ZMod 0 = ℤ` chain is a bi-infinite chain). -/
def steinerPorism_pos_stmt : Prop :=
  ∀ (S₁ S₂ : Sphere ℂ), 0 < S₁.radius → dist S₁.center S₂.center < S₂.radius - S₁.radius →
    ∀ (n : ℕ), 0 < n → ∀ (c : ZMod n → Sphere ℂ), Arbelos.IsSteinerChain S₁ S₂ n c →
    ∀ (s₀ : Sphere ℂ), 0 < s₀.radius → S₁.IsExtTangent s₀ → s₀.IsIntTangent S₂ →
    ∃ d : ZMod n → Sphere ℂ, Arbelos.IsSteinerChain S₁ S₂ n d ∧ d 0 = s₀

theorem steiner_R_to_pos : type_of% @Arbelos.steiner_porism → steinerPorism_pos_stmt :=
  fun h S₁ S₂ h1 hin n _ c hc s₀ hs he hi ↦ h S₁ S₂ h1 hin n c hc s₀ hs he hi

theorem steiner_R_to_B : type_of% @Arbelos.steiner_porism → blind31_stmt := by
  intro h S₁ S₂ s₀ n c h1 hin hc hs he hi
  have : NeZero n := ⟨hc.1.ne'⟩
  obtain ⟨d, hd, hd0⟩ := h (toS S₁) (toS S₂) h1 hin n _ (toReal_chain hc) (toS s₀) hs
    ((bExt_iff _ _).1 he).2.2.symm ((bInt_iff _ _).1 hi).2.2
  exact ⟨_, ofReal_chain h1 hin hc.1 hd, d0_ofReal hd0⟩

theorem steiner_B_to_pos : blind31_stmt → steinerPorism_pos_stmt := by
  intro h S₁ S₂ h1 hin n hn c hc s₀ hs he hi
  have : NeZero n := ⟨hn.ne'⟩
  have h2 : 0 < S₂.radius := by linarith [dist_nonneg (x := S₁.center) (y := S₂.center)]
  obtain ⟨d, hd, hd0⟩ := h (ofS S₁) (ofS S₂) (ofS s₀) n (fun k ↦ ofS (c k)) h1 hin
    (ofReal_chain (S₁ := ofS S₁) (S₂ := ofS S₂) h1 hin hn hc) hs
    ((bExt_iff _ _).2 ⟨hs, h1, he.symm⟩) ((bInt_iff _ _).2 ⟨hs, h2, hi⟩)
  exact ⟨_, toReal_chain (S₁ := ofS S₁) (S₂ := ofS S₂) hd, d0_toReal hd0⟩

/-! ## thm:steiner — `steiner_porism_simple`, `steiner_porism_disjoint` vs `blind_32`, `blind_33` -/

def blind32_stmt : Prop :=
  ∀ (S₁ S₂ s₀ : BlindCircle) (n : ℕ) (c : ℕ → BlindCircle),
    0 < S₁.2 → dist S₁.1 S₂.1 < S₂.2 - S₁.2 → 3 ≤ n →
    BlindSimpleSteinerChain S₁ S₂ n c → 0 < s₀.2 →
    BlindExternallyTangent s₀ S₁ → BlindInternallyTangent s₀ S₂ →
    ∃ d : ℕ → BlindCircle, BlindSimpleSteinerChain S₁ S₂ n d ∧ d 0 = s₀

def blind33_stmt : Prop :=
  ∀ (S₁ S₂ s₀ : BlindCircle) (n : ℕ) (c : ℕ → BlindCircle),
    0 < S₁.2 → dist S₁.1 S₂.1 < S₂.2 - S₁.2 → 3 ≤ n →
    BlindSimpleSteinerChain S₁ S₂ n c → BlindDisjointSteinerChain S₁ S₂ n c → 0 < s₀.2 →
    BlindExternallyTangent s₀ S₁ → BlindInternallyTangent s₀ S₂ →
    ∃ d : ℕ → BlindCircle,
      BlindSimpleSteinerChain S₁ S₂ n d ∧ BlindDisjointSteinerChain S₁ S₂ n d ∧ d 0 = s₀

theorem simple_R_to_B : type_of% @Arbelos.steiner_porism_simple → blind32_stmt := by
  intro h S₁ S₂ s₀ n c h1 hin hn3 hc hs he hi
  have : NeZero n := ⟨by omega⟩
  obtain ⟨d, ⟨hd, -, hdi⟩, hd0⟩ := h (toS S₁) (toS S₂) h1 hin n _
    ⟨toReal_chain hc.1, hn3, inj_toReal hc.2⟩ (toS s₀)
    ((bExt_iff _ _).1 he).2.2.symm ((bInt_iff _ _).1 hi).2.2
  exact ⟨_, ⟨ofReal_chain h1 hin (by omega) hd, inj_ofReal hdi⟩, d0_ofReal hd0⟩

theorem simple_B_to_R : blind32_stmt → type_of% @Arbelos.steiner_porism_simple := by
  intro h S₁ S₂ h1 hin n c ⟨hc, hn3, hci⟩ s₀ he hi
  have : NeZero n := ⟨by omega⟩
  have hs := s0_pos hin he hi
  have h2 : 0 < S₂.radius := by linarith [dist_nonneg (x := S₁.center) (y := S₂.center)]
  obtain ⟨d, ⟨hd, hdi⟩, hd0⟩ := h (ofS S₁) (ofS S₂) (ofS s₀) n (fun k ↦ ofS (c k)) h1 hin hn3
    ⟨ofReal_chain (S₁ := ofS S₁) (S₂ := ofS S₂) h1 hin (by omega) hc, inj_ofReal hci⟩ hs
    ((bExt_iff _ _).2 ⟨hs, h1, he.symm⟩) ((bInt_iff _ _).2 ⟨hs, h2, hi⟩)
  exact ⟨_, ⟨toReal_chain (S₁ := ofS S₁) (S₂ := ofS S₂) hd, hn3, inj_toReal hdi⟩,
    d0_toReal hd0⟩

theorem disjoint_R_to_B : type_of% @Arbelos.steiner_porism_disjoint → blind33_stmt := by
  intro h S₁ S₂ s₀ n c h1 hin hn3 hc hcd hs he hi
  have : NeZero n := ⟨by omega⟩
  obtain ⟨d, ⟨⟨hd, -, hdi⟩, hdd⟩, hd0⟩ := h (toS S₁) (toS S₂) h1 hin n _
    ⟨⟨toReal_chain hc.1, hn3, inj_toReal hc.2⟩, disj_toReal hcd.2⟩ (toS s₀)
    ((bExt_iff _ _).1 he).2.2.symm ((bInt_iff _ _).1 hi).2.2
  have hb := ofReal_chain h1 hin (by omega) hd
  exact ⟨_, ⟨hb, inj_ofReal hdi⟩, ⟨hb, disj_ofReal hdd⟩, d0_ofReal hd0⟩

theorem disjoint_B_to_R : blind33_stmt → type_of% @Arbelos.steiner_porism_disjoint := by
  intro h S₁ S₂ h1 hin n c ⟨⟨hc, hn3, hci⟩, hcd⟩ s₀ he hi
  have : NeZero n := ⟨by omega⟩
  have hs := s0_pos hin he hi
  have h2 : 0 < S₂.radius := by linarith [dist_nonneg (x := S₁.center) (y := S₂.center)]
  have hb := ofReal_chain (S₁ := ofS S₁) (S₂ := ofS S₂) h1 hin (by omega) hc
  obtain ⟨d, ⟨hd, hdi⟩, ⟨-, hdd⟩, hd0⟩ := h (ofS S₁) (ofS S₂) (ofS s₀) n
    (fun k ↦ ofS (c k)) h1 hin hn3 ⟨hb, inj_ofReal hci⟩ ⟨hb, disj_ofReal hcd⟩ hs
    ((bExt_iff _ _).2 ⟨hs, h1, he.symm⟩) ((bInt_iff _ _).2 ⟨hs, h2, hi⟩)
  exact ⟨_, ⟨⟨toReal_chain (S₁ := ofS S₁) (S₂ := ofS S₂) hd, hn3, inj_toReal hdi⟩,
    disj_toReal hdd⟩, d0_toReal hd0⟩

/-! ## thm:steiner — `steiner_porism_strong`, `steiner_concentric_strong` vs `blind_32/33/34`
(R→B only; see report for the B→R gap) -/

theorem strong_R_to_B : type_of% @Arbelos.steiner_porism_strong → blind32_stmt ∧ blind33_stmt := by
  intro h
  refine ⟨fun S₁ S₂ s₀ n c h1 hin hn3 hc hs he hi ↦ ?_,
    fun S₁ S₂ s₀ n c h1 hin hn3 hc hcd hs he hi ↦ ?_⟩
  · have : NeZero n := ⟨by omega⟩
    obtain ⟨d, hd, hd0, hinj, -⟩ := h (toS S₁) (toS S₂) h1 hin n _ (toReal_chain hc.1) (toS s₀)
      ((bExt_iff _ _).1 he).2.2.symm ((bInt_iff _ _).1 hi).2.2
    exact ⟨_, ⟨ofReal_chain h1 hin (by omega) hd, inj_ofReal (hinj (inj_toReal hc.2))⟩,
      d0_ofReal hd0⟩
  · have : NeZero n := ⟨by omega⟩
    obtain ⟨d, hd, hd0, hinj, hdis⟩ := h (toS S₁) (toS S₂) h1 hin n _ (toReal_chain hc.1)
      (toS s₀) ((bExt_iff _ _).1 he).2.2.symm ((bInt_iff _ _).1 hi).2.2
    have hb := ofReal_chain h1 hin (by omega) hd
    exact ⟨_, ⟨hb, inj_ofReal (hinj (inj_toReal hc.2))⟩,
      ⟨hb, disj_ofReal (hdis (disj_toReal hcd.2))⟩, d0_ofReal hd0⟩

/-! ## thm:steiner — `steiner_concentric` (and `steiner_concentric_strong`) vs `blind_34` -/

def blind34_stmt : Prop :=
  ∀ (S₁ S₂ s₀ : BlindCircle) (n : ℕ) (c : ℕ → BlindCircle),
    0 < S₁.2 → dist S₁.1 S₂.1 < S₂.2 - S₁.2 → S₁.1 = S₂.1 →
    BlindSteinerChain S₁ S₂ n c →
    dist s₀.1 S₁.1 = s₀.2 + S₁.2 → dist s₀.1 S₂.1 + s₀.2 = S₂.2 →
    ∃ d : ℕ → BlindCircle, BlindSteinerChain S₁ S₂ n d ∧ d 0 = s₀

/-- `steiner_concentric` restricted to `0 < S₁.radius` and `0 < n` (what `blind_34` reaches). -/
def steinerConc_pos_stmt : Prop :=
  ∀ (S₁ S₂ : Sphere ℂ), S₁.center = S₂.center → 0 < S₁.radius →
    ∀ (n : ℕ), 0 < n → ∀ (c : ZMod n → Sphere ℂ), Arbelos.IsSteinerChain S₁ S₂ n c →
    ∀ (s₀ : Sphere ℂ), S₁.IsExtTangent s₀ → s₀.IsIntTangent S₂ →
    ∃ d : ZMod n → Sphere ℂ, Arbelos.IsSteinerChain S₁ S₂ n d ∧ d 0 = s₀

theorem conc_hyps {S₁ S₂ s₀ : BlindCircle} (hin : dist S₁.1 S₂.1 < S₂.2 - S₁.2)
    (hc : S₁.1 = S₂.1) (he : dist s₀.1 S₁.1 = s₀.2 + S₁.2) (hi : dist s₀.1 S₂.1 + s₀.2 = S₂.2)
    (h1 : 0 < S₁.2) :
    (toS S₁).IsExtTangent (toS s₀) ∧ (toS s₀).IsIntTangent (toS S₂) := by
  rw [hc, dist_self] at hin
  rw [hc] at he
  have hs : 0 < s₀.2 := by linarith
  rw [Sphere.isExtTangent_iff_dist_center, Sphere.isIntTangent_iff_dist_center]
  simp only [toS_center, toS_radius]
  exact ⟨⟨by rw [dist_comm, hc, he]; ring, h1.le, hs.le⟩, ⟨by linarith, hs.le, by linarith⟩⟩

theorem conc_R_to_B : type_of% @Arbelos.steiner_concentric → blind34_stmt := by
  intro h S₁ S₂ s₀ n c h1 hin hc hch he hi
  have : NeZero n := ⟨hch.1.ne'⟩
  obtain ⟨e1, e2⟩ := conc_hyps hin hc he hi h1
  obtain ⟨d, hd, hd0⟩ := h (toS S₁) (toS S₂) hc n _ (toReal_chain hch) (toS s₀) e1 e2
  exact ⟨_, ofReal_chain h1 hin hch.1 hd, d0_ofReal hd0⟩

theorem concStrong_R_to_B : type_of% @Arbelos.steiner_concentric_strong → blind34_stmt := by
  intro h S₁ S₂ s₀ n c h1 hin hc hch he hi
  have : NeZero n := ⟨hch.1.ne'⟩
  obtain ⟨e1, e2⟩ := conc_hyps hin hc he hi h1
  obtain ⟨d, hd, hd0, -, -⟩ := h (toS S₁) (toS S₂) hc n _ (toReal_chain hch) (toS s₀) e1 e2
  exact ⟨_, ofReal_chain h1 hin hch.1 hd, d0_ofReal hd0⟩

theorem conc_R_to_pos : type_of% @Arbelos.steiner_concentric → steinerConc_pos_stmt :=
  fun h S₁ S₂ hc _ n _ c hch s₀ he hi ↦ h S₁ S₂ hc n c hch s₀ he hi

theorem conc_B_to_pos : blind34_stmt → steinerConc_pos_stmt := by
  intro h S₁ S₂ hc h1 n hn c hch s₀ he hi
  have : NeZero n := ⟨hn.ne'⟩
  -- nesting follows from the existing chain (circle `c 0`)
  obtain ⟨hp, he0, hi0, -⟩ := hch 0
  rw [Sphere.isExtTangent_iff_dist_center] at he0 he
  rw [Sphere.isIntTangent_iff_dist_center] at hi0 hi
  have hin : dist S₁.center S₂.center < S₂.radius - S₁.radius := by
    rw [← hc] at hi0; rw [hc, dist_self]; rw [dist_comm] at hi0; linarith [he0.1]
  have hch' : Arbelos.IsSteinerChain S₁ S₂ n c := hch
  obtain ⟨d, hd, hd0⟩ := h (ofS S₁) (ofS S₂) (ofS s₀) n (fun k ↦ ofS (c k)) h1 hin hc
    (ofReal_chain (S₁ := ofS S₁) (S₂ := ofS S₂) h1 hin hn hch')
    (by show dist s₀.center S₁.center = s₀.radius + S₁.radius; rw [dist_comm, he.1]; ring)
    (by show dist s₀.center S₂.center + s₀.radius = S₂.radius; rw [hi.1]; ring)
  exact ⟨_, toReal_chain (S₁ := ofS S₁) (S₂ := ofS S₂) hd, d0_toReal hd0⟩

/-! ## thm:steiner — `exists_inversion_concentric` vs `blind_35` -/

def blind35_stmt : Prop :=
  ∀ (S₁ S₂ : BlindCircle), 0 < S₁.2 → dist S₁.1 S₂.1 < S₂.2 - S₁.2 → S₁.1 ≠ S₂.1 →
    ∃ center : ℂ, ∃ radius : ℝ,
      0 < radius ∧
      0 < BlindPower center S₁ ∧ 0 < BlindPower center S₂ ∧
      (BlindInvertedCircle center radius S₁).1 = (BlindInvertedCircle center radius S₂).1

theorem pow_eq (z : ℂ) (S : BlindCircle) : BlindPower z S = Arbelos.powC z (toS S) := by
  simp only [BlindPower, Arbelos.powC, toS_center, toS_radius]
  rw [dist_comm, Complex.dist_eq]

theorem invC_eq (z : ℂ) (S : BlindCircle) :
    (BlindInvertedCircle z 1 S).1 = (Arbelos.invSphere z 1 (toS S)).center := by
  simp only [BlindInvertedCircle, Arbelos.invSphere, toS_center, toS_radius, pow_eq]
  rfl

theorem invC_scale (z : ℂ) (r : ℝ) (hr : r ≠ 0) (S T : BlindCircle)
    (h : (BlindInvertedCircle z r S).1 = (BlindInvertedCircle z r T).1) :
    (BlindInvertedCircle z 1 S).1 = (BlindInvertedCircle z 1 T).1 := by
  simp only [BlindInvertedCircle] at h ⊢
  have key := add_left_cancel h
  have e : ∀ p : ℝ, (((1 : ℝ) ^ 2 / p : ℝ) : ℂ) = ((1 / r ^ 2 : ℝ) : ℂ) * ((r ^ 2 / p : ℝ) : ℂ) := by
    intro p
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [e, e, mul_assoc, mul_assoc, key]

theorem inv_R_to_B : type_of% @Arbelos.exists_inversion_concentric → blind35_stmt := by
  intro h S₁ S₂ h1 hin hne
  obtain ⟨c, hp1, hp2, hcen⟩ := h (toS S₁) (toS S₂) h1 hne hin
  exact ⟨c, 1, one_pos, by rw [pow_eq]; exact hp1, by rw [pow_eq]; exact hp2,
    by rw [invC_eq, invC_eq]; exact hcen⟩

theorem inv_B_to_R : blind35_stmt → type_of% @Arbelos.exists_inversion_concentric := by
  intro h S₁ S₂ h1 hne hin
  obtain ⟨c, r, hr, hp1, hp2, hcen⟩ := h (ofS S₁) (ofS S₂) h1 hin hne
  have := invC_scale c r hr.ne' _ _ hcen
  rw [invC_eq, invC_eq] at this
  rw [pow_eq] at hp1 hp2
  exact ⟨c, hp1, hp2, this⟩


/-! ### `pappus_chain`: remaining directions. Both sides are field identities, so these hold
by unfolding + `ring` (`blind26_holds`); the hypotheses are not needed. -/

theorem pappusChain_B22_to_R : blind22_stmt → type_of% @Arbelos.pappus_chain :=
  fun _ {a b} n ↦ blind26_holds a b n

theorem pappusChain_R_to_B26 : type_of% @Arbelos.pappus_chain → blind26_stmt :=
  fun _ ↦ blind26_holds

end L13CmpArb
