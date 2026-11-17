import Arbelos

/-!
# Layer 13 comparison (machine john): Bankoff pair `blind_79` / `blind_80` vs
# `Arbelos.bankoff` / `Arbelos.bankoff_exists`

Blind definitions are copied verbatim from `PaperIBlind.lean` (section "bankoff addendum" plus the
generic circle defs it uses), namespace `L13CmpBankoff`. Each `blindK_stmt` is `blind_K` with its
proof placeholder removed and all variables universally quantified. Real statements are referenced
via `type_of%` only; no library theorem is used in any proof body (library *definitions* such as
`bigS`, `leftS`, `rightS`, `ptC` are unfolded).
-/

noncomputable section
open scoped RealInnerProductSpace
open Set Metric EuclideanGeometry

namespace L13CmpBankoff

/-! ## Verbatim blind definitions -/

def BlindCircle : Type := ℂ × ℝ

def BlindCirclePoints (c : BlindCircle) : Set ℂ :=
  {z | dist z c.1 = c.2}

def BlindInternallyTangent (inner outer : BlindCircle) : Prop :=
  inner.2 > 0 ∧ outer.2 > 0 ∧
    dist inner.1 outer.1 + inner.2 = outer.2

def BlindIsCircle (c : BlindCircle) : Prop :=
  0 < c.2

def BlindUpperHalfPlane (p : ℂ) : Prop :=
  0 < p.im

def BlindExtTangentAtPoint (c d : BlindCircle) (p : ℂ) : Prop :=
  BlindIsCircle c ∧ BlindIsCircle d ∧
    dist c.1 d.1 = c.2 + d.2 ∧
    0 ≤ p.im ∧ BlindCirclePoints c p ∧ BlindCirclePoints d p

def BlindOuterCircle (a b : ℝ) : BlindCircle :=
  (((a + b : ℝ) : ℂ), a + b)

def BlindFirstCircle (a : ℝ) : BlindCircle :=
  ((a : ℂ), a)

def BlindSecondCircle (a b : ℝ) : BlindCircle :=
  (((2 * a + b : ℝ) : ℂ), b)

def BlindCommonPoint (a : ℝ) : ℂ :=
  ((2 * a : ℝ) : ℂ)

def BlindBankoffCircle (a b : ℝ) : BlindCircle :=
  (((2 * a : ℝ) : ℂ) + ((a * b / (a + b) : ℝ) : ℂ) * Complex.I,
    a * b / (a + b))

/-! ## Blind statements as closed propositions -/

/-- `blind_79` (thm:bankoff, radius claim). -/
def blind79_stmt : Prop :=
  ∀ (a b : ℝ), 0 < a → 0 < b →
    ∀ (c₁ k : BlindCircle) (T₁ T₂ : ℂ),
      BlindUpperHalfPlane c₁.1 →
      BlindInternallyTangent c₁ (BlindOuterCircle a b) →
      BlindExtTangentAtPoint c₁ (BlindFirstCircle a) T₁ →
      BlindExtTangentAtPoint c₁ (BlindSecondCircle a b) T₂ →
      BlindIsCircle k →
      BlindCirclePoints k (BlindCommonPoint a) →
      BlindCirclePoints k T₁ →
      BlindCirclePoints k T₂ →
      k.2 = a * b / (a + b)

/-- `blind_80` (thm:bankoff, existence with explicit centre). -/
def blind80_stmt : Prop :=
  ∀ (a b : ℝ), 0 < a → 0 < b →
    ∀ (c₁ : BlindCircle) (T₁ T₂ : ℂ),
      BlindUpperHalfPlane c₁.1 →
      BlindInternallyTangent c₁ (BlindOuterCircle a b) →
      BlindExtTangentAtPoint c₁ (BlindFirstCircle a) T₁ →
      BlindExtTangentAtPoint c₁ (BlindSecondCircle a b) T₂ →
      BlindIsCircle (BlindBankoffCircle a b) ∧
        BlindCirclePoints (BlindBankoffCircle a b) (BlindCommonPoint a) ∧
        BlindCirclePoints (BlindBankoffCircle a b) T₁ ∧
        BlindCirclePoints (BlindBankoffCircle a b) T₂

/-! ## Bridge lemmas (Mathlib only) -/

def toS (c : BlindCircle) : Sphere ℂ := ⟨c.1, c.2⟩
def ofS (s : Sphere ℂ) : BlindCircle := (s.center, s.radius)

@[simp] theorem toS_ofS (s : Sphere ℂ) : toS (ofS s) = s := rfl
@[simp] theorem toS_center (c : BlindCircle) : (toS c).center = c.1 := rfl
@[simp] theorem toS_radius (c : BlindCircle) : (toS c).radius = c.2 := rfl

theorem outer_eq (a b : ℝ) : toS (BlindOuterCircle a b) = Arbelos.bigS a b := rfl
theorem first_eq (a b : ℝ) : toS (BlindFirstCircle a) = Arbelos.leftS a b := rfl
theorem second_eq (a b : ℝ) : toS (BlindSecondCircle a b) = Arbelos.rightS a b := rfl
theorem common_eq (a b : ℝ) : BlindCommonPoint a = Arbelos.ptC a b := rfl

theorem pts_iff (c : BlindCircle) (z : ℂ) : BlindCirclePoints c z ↔ z ∈ toS c :=
  Iff.rfl

/-- Blind internal tangency = Mathlib internal tangency + strict positivity of both radii. -/
theorem int_iff (c d : BlindCircle) :
    BlindInternallyTangent c d ↔ 0 < c.2 ∧ 0 < d.2 ∧ (toS c).IsIntTangent (toS d) := by
  rw [Sphere.isIntTangent_iff_dist_center]
  simp only [BlindInternallyTangent, toS_center, toS_radius, gt_iff_lt]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith, h1.le, h2.le⟩
  · rintro ⟨h1, h2, h3, -, -⟩; exact ⟨h1, h2, by linarith⟩

/-- Blind "externally tangent at a point" = Mathlib `IsExtTangentAt` (with the arguments in the
library's order `d`, `c`) + strict positivity of both radii + `0 ≤ p.im`. -/
theorem extAt_iff (c d : BlindCircle) (p : ℂ) :
    BlindExtTangentAtPoint c d p ↔
      0 < c.2 ∧ 0 < d.2 ∧ 0 ≤ p.im ∧ (toS d).IsExtTangentAt (toS c) p := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h4, (pts_iff _ _).1 h6, (pts_iff _ _).1 h5, ?_⟩
    rw [← dist_add_dist_eq_iff]
    simp only [toS_center]
    have e5 : dist p c.1 = c.2 := h5
    have e6 : dist p d.1 = d.2 := h6
    rw [dist_comm d.1 p, e6, e5, dist_comm, h3, add_comm]
  · rintro ⟨h1, h2, h4, ⟨m1, m2, w⟩⟩
    refine ⟨h1, h2, ?_, h4, (pts_iff _ _).2 m2, (pts_iff _ _).2 m1⟩
    rw [← dist_add_dist_eq_iff] at w
    simp only [toS_center] at w
    have e1 : dist p d.1 = d.2 := m1
    have e2 : dist p c.1 = c.2 := m2
    rw [dist_comm, ← w, dist_comm d.1 p, e1, e2, add_comm]

/-- Squared distance to a real point, in coordinates. -/
theorem dist_real_sq (z : ℂ) (x : ℝ) : dist (x : ℂ) z ^ 2 = (x - z.re) ^ 2 + z.im ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]
  simp

/-- Points of a segment from a real point `x` to `z`: imaginary part `μ * z.im`, `μ ∈ [0,1]`. -/
theorem wbtw_real_im {x : ℝ} {z p : ℂ} (h : Wbtw ℝ (x : ℂ) p z) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ p = AffineMap.lineMap (x : ℂ) z μ ∧ p.im = μ * z.im := by
  obtain ⟨μ, ⟨h0, h1⟩, rfl⟩ := h
  refine ⟨μ, h0, h1, rfl, ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  simp

/-- The incircle hypotheses of the library force a positive radius (the degenerate radius-0 case
would put a point in the open upper half-plane on both small circles, which meet only at `C`). -/
theorem s0_radius_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s₀ : Sphere ℂ)
    (hleft : (Arbelos.leftS a b).IsExtTangent s₀) (hright : (Arbelos.rightS a b).IsExtTangent s₀)
    (hup : 0 < s₀.center.im) : 0 < s₀.radius := by
  rw [Sphere.isExtTangent_iff_dist_center] at hleft hright
  obtain ⟨h1, -, hr⟩ := hleft
  obtain ⟨h2, -, -⟩ := hright
  rcases hr.lt_or_eq with h | h
  · exact h
  · exfalso
    simp only [Arbelos.leftS, Arbelos.rightS, ← h, add_zero] at h1 h2
    have q1 := dist_real_sq s₀.center a
    have q2 := dist_real_sq s₀.center (2 * a + b)
    rw [h1] at q1; rw [h2] at q2
    have hx : s₀.center.re = 2 * a := by
      have : (a + b) * (s₀.center.re - 2 * a) = 0 := by linear_combination (q2 - q1) / 2
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    rw [hx] at q1
    nlinarith

/-- Under the library hypotheses, a tangency point on a small circle lies strictly above the axis. -/
theorem tangency_im_pos {x ρ : ℝ} (s₀ : Sphere ℂ) (hup : 0 < s₀.center.im)
    (T : ℂ) (hT : (⟨(x : ℂ), ρ⟩ : Sphere ℂ).IsExtTangentAt s₀ T)
    (hd : dist (x : ℂ) s₀.center = ρ + s₀.radius) (hρ : 0 < ρ) : 0 < T.im := by
  obtain ⟨μ, h0, -, hp, him⟩ := wbtw_real_im hT.wbtw
  rcases h0.lt_or_eq with h | h
  · rw [him]; positivity
  · exfalso
    have hm : dist T s₀.center = s₀.radius := hT.mem_right
    rw [hp, ← h, AffineMap.lineMap_apply_zero, hd] at hm
    linarith

/-- Library hypotheses ⇒ blind hypotheses (for `c₁ = ofS s₀`). -/
theorem lib_to_blind {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s₀ : Sphere ℂ)
    (hbig : s₀.IsIntTangent (Arbelos.bigS a b)) (hleft : (Arbelos.leftS a b).IsExtTangent s₀)
    (hright : (Arbelos.rightS a b).IsExtTangent s₀) (hup : 0 < s₀.center.im)
    (T₁ T₂ : ℂ) (hT₁ : (Arbelos.leftS a b).IsExtTangentAt s₀ T₁)
    (hT₂ : (Arbelos.rightS a b).IsExtTangentAt s₀ T₂) :
    BlindUpperHalfPlane (ofS s₀).1 ∧
      BlindInternallyTangent (ofS s₀) (BlindOuterCircle a b) ∧
      BlindExtTangentAtPoint (ofS s₀) (BlindFirstCircle a) T₁ ∧
      BlindExtTangentAtPoint (ofS s₀) (BlindSecondCircle a b) T₂ ∧
      0 < T₁.im := by
  have hr := s0_radius_pos ha hb s₀ hleft hright hup
  have d1 := hleft.dist_center
  have d2 := hright.dist_center
  have i1 := tangency_im_pos s₀ hup T₁ hT₁ d1 ha
  have i2 := tangency_im_pos s₀ hup T₂ hT₂ d2 hb
  refine ⟨hup, ?_, ?_, ?_, i1⟩
  · exact (int_iff _ _).2 ⟨hr, show 0 < a + b by linarith, hbig⟩
  · exact (extAt_iff _ _ _).2 ⟨hr, ha, i1.le, hT₁⟩
  · exact (extAt_iff _ _ _).2 ⟨hr, hb, i2.le, hT₂⟩

/-! ## Row 1: `Arbelos.bankoff` vs `blind_79` -/

theorem bankoff_R_to_B : type_of% @Arbelos.bankoff → blind79_stmt := by
  intro h a b ha hb c₁ k T₁ T₂ hup hin ht₁ ht₂ _hk hC h₁ h₂
  rw [int_iff, outer_eq] at hin
  rw [extAt_iff, first_eq a b] at ht₁
  rw [extAt_iff, second_eq] at ht₂
  exact h ha hb (toS c₁) hin.2.2 ht₁.2.2.2.isExtTangent ht₂.2.2.2.isExtTangent hup T₁ T₂
    ht₁.2.2.2 ht₂.2.2.2 (toS k) ((pts_iff _ _).1 hC) ((pts_iff _ _).1 h₁) ((pts_iff _ _).1 h₂)

theorem bankoff_B_to_R : blind79_stmt → type_of% @Arbelos.bankoff := by
  intro h a b ha hb s₀ hbig hleft hright hup T₁ T₂ hT₁ hT₂ s hC h₁ h₂
  obtain ⟨u, i, e1, e2, hpos⟩ := lib_to_blind ha hb s₀ hbig hleft hright hup T₁ T₂ hT₁ hT₂
  -- the library's `s` is an arbitrary sphere; the blind statement asks for `0 < radius`
  have hs : 0 < s.radius := by
    rcases (s.radius_nonneg_of_mem hC).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have a1 : dist (Arbelos.ptC a b) s.center = 0 := by rw [EuclideanGeometry.mem_sphere.1 hC, ← heq]
      have a2 : dist T₁ s.center = 0 := by rw [EuclideanGeometry.mem_sphere.1 h₁, ← heq]
      rw [dist_eq_zero] at a1 a2
      have : T₁.im = (Arbelos.ptC a b).im := by rw [a1, a2]
      simp [Arbelos.ptC] at this
      linarith
  exact h a b ha hb (ofS s₀) (ofS s) T₁ T₂ u i e1 e2 hs
    ((pts_iff _ _).2 hC) ((pts_iff _ _).2 h₁) ((pts_iff _ _).2 h₂)

/-! ## Row 2: `Arbelos.bankoff_exists` vs `blind_80` -/

theorem bankoffEx_B_to_R : blind80_stmt → type_of% @Arbelos.bankoff_exists := by
  intro h a b ha hb s₀ hbig hleft hright hup T₁ T₂ hT₁ hT₂
  obtain ⟨u, i, e1, e2, -⟩ := lib_to_blind ha hb s₀ hbig hleft hright hup T₁ T₂ hT₁ hT₂
  obtain ⟨-, hC, h₁, h₂⟩ := h a b ha hb (ofS s₀) T₁ T₂ u i e1 e2
  exact ⟨toS (BlindBankoffCircle a b), (pts_iff _ _).1 hC, (pts_iff _ _).1 h₁,
    (pts_iff _ _).1 h₂, rfl⟩

/-- What `bankoff_exists` *does* give in blind vocabulary: `blind_80` with the centre
existentially quantified (the explicit centre `2a + i·ab/(a+b)` is not recoverable by
repackaging — see the report: DIFFERENCE, REAL, library weaker). -/
def blind80_weak_stmt : Prop :=
  ∀ (a b : ℝ), 0 < a → 0 < b →
    ∀ (c₁ : BlindCircle) (T₁ T₂ : ℂ),
      BlindUpperHalfPlane c₁.1 →
      BlindInternallyTangent c₁ (BlindOuterCircle a b) →
      BlindExtTangentAtPoint c₁ (BlindFirstCircle a) T₁ →
      BlindExtTangentAtPoint c₁ (BlindSecondCircle a b) T₂ →
      ∃ k : BlindCircle, k.2 = a * b / (a + b) ∧ BlindIsCircle k ∧
        BlindCirclePoints k (BlindCommonPoint a) ∧
        BlindCirclePoints k T₁ ∧ BlindCirclePoints k T₂

theorem bankoffEx_R_to_Bweak : type_of% @Arbelos.bankoff_exists → blind80_weak_stmt := by
  intro h a b ha hb c₁ T₁ T₂ hup hin ht₁ ht₂
  rw [int_iff, outer_eq] at hin
  rw [extAt_iff, first_eq a b] at ht₁
  rw [extAt_iff, second_eq] at ht₂
  obtain ⟨s, hC, h₁, h₂, hr⟩ := h ha hb (toS c₁) hin.2.2 ht₁.2.2.2.isExtTangent
    ht₂.2.2.2.isExtTangent hup T₁ T₂ ht₁.2.2.2 ht₂.2.2.2
  refine ⟨ofS s, hr, ?_, (pts_iff _ _).2 hC, (pts_iff _ _).2 h₁, (pts_iff _ _).2 h₂⟩
  show 0 < s.radius
  rw [hr]; have := ha; have := hb; positivity

theorem blind80_to_weak : blind80_stmt → blind80_weak_stmt := by
  intro h a b ha hb c₁ T₁ T₂ hup hin ht₁ ht₂
  obtain ⟨h0, hC, h₁, h₂⟩ := h a b ha hb c₁ T₁ T₂ hup hin ht₁ ht₂
  exact ⟨_, rfl, h0, hC, h₁, h₂⟩

end L13CmpBankoff
