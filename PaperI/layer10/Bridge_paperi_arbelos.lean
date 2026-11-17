import Arbelos.L14

/-!
# Layer 10: definition bridges

Each locally defined notion of the library is tied to the standard (Mathlib / classical) notion:

* `bridge_vline`, `bridge_perpC` : the local vertical line is the set `{z | re z = x₀}`;
* `bridge_arbelos_area` : the Lebesgue measure of `arbelosRegion` is the classical
  "big half disc minus the two small half discs" value `π(a+b)²/2 - πa²/2 - πb²/2 = πab`;
* `bridge_twin_left`, `bridge_twin_right` : the twin circles exist and have the classical
  Archimedes radius `ab/(a+b) = 1/(1/a + 1/b)`;
* `bankoff_center`, `bridge_bankoff` : every circle through `C` and the two contact points is the
  classical Bankoff circle, centre `2a + i·ab/(a+b)` and radius `ab/(a+b)`;
* `bridge_isSteinerChain_iff` : the Steiner-chain predicate is tangency of every circle to both
  boundary circles and of consecutive circles, in centre-distance form;
* `bridge_powC` : `powC` is Mathlib's `Sphere.power`;
* `bridge_exists_inversion_concentric` : the reduction lemma, stated with Mathlib's `inversion`
  (images of point sets) instead of `invSphere`.
-/

open EuclideanGeometry Complex MeasureTheory

namespace Arbelos

/-- `vline x₀` is the vertical line `{z | z.re = x₀}`. -/
theorem bridge_vline (x₀ : ℝ) : (vline x₀ : Set ℂ) = {z : ℂ | z.re = x₀} := by
  ext z; exact mem_vline_iff

/-- The perpendicular at `C` is the vertical line `{z | z.re = 2a}`. -/
theorem bridge_perpC (a b : ℝ) : (perpC a b : Set ℂ) = {z : ℂ | z.re = 2 * a} :=
  bridge_vline (2 * a)

/-- **Area of the arbelos**, against the classical value: the Lebesgue measure of the arbelos is
the area of the big half disc minus the two small half discs. -/
theorem bridge_arbelos_area {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume (arbelosRegion a b) =
      ENNReal.ofReal (Real.pi * (a + b) ^ 2 / 2 - Real.pi * a ^ 2 / 2 - Real.pi * b ^ 2 / 2) := by
  have hR : 0 < a + b := by linarith
  have hab : 0 ≤ a * b := by positivity
  set D : ℂ := ⟨2 * a, 2 * Real.sqrt (a * b)⟩
  have hs := Real.sq_sqrt hab
  have hD : D ∈ bigS a b := by
    rw [mem_sphere_iff_sq hR.le]
    simp only [bigS, D, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith
  have hDp : D ∈ perpC a b := by rw [perpC, mem_vline_iff]
  rw [arbelos_area ha hb D hD hDp, Complex.volume_ball]
  have hCD : dist (ptC a b) D / 2 = Real.sqrt (a * b) := by
    rw [ptC, Complex.dist_eq_re_im]
    simp only [D, Complex.ofReal_re, Complex.ofReal_im, sub_self, zero_sub, neg_sq]
    rw [zero_pow two_ne_zero, zero_add, mul_pow, hs, show (2 : ℝ) ^ 2 * (a * b) = 2 ^ 2 * (a * b)
      from rfl, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  rw [hCD, ofReal_disc_area _ (Real.sqrt_nonneg _), hs]
  congr 1; ring

/-- The classical twin radius `ab/(a+b)` is half the harmonic mean `2/(1/a + 1/b)`. -/
theorem bridge_twin_radius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * b / (a + b) = 1 / (1 / a + 1 / b) := by
  have : 0 < a + b := by linarith
  field_simp; ring

/-- **Left twin circle**, classical form: it exists, and has radius `ab/(a+b)`. -/
theorem bridge_twin_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ s : Sphere ℂ, 0 < s.center.im ∧ s.center.re < 2 * a ∧ s.IsTangent (perpC a b) ∧
      s.IsIntTangent (bigS a b) ∧ (leftS a b).IsExtTangent s ∧ s.radius = a * b / (a + b) := by
  obtain ⟨s, h0, h1, h2, h3, h4⟩ := twin_left_exists ha hb
  exact ⟨s, h0, h1, h2, h3, h4, twin_left ha hb s h1 h2 h3 h4⟩

/-- **Right twin circle**, classical form: it exists, and has radius `ab/(a+b)`. -/
theorem bridge_twin_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ s : Sphere ℂ, 0 < s.center.im ∧ 2 * a < s.center.re ∧ s.IsTangent (perpC a b) ∧
      s.IsIntTangent (bigS a b) ∧ (rightS a b).IsExtTangent s ∧ s.radius = a * b / (a + b) := by
  obtain ⟨s, h0, h1, h2, h3, h4⟩ := twin_right_exists ha hb
  exact ⟨s, h0, h1, h2, h3, h4, twin_right ha hb s h1 h2 h3 h4⟩

/-- **Bankoff's circle, centre and radius.** Any circle through `C` and the two points where the
incircle touches the small semicircles has centre `2a + i·ab/(a+b)` and radius `ab/(a+b)`. -/
theorem bankoff_center {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s₀ : Sphere ℂ)
    (hbig : s₀.IsIntTangent (bigS a b)) (hleft : (leftS a b).IsExtTangent s₀)
    (hright : (rightS a b).IsExtTangent s₀) (hup : 0 < s₀.center.im)
    (T₁ T₂ : ℂ) (hT₁ : (leftS a b).IsExtTangentAt s₀ T₁) (hT₂ : (rightS a b).IsExtTangentAt s₀ T₂)
    (s : Sphere ℂ) (hC : ptC a b ∈ s) (h₁ : T₁ ∈ s) (h₂ : T₂ ∈ s) :
    s.center = ⟨2 * a, a * b / (a + b)⟩ ∧ s.radius = a * b / (a + b) := by
  have hrad := bankoff ha hb s₀ hbig hleft hright hup T₁ T₂ hT₁ hT₂ s hC h₁ h₂
  refine ⟨?_, hrad⟩
  have hR : 0 < a + b := by linarith
  have h0 := incircle_eq ha hb s₀ hbig hleft hright hup
  subst h0
  have hr := pappus_radius_pos ha hb 1
  have e1 := extTangentAt_eq hT₁ ha hr
  have e2 := extTangentAt_eq hT₂ hb hr
  have hD1 : 0 < a ^ 2 + 2 * a * b + 2 * b ^ 2 := by positivity
  have hD2 : 0 < 2 * a ^ 2 + 2 * a * b + b ^ 2 := by positivity
  have x1 : (a ^ 2 + 2 * a * b + 2 * b ^ 2) * T₁.re = 2 * a * (a + b) ^ 2 := by
    rw [e1]
    simp only [leftS, pappusCircle, famCircle, famDen, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero,
      Nat.cast_one]
    field_simp; ring
  have y1 : (a ^ 2 + 2 * a * b + 2 * b ^ 2) * T₁.im = 2 * a * b * (a + b) := by
    rw [e1]
    simp only [leftS, pappusCircle, famCircle, famDen, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, add_zero,
      sub_zero, zero_add, Nat.cast_one]
    field_simp; ring
  have x2 : (2 * a ^ 2 + 2 * a * b + b ^ 2) * T₂.re = 2 * a * (a + b) * (2 * a + b) := by
    rw [e2]
    simp only [rightS, pappusCircle, famCircle, famDen, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero,
      Nat.cast_one]
    field_simp; ring
  have y2 : (2 * a ^ 2 + 2 * a * b + b ^ 2) * T₂.im = 2 * a * b * (a + b) := by
    rw [e2]
    simp only [rightS, pappusCircle, famCircle, famDen, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, add_zero,
      sub_zero, zero_add, Nat.cast_one]
    field_simp; ring
  have hs0 : 0 ≤ s.radius := s.radius_nonneg_of_mem hC
  rw [mem_sphere_iff_sq hs0] at hC h₁ h₂
  simp only [ptC, Complex.ofReal_re, Complex.ofReal_im] at hC
  set u := s.center.re with hu_def
  set v := s.center.im with hv_def
  set D1 := a ^ 2 + 2 * a * b + 2 * b ^ 2
  set D2 := 2 * a ^ 2 + 2 * a * b + b ^ 2
  have L1 : 4 * a * b * D1 * (b * u - (a + b) * v - a * b) = 0 := by
    linear_combination D1 ^ 2 * (h₁ - hC) - (D1 * T₁.re + 2 * a * (a + b) ^ 2 - 2 * u * D1) * x1
      - (D1 * T₁.im + 2 * a * b * (a + b) - 2 * v * D1) * y1
  have L2 : 4 * a * b * D2 * (a * u + (a + b) * v - 2 * a ^ 2 - a * b) = 0 := by
    linear_combination -(D2 ^ 2 * (h₂ - hC) - (D2 * T₂.re + 2 * a * (a + b) * (2 * a + b) -
      2 * u * D2) * x2 - (D2 * T₂.im + 2 * a * b * (a + b) - 2 * v * D2) * y2)
  have k1 : b * u - (a + b) * v - a * b = 0 := by
    rcases mul_eq_zero.1 L1 with h | h
    · exact absurd h (by positivity)
    · exact h
  have k2 : a * u + (a + b) * v - 2 * a ^ 2 - a * b = 0 := by
    rcases mul_eq_zero.1 L2 with h | h
    · exact absurd h (by positivity)
    · exact h
  have hu : u = 2 * a := by
    have : (a + b) * (u - 2 * a) = 0 := by linear_combination k1 + k2
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hv : v * (a + b) = a * b := by rw [hu] at k1; linear_combination -k1
  apply Complex.ext
  · exact hu
  · show v = a * b / (a + b)
    rw [eq_div_iff hR.ne']; exact hv

/-- **Bankoff's circle**, classical form: the circle through `C` and the two contact points is
the sphere with centre `2a + i·ab/(a+b)` and radius `ab/(a+b)`, and that sphere does pass through
the three points. -/
theorem bridge_bankoff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s₀ : Sphere ℂ)
    (hbig : s₀.IsIntTangent (bigS a b)) (hleft : (leftS a b).IsExtTangent s₀)
    (hright : (rightS a b).IsExtTangent s₀) (hup : 0 < s₀.center.im)
    (T₁ T₂ : ℂ) (hT₁ : (leftS a b).IsExtTangentAt s₀ T₁) (hT₂ : (rightS a b).IsExtTangentAt s₀ T₂) :
    (∀ s : Sphere ℂ, ptC a b ∈ s → T₁ ∈ s → T₂ ∈ s →
      s = (⟨⟨2 * a, a * b / (a + b)⟩, a * b / (a + b)⟩ : Sphere ℂ)) ∧
    ptC a b ∈ (⟨⟨2 * a, a * b / (a + b)⟩, a * b / (a + b)⟩ : Sphere ℂ) ∧
    T₁ ∈ (⟨⟨2 * a, a * b / (a + b)⟩, a * b / (a + b)⟩ : Sphere ℂ) ∧
    T₂ ∈ (⟨⟨2 * a, a * b / (a + b)⟩, a * b / (a + b)⟩ : Sphere ℂ) := by
  have key : ∀ s : Sphere ℂ, ptC a b ∈ s → T₁ ∈ s → T₂ ∈ s →
      s = (⟨⟨2 * a, a * b / (a + b)⟩, a * b / (a + b)⟩ : Sphere ℂ) := by
    intro s hC h₁ h₂
    obtain ⟨hc, hr⟩ := bankoff_center ha hb s₀ hbig hleft hright hup T₁ T₂ hT₁ hT₂ s hC h₁ h₂
    exact Sphere.ext hc hr
  obtain ⟨s, hC, h₁, h₂, -, -⟩ := bankoff_exists ha hb s₀ hbig hleft hright hup T₁ T₂ hT₁ hT₂
  have e := key s hC h₁ h₂
  rw [e] at hC h₁ h₂
  exact ⟨key, hC, h₁, h₂⟩

/-- **Steiner chains**, in centre-distance form: every circle has positive radius, touches the
inner circle externally and the outer circle internally, and touches the next circle externally. -/
theorem bridge_isSteinerChain_iff (S₁ S₂ : Sphere ℂ) (n : ℕ) (c : ZMod n → Sphere ℂ) :
    IsSteinerChain S₁ S₂ n c ↔ ∀ i, 0 < (c i).radius ∧ 0 ≤ S₁.radius ∧
      dist S₁.center (c i).center = S₁.radius + (c i).radius ∧
      dist (c i).center S₂.center = S₂.radius - (c i).radius ∧
      dist (c i).center (c (i + 1)).center = (c i).radius + (c (i + 1)).radius := by
  unfold IsSteinerChain
  simp only [Sphere.isExtTangent_iff_dist_center, Sphere.isIntTangent_iff_dist_center]
  constructor
  · intro h i
    obtain ⟨h0, ⟨e1, r1, -⟩, ⟨e2, -, -⟩, ⟨e3, -, -⟩⟩ := h i
    exact ⟨h0, r1, e1, e2, e3⟩
  · intro h i
    obtain ⟨h0, r1, e1, e2, e3⟩ := h i
    have h1 := (h (i + 1)).1
    have hd := dist_nonneg (x := (c i).center) (y := S₂.center)
    exact ⟨h0, ⟨e1, r1, h0.le⟩, ⟨e2, h0.le, by linarith⟩, ⟨e3, h0.le, h1.le⟩⟩

/-- `powC` is Mathlib's power of a point with respect to a sphere. -/
theorem bridge_powC (c : ℂ) (s : Sphere ℂ) : powC c s = s.power c := by
  rw [powC, Sphere.power, dist_eq_norm, norm_sub_rev]

/-- **Reduction lemma with Mathlib's `inversion`.** Two non-concentric circles, one strictly
inside the other, are mapped by the inversion `EuclideanGeometry.inversion c 1` (for a suitable
centre `c` outside both) onto two concentric circles. -/
theorem bridge_exists_inversion_concentric (S₁ S₂ : Sphere ℂ) (h₁ : 0 < S₁.radius)
    (hne : S₁.center ≠ S₂.center) (hin : dist S₁.center S₂.center < S₂.radius - S₁.radius) :
    ∃ c : ℂ, 0 < S₁.power c ∧ 0 < S₂.power c ∧ ∃ T₁ T₂ : Sphere ℂ, T₁.center = T₂.center ∧
      inversion c 1 '' (S₁ : Set ℂ) = (T₁ : Set ℂ) ∧ inversion c 1 '' (S₂ : Set ℂ) = (T₂ : Set ℂ) := by
  obtain ⟨c, hp₁, hp₂, hcen⟩ := exists_inversion_concentric S₁ S₂ h₁ hne hin
  have hr₂ : 0 ≤ S₂.radius := by have := dist_nonneg (x := S₁.center) (y := S₂.center); linarith
  have hq₁ : ‖S₁.center - c‖ ^ 2 ≠ S₁.radius ^ 2 := by
    rw [powC] at hp₁; exact fun h ↦ by rw [h, sub_self] at hp₁; exact lt_irrefl _ hp₁
  have hq₂ : ‖S₂.center - c‖ ^ 2 ≠ S₂.radius ^ 2 := by
    rw [powC] at hp₂; exact fun h ↦ by rw [h, sub_self] at hp₂; exact lt_irrefl _ hp₂
  refine ⟨c, (bridge_powC c S₁) ▸ hp₁, (bridge_powC c S₂) ▸ hp₂, invSphere c 1 S₁, invSphere c 1 S₂,
    hcen, image_inversion_sphere one_ne_zero h₁.le hq₁, image_inversion_sphere one_ne_zero hr₂ hq₂⟩

end Arbelos
