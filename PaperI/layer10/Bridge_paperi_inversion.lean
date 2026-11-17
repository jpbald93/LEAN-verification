import Inversion.L14

/-!
# Layer 10: definition bridges

Each locally defined notion of the library is tied to the standard (Mathlib / classical) notion:

* `bridge_invPt`, `bridge_invPt_bijOn` : `invPt R` is Mathlib's `EuclideanGeometry.inversion 0 R`
  as a function, and a bijection (an involution) of the punctured space for `R ≠ 0`;
* `bridge_extTangent`, `bridge_intTangent` : the signed-radius tangency condition
  `dist(c₁, c₂)² = (r₁ + r₂)²` used by `descartes` is Mathlib's `Sphere.IsExtTangent` for two
  positive radii and `Sphere.IsIntTangent` when the second circle encloses the first (negative
  signed radius);
* `bridge_descartes_classical` : for four mutually externally tangent circles (Mathlib
  tangency), `k₄ = k₁ + k₂ + k₃ ± 2√(k₁k₂ + k₂k₃ + k₃k₁)`;
* `bridge_descartesForm`, `bridge_isDescartes` : the Descartes forms against the classical
  relation `(∑ kᵢ)² = 2 ∑ kᵢ²`;
* `bridge_apolloMove` : the Apollonian move replaces a curvature by the other root of the
  Descartes quadratic (Vieta: the two roots sum to `2(k₁ + k₂ + k₃)`);
* `bridge_cross_iff_collinear`, `bridge_peaucellier_collinear` : the coordinate condition
  `P.re * Q.im - P.im * Q.re = 0` of `peaucellier_collinear` is Mathlib's
  `Collinear ℝ {0, P, Q}`.
-/

open EuclideanGeometry

namespace Inversion

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `invPt R` is Mathlib's inversion in the sphere of radius `R` centred at `0`. -/
theorem bridge_invPt (R : ℝ) : (invPt R : V → V) = EuclideanGeometry.inversion (0 : V) R :=
  funext (invPt_eq_inversion R)

/-- On the punctured space `V \ {0}`, `invPt R` (`R ≠ 0`) is a bijection, agreeing with
Mathlib's `inversion 0 R`. -/
theorem bridge_invPt_bijOn {R : ℝ} (hR : R ≠ 0) :
    Set.EqOn (invPt R) (EuclideanGeometry.inversion (0 : V) R) {0}ᶜ ∧
      Set.BijOn (invPt R) ({0}ᶜ : Set V) {0}ᶜ := by
  refine ⟨fun P _ ↦ invPt_eq_inversion R P, ?_⟩
  have hm : Set.MapsTo (invPt R) ({0}ᶜ : Set V) {0}ᶜ := fun P hP ↦ invPt_ne_zero hR hP
  exact Set.InvOn.bijOn ⟨fun P _ ↦ invPt_invPt hR P, fun P _ ↦ invPt_invPt hR P⟩ hm hm

end General

/-- **External tangency.** For positive radii, the signed tangency condition of `descartes` is
Mathlib's external tangency. -/
theorem bridge_extTangent {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2 ↔
      (⟨c₁, r₁⟩ : Sphere ℂ).IsExtTangent (⟨c₂, r₂⟩ : Sphere ℂ) := by
  rw [Sphere.isExtTangent_iff_dist_center]
  simp only
  constructor
  · intro h
    exact ⟨(sq_eq_sq₀ dist_nonneg (by positivity)).1 h, h₁.le, h₂.le⟩
  · rintro ⟨h, -, -⟩; rw [h]

/-- **Internal tangency.** If the second circle has negative signed radius `r₂` (it encloses the
first, `r₁ ≤ -r₂`), the signed tangency condition is Mathlib's internal tangency of the circle of
radius `r₁` in the circle of radius `-r₂`. -/
theorem bridge_intTangent {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₂ < 0) (h₁₂ : r₁ ≤ -r₂) :
    dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2 ↔
      (⟨c₁, r₁⟩ : Sphere ℂ).IsIntTangent (⟨c₂, -r₂⟩ : Sphere ℂ) := by
  rw [Sphere.isIntTangent_iff_dist_center]
  simp only
  constructor
  · intro h
    have e : (r₁ + r₂) ^ 2 = (-r₂ - r₁) ^ 2 := by ring
    rw [e] at h
    exact ⟨(sq_eq_sq₀ dist_nonneg (by linarith)).1 h, h₁.le, by linarith⟩
  · rintro ⟨h, -, -⟩; rw [h]; ring

/-- The Descartes form vanishes exactly on the classical relation `(∑ kᵢ)² = 2 ∑ kᵢ²`. -/
theorem bridge_descartesForm (k₁ k₂ k₃ k₄ : ℝ) :
    descartesForm k₁ k₂ k₃ k₄ = 0 ↔
      (k₁ + k₂ + k₃ + k₄) ^ 2 = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2) := by
  unfold descartesForm; exact sub_eq_zero

/-- `IsDescartes` is the classical Descartes relation for the real curvatures. -/
theorem bridge_isDescartes (a b c d : ℤ) :
    IsDescartes (a, b, c, d) ↔
      ((a : ℝ) + b + c + d) ^ 2 = 2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 + (d : ℝ) ^ 2) := by
  rw [← bridge_descartesForm, ← descartesFormZ_cast]
  unfold IsDescartes
  exact_mod_cast Iff.rfl

/-- **Descartes' theorem, classical form.** Four mutually externally tangent circles (Mathlib
tangency) with curvatures `kᵢ = 1/rᵢ` satisfy `k₄ = k₁ + k₂ + k₃ ± 2√(k₁k₂ + k₂k₃ + k₃k₁)`. -/
theorem bridge_descartes_classical {c₁ c₂ c₃ c₄ : ℂ} {r₁ r₂ r₃ r₄ : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) (h₃ : 0 < r₃) (h₄ : 0 < r₄)
    (t₁₂ : (⟨c₁, r₁⟩ : Sphere ℂ).IsExtTangent ⟨c₂, r₂⟩)
    (t₁₃ : (⟨c₁, r₁⟩ : Sphere ℂ).IsExtTangent ⟨c₃, r₃⟩)
    (t₁₄ : (⟨c₁, r₁⟩ : Sphere ℂ).IsExtTangent ⟨c₄, r₄⟩)
    (t₂₃ : (⟨c₂, r₂⟩ : Sphere ℂ).IsExtTangent ⟨c₃, r₃⟩)
    (t₂₄ : (⟨c₂, r₂⟩ : Sphere ℂ).IsExtTangent ⟨c₄, r₄⟩)
    (t₃₄ : (⟨c₃, r₃⟩ : Sphere ℂ).IsExtTangent ⟨c₄, r₄⟩) :
    1 / r₄ = 1 / r₁ + 1 / r₂ + 1 / r₃ +
        2 * √(1 / r₁ * (1 / r₂) + 1 / r₂ * (1 / r₃) + 1 / r₃ * (1 / r₁)) ∨
      1 / r₄ = 1 / r₁ + 1 / r₂ + 1 / r₃ -
        2 * √(1 / r₁ * (1 / r₂) + 1 / r₂ * (1 / r₃) + 1 / r₃ * (1 / r₁)) := by
  have h := descartes h₁.ne' h₂.ne' h₃.ne' h₄.ne' ((bridge_extTangent h₁ h₂).2 t₁₂)
    ((bridge_extTangent h₁ h₃).2 t₁₃) ((bridge_extTangent h₁ h₄).2 t₁₄)
    ((bridge_extTangent h₂ h₃).2 t₂₃) ((bridge_extTangent h₂ h₄).2 t₂₄)
    ((bridge_extTangent h₃ h₄).2 t₃₄)
  exact ((descartes_solve _ _ _ _).1 ((bridge_descartesForm _ _ _ _).2 h)).2

/-- **The Apollonian move is Vieta's involution.** Moving the last curvature of a Descartes
quadruple gives the other root `d'` of the Descartes quadratic in `k₄`: both satisfy the relation
and `d + d' = 2(a + b + c)`. -/
theorem bridge_apolloMove {a b c d : ℤ} (h : IsDescartes (a, b, c, d)) :
    apolloMove 3 (a, b, c, d) = (a, b, c, 2 * (a + b + c) - d) ∧
      IsDescartes (apolloMove 3 (a, b, c, d)) ∧ d + (2 * (a + b + c) - d) = 2 * (a + b + c) :=
  ⟨rfl, isDescartes_apolloMove 3 h, by ring⟩

/-- The coordinate collinearity condition is Mathlib's `Collinear` for `{0, P, Q}`. -/
theorem bridge_cross_iff_collinear (P Q : ℂ) :
    P.re * Q.im - P.im * Q.re = 0 ↔ Collinear ℝ ({0, P, Q} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := (0 : ℂ)) (by simp)]
  constructor
  · intro h
    by_cases hP : P = 0
    · refine ⟨Q, ?_⟩
      intro Y hY
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
      rcases hY with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp [hP]⟩
      · exact ⟨1, by simp⟩
    · have hn : P.re ^ 2 + P.im ^ 2 ≠ 0 := by
        intro h0; apply hP
        apply Complex.ext <;> simp <;> nlinarith [sq_nonneg P.re, sq_nonneg P.im]
      refine ⟨P, ?_⟩
      intro Y hY
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
      rcases hY with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · refine ⟨(P.re * Y.re + P.im * Y.im) / (P.re ^ 2 + P.im ^ 2), ?_⟩
        apply Complex.ext <;>
          simp only [vadd_eq_add, add_zero, Complex.smul_re, Complex.smul_im, smul_eq_mul] <;>
          field_simp
        · linear_combination (-P.im) * h
        · linear_combination P.re * h
  · rintro ⟨v, hv⟩
    obtain ⟨s, hs⟩ := hv P (by simp)
    obtain ⟨t, ht⟩ := hv Q (by simp)
    rw [vadd_eq_add, add_zero] at hs ht
    rw [hs, ht]
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring

/-- **Peaucellier–Lipkin**, Mathlib form: the pivot `0` and the two rhombus vertices `P, Q` are
collinear. -/
theorem bridge_peaucellier_collinear {a b : ℝ} {A B P Q : ℂ} (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a) (hQA : dist Q A = a) (hQB : dist Q B = a)
    (hAB : A ≠ B) : Collinear ℝ ({0, P, Q} : Set ℂ) :=
  (bridge_cross_iff_collinear P Q).1 (peaucellier_collinear hA hB hPA hPB hQA hQB hAB)

end Inversion
