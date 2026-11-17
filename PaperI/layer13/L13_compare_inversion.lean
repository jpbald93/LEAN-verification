import Inversion

/-!
# Layer 13 comparison (machine john): blind statements vs the `Inversion` library

Blind definitions are copied verbatim from `PaperIBlind.lean` (namespace `L13CmpInv`).
Real statements are referenced only through `type_of%`; no library theorem is used in a
proof body (library *definitions* `invPt`, `descartesForm`, `descartesFormZ` are unfolded).
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators

namespace L13CmpInv

/-! ## Verbatim blind definitions -/

def BlindInversion (center : ℂ) (radius : ℝ) (z : ℂ) : ℂ :=
  center + ((radius ^ 2 / ‖z - center‖ ^ 2 : ℝ) : ℂ) * (z - center)

def BlindCurvature (signedRadius : ℝ) : ℝ :=
  1 / signedRadius

def BlindDescartesCurvatures (k : Fin 4 → ℝ) : Prop :=
  (∑ i : Fin 4, k i) ^ 2 = 2 * ∑ i : Fin 4, (k i) ^ 2

def BlindApollonianMove (k : Fin 4 → ℝ) (i : Fin 4) : Fin 4 → ℝ :=
  fun j =>
    if j = i then 2 * ∑ h ∈ Finset.univ.erase i, k h - k i else k j

def BlindSignedTangency {X : Type*} [MetricSpace X]
    (c d : X) (r s : ℝ) : Prop :=
  dist c d ^ 2 = (r + s) ^ 2

/-! ## thm:ptolemyinv — `ptolemy_inequality` vs `blind_57` -/

def blind57_stmt.{u} : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P Q S : V) (R : ℝ), P ≠ 0 → Q ≠ 0 → S ≠ 0 → R ≠ 0 →
    dist P S * ‖Q‖ ≤ dist P Q * ‖S‖ + dist Q S * ‖P‖

theorem ptIneq_R_to_B.{u} : type_of% @Inversion.ptolemy_inequality.{u} → blind57_stmt.{u} :=
  fun h _ _ _ P Q S _ hP hQ hS _ ↦ h hP hQ hS

theorem ptIneq_B_to_R.{u} : blind57_stmt.{u} → type_of% @Inversion.ptolemy_inequality.{u} :=
  fun h _ _ _ _ _ _ hP hQ hS ↦ h _ _ _ 1 hP hQ hS one_ne_zero

/-! ## thm:ptolemyinv — `collinear_iff_dist_boundary` vs `blind_58` -/

def blind58_stmt.{u} : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (P Q S : V),
    Collinear ℝ ({P, Q, S} : Set V) ↔
      dist P Q + dist Q S = dist P S ∨
      dist Q S + dist S P = dist Q P ∨
      dist S P + dist P Q = dist S Q

theorem colDist_R_to_B.{u} :
    type_of% @Inversion.collinear_iff_dist_boundary.{u} → blind58_stmt.{u} :=
  fun h _ _ _ P Q S ↦ h P Q S

theorem colDist_B_to_R.{u} :
    blind58_stmt.{u} → type_of% @Inversion.collinear_iff_dist_boundary.{u} :=
  fun h _ _ _ X Y Z ↦ h X Y Z

/-! ## thm:ptolemyinv — `ptolemy_concyclic` vs `blind_60` -/

def blind60_stmt : Prop :=
  ∀ (P Q S K : ℂ) (R : ℝ), P ≠ 0 → Q ≠ 0 → S ≠ 0 → R ≠ 0 →
    ‖P - K‖ = ‖K‖ → ‖Q - K‖ = ‖K‖ → ‖S - K‖ = ‖K‖ →
    dist P Q * ‖S‖ + dist Q S * ‖P‖ = dist P S * ‖Q‖ ∨
    dist Q S * ‖P‖ + dist S P * ‖Q‖ = dist Q P * ‖S‖ ∨
    dist S P * ‖Q‖ + dist P Q * ‖S‖ = dist S Q * ‖P‖

theorem ptConc_R_to_B : type_of% @Inversion.ptolemy_concyclic → blind60_stmt :=
  fun h _ _ _ _ _ hP hQ hS _ hPK hQK hSK ↦ h hP hQ hS hPK hQK hSK

theorem ptConc_B_to_R : blind60_stmt → type_of% @Inversion.ptolemy_concyclic :=
  fun h _ _ _ _ hP hQ hS hPK hQK hSK ↦ h _ _ _ _ 1 hP hQ hS one_ne_zero hPK hQK hSK

/-! ## thm:peaucellier — `peaucellier_add`, `peaucellier_inner`, `peaucellier_collinear`
vs `blind_61`, `blind_62`, `blind_63` -/

def blind61_stmt : Prop :=
  ∀ (A B P Q : ℂ) (a b : ℝ), ‖A‖ = b → ‖B‖ = b →
    dist P A = a → dist P B = a → dist Q A = a → dist Q B = a → A ≠ B →
    Collinear ℝ ({(0 : ℂ), P, Q} : Set ℂ)

def blind62_stmt : Prop :=
  ∀ (A B P Q : ℂ) (a b : ℝ), ‖A‖ = b → ‖B‖ = b →
    dist P A = a → dist P B = a → dist Q A = a → dist Q B = a → A ≠ B → P ≠ Q →
    P + Q = A + B

def blind63_stmt : Prop :=
  ∀ (A B P Q : ℂ) (a b : ℝ), ‖A‖ = b → ‖B‖ = b →
    dist P A = a → dist P B = a → dist Q A = a → dist Q B = a → A ≠ B → P ≠ Q →
    inner ℝ P Q = b ^ 2 - a ^ 2

/-- Mathlib-only bridge: `0, P, Q` collinear iff the planar cross product vanishes. -/
theorem collinear_zero_iff_cross (P Q : ℂ) :
    Collinear ℝ ({(0 : ℂ), P, Q} : Set ℂ) ↔ P.re * Q.im - P.im * Q.re = 0 := by
  rw [collinear_iff_of_mem (p₀ := (0 : ℂ)) (by simp)]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := hv P (by simp)
    obtain ⟨s, hs⟩ := hv Q (by simp)
    rw [vadd_eq_add, add_zero] at hr hs
    rw [hr, hs]
    simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  · intro h
    by_cases hP : P = 0
    · refine ⟨Q, fun p hp ↦ ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp [hP]⟩
      · exact ⟨1, by simp⟩
    · have hN : P.re ^ 2 + P.im ^ 2 ≠ 0 := by
        intro h0
        apply hP
        apply Complex.ext
        · simp only [Complex.zero_re]; nlinarith [sq_nonneg P.re, sq_nonneg P.im]
        · simp only [Complex.zero_im]; nlinarith [sq_nonneg P.re, sq_nonneg P.im]
      refine ⟨P, fun p hp ↦ ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · refine ⟨(p.re * P.re + p.im * P.im) / (P.re ^ 2 + P.im ^ 2), ?_⟩
        rw [vadd_eq_add, add_zero]
        apply Complex.ext
        · simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero]
          field_simp
          linear_combination (-P.im) * h
        · simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, add_zero]
          field_simp
          linear_combination P.re * h

theorem peauc3_R_to_B :
    (type_of% @Inversion.peaucellier_add ∧ type_of% @Inversion.peaucellier_inner ∧
      type_of% @Inversion.peaucellier_collinear) →
      (blind61_stmt ∧ blind62_stmt ∧ blind63_stmt) := by
  rintro ⟨hadd, hinn, hcol⟩
  refine ⟨fun A B P Q a b h1 h2 h3 h4 h5 h6 h7 ↦ ?_,
    fun A B P Q a b h1 h2 h3 h4 h5 h6 h7 h8 ↦ hadd h1 h2 h3 h4 h5 h6 h7 h8,
    fun A B P Q a b h1 h2 h3 h4 h5 h6 h7 h8 ↦ hinn h1 h2 h3 h4 h5 h6 h7 h8⟩
  exact (collinear_zero_iff_cross P Q).2 (hcol h1 h2 h3 h4 h5 h6 h7)

theorem peauc3_B_to_R :
    (blind61_stmt ∧ blind62_stmt ∧ blind63_stmt) →
      (type_of% @Inversion.peaucellier_add ∧ type_of% @Inversion.peaucellier_inner ∧
        type_of% @Inversion.peaucellier_collinear) := by
  rintro ⟨h61, h62, h63⟩
  refine ⟨fun h1 h2 h3 h4 h5 h6 h7 h8 ↦ h62 _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8,
    fun h1 h2 h3 h4 h5 h6 h7 h8 ↦ h63 _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8,
    fun h1 h2 h3 h4 h5 h6 h7 ↦ ?_⟩
  exact (collinear_zero_iff_cross _ _).1 (h61 _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7)

/-! ## thm:peaucellier — `peaucellier`, `peaucellier_classic`, `peaucellier_line`,
`peaucellier_classic_line` vs `blind_64` … `blind_69` -/

theorem invPt_eq_blind (R : ℝ) (P : ℂ) : Inversion.invPt R P = BlindInversion 0 R P := by
  simp only [Inversion.invPt, BlindInversion, sub_zero, zero_add, Complex.real_smul]

def blind64_stmt : Prop :=
  ∀ (A B P Q : ℂ) (a b R : ℝ), ‖A‖ = b → ‖B‖ = b →
    dist P A = a → dist P B = a → dist Q A = a → dist Q B = a → A ≠ B → P ≠ Q → R ≠ 0 →
    b ^ 2 - a ^ 2 = R ^ 2 → Q = BlindInversion 0 R P

def blind65_stmt : Prop :=
  ∀ (A B P Q : ℂ) (a b R : ℝ), ‖A‖ = b → ‖B‖ = b →
    dist P A = a → dist P B = a → dist Q A = a → dist Q B = a → A ≠ B → P ≠ Q → R ≠ 0 →
    b ^ 2 - a ^ 2 = R ^ 2 → ‖P‖ * ‖Q‖ = R ^ 2

def blind66_stmt : Prop :=
  ∀ (A B P Q C : ℂ) (a b R : ℝ), ‖A‖ = b → ‖B‖ = b →
    dist P A = a → dist P B = a → dist Q A = a → dist Q B = a → A ≠ B → P ≠ Q → R ≠ 0 →
    b ^ 2 - a ^ 2 = R ^ 2 → ‖P - C‖ = ‖C‖ → inner ℝ Q C = R ^ 2 / 2

def blind67_stmt : Prop :=
  ∀ (A B P Q : ℂ) (a b R : ℝ), ‖A‖ = b → ‖B‖ = b →
    dist P A = a → dist P B = a → dist Q A = a → dist Q B = a → A ≠ B → P ≠ Q → R ≠ 0 →
    a ^ 2 - b ^ 2 = R ^ 2 → Q = -BlindInversion 0 R P

def blind68_stmt : Prop :=
  ∀ (A B P Q : ℂ) (a b R : ℝ), ‖A‖ = b → ‖B‖ = b →
    dist P A = a → dist P B = a → dist Q A = a → dist Q B = a → A ≠ B → P ≠ Q → R ≠ 0 →
    a ^ 2 - b ^ 2 = R ^ 2 → ‖P‖ * ‖Q‖ = R ^ 2

def blind69_stmt : Prop :=
  ∀ (A B P Q C : ℂ) (a b R : ℝ), ‖A‖ = b → ‖B‖ = b →
    dist P A = a → dist P B = a → dist Q A = a → dist Q B = a → A ≠ B → P ≠ Q → R ≠ 0 →
    a ^ 2 - b ^ 2 = R ^ 2 → ‖P - C‖ = ‖C‖ → inner ℝ Q C = -R ^ 2 / 2

theorem peauc4_R_to_B :
    (type_of% @Inversion.peaucellier ∧ type_of% @Inversion.peaucellier_classic ∧
      type_of% @Inversion.peaucellier_line ∧ type_of% @Inversion.peaucellier_classic_line) →
      (blind64_stmt ∧ blind65_stmt ∧ blind66_stmt ∧ blind67_stmt ∧ blind68_stmt ∧
        blind69_stmt) := by
  rintro ⟨hn, hc, hnl, hcl⟩
  refine ⟨fun A B P Q a b R h1 h2 h3 h4 h5 h6 h7 h8 hR hab ↦ ?_,
    fun A B P Q a b R h1 h2 h3 h4 h5 h6 h7 h8 hR hab ↦ (hc hR hab h1 h2 h3 h4 h5 h6 h7 h8).2,
    fun A B P Q C a b R h1 h2 h3 h4 h5 h6 h7 h8 hR hab hC ↦
      hcl hR hab h1 h2 h3 h4 h5 h6 h7 h8 hC,
    fun A B P Q a b R h1 h2 h3 h4 h5 h6 h7 h8 hR hab ↦ ?_,
    fun A B P Q a b R h1 h2 h3 h4 h5 h6 h7 h8 hR hab ↦ (hn hR hab h1 h2 h3 h4 h5 h6 h7 h8).2,
    fun A B P Q C a b R h1 h2 h3 h4 h5 h6 h7 h8 hR hab hC ↦ ?_⟩
  · rw [← invPt_eq_blind]; exact (hc hR hab h1 h2 h3 h4 h5 h6 h7 h8).1
  · rw [← invPt_eq_blind]; exact (hn hR hab h1 h2 h3 h4 h5 h6 h7 h8).1
  · rw [neg_div]; exact hnl hR hab h1 h2 h3 h4 h5 h6 h7 h8 hC

theorem peauc4_B_to_R :
    (blind64_stmt ∧ blind65_stmt ∧ blind66_stmt ∧ blind67_stmt ∧ blind68_stmt ∧
        blind69_stmt) →
      (type_of% @Inversion.peaucellier ∧ type_of% @Inversion.peaucellier_classic ∧
        type_of% @Inversion.peaucellier_line ∧ type_of% @Inversion.peaucellier_classic_line) := by
  rintro ⟨h64, h65, h66, h67, h68, h69⟩
  refine ⟨fun hR hab h1 h2 h3 h4 h5 h6 h7 h8 ↦ ⟨?_, h68 _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 hR hab⟩,
    fun hR hab h1 h2 h3 h4 h5 h6 h7 h8 ↦ ⟨?_, h65 _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 hR hab⟩,
    fun hR hab h1 h2 h3 h4 h5 h6 h7 h8 hC ↦ ?_,
    fun hR hab h1 h2 h3 h4 h5 h6 h7 h8 hC ↦ h66 _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 hR hab hC⟩
  · rw [invPt_eq_blind]; exact h67 _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 hR hab
  · rw [invPt_eq_blind]; exact h64 _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 hR hab
  · rw [← neg_div]; exact h69 _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 hR hab hC

/-! ## thm:descartes — `descartes` vs `blind_70` -/

def blind70_stmt : Prop :=
  ∀ (c : Fin 4 → ℂ) (r : Fin 4 → ℝ), (∀ i, r i ≠ 0) →
    (∀ i j, i < j → BlindSignedTangency (c i) (c j) (r i) (r j)) →
    BlindDescartesCurvatures (fun i => BlindCurvature (r i))

theorem descartes_R_to_B : type_of% @Inversion.descartes → blind70_stmt := by
  intro h c r hr ht
  have t : ∀ i j : Fin 4, i < j → dist (c i) (c j) ^ 2 = (r i + r j) ^ 2 := ht
  have := h (hr 0) (hr 1) (hr 2) (hr 3) (t 0 1 (by decide)) (t 0 2 (by decide))
    (t 0 3 (by decide)) (t 1 2 (by decide)) (t 1 3 (by decide)) (t 2 3 (by decide))
  simp only [BlindDescartesCurvatures, BlindCurvature, Fin.sum_univ_four]
  exact this

theorem descartes_B_to_R : blind70_stmt → type_of% @Inversion.descartes := by
  intro h c₁ c₂ c₃ c₄ r₁ r₂ r₃ r₄ h₁ h₂ h₃ h₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
  have := h ![c₁, c₂, c₃, c₄] ![r₁, r₂, r₃, r₄]
    (fun i ↦ by fin_cases i <;> assumption)
    (fun i j hij ↦ by
      fin_cases i <;> fin_cases j <;> simp_all [BlindSignedTangency] <;>
        exact absurd hij (by decide))
  simp only [BlindDescartesCurvatures, BlindCurvature, Fin.sum_univ_four] at this
  exact this

/-! ## thm:soddy — `soddy` vs `blind_71` -/

def blind71_stmt : Prop :=
  ∀ (c : Fin 5 → EuclideanSpace ℝ (Fin 3)) (r : Fin 5 → ℝ), (∀ i, r i ≠ 0) →
    (∀ i j, i < j → BlindSignedTangency (c i) (c j) (r i) (r j)) →
    (∑ i : Fin 5, BlindCurvature (r i)) ^ 2 = 3 * ∑ i : Fin 5, (BlindCurvature (r i)) ^ 2

theorem soddy_R_to_B : type_of% @Inversion.soddy → blind71_stmt := by
  intro h c r hr ht
  have t : ∀ i j : Fin 5, i < j → dist (c i) (c j) ^ 2 = (r i + r j) ^ 2 := ht
  have := h (hr 0) (hr 1) (hr 2) (hr 3) (hr 4) (t 0 1 (by decide)) (t 0 2 (by decide))
    (t 0 3 (by decide)) (t 0 4 (by decide)) (t 1 2 (by decide)) (t 1 3 (by decide))
    (t 1 4 (by decide)) (t 2 3 (by decide)) (t 2 4 (by decide)) (t 3 4 (by decide))
  simp only [BlindCurvature, Fin.sum_univ_five]
  exact this

theorem soddy_B_to_R : blind71_stmt → type_of% @Inversion.soddy := by
  intro h c₁ c₂ c₃ c₄ c₅ r₁ r₂ r₃ r₄ r₅ h₁ h₂ h₃ h₄ h₅ h₁₂ h₁₃ h₁₄ h₁₅ h₂₃ h₂₄ h₂₅ h₃₄ h₃₅ h₄₅
  have := h ![c₁, c₂, c₃, c₄, c₅] ![r₁, r₂, r₃, r₄, r₅]
    (fun i ↦ by fin_cases i <;> assumption)
    (fun i j hij ↦ by
      fin_cases i <;> fin_cases j <;> simp_all [BlindSignedTangency] <;>
        exact absurd hij (by decide))
  simp only [BlindCurvature, Fin.sum_univ_five] at this
  exact this

/-! ## thm:apollonian — `descartes_solve`, `descartes_vieta` vs `blind_72`, `blind_73`, `blind_74` -/

theorem blindDesc_iff (k₁ k₂ k₃ k₄ : ℝ) :
    BlindDescartesCurvatures ![k₁, k₂, k₃, k₄] ↔ Inversion.descartesForm k₁ k₂ k₃ k₄ = 0 := by
  have e : BlindDescartesCurvatures ![k₁, k₂, k₃, k₄] ↔
      (k₁ + k₂ + k₃ + k₄) ^ 2 = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2) := by
    unfold BlindDescartesCurvatures
    rw [Fin.sum_univ_four, Fin.sum_univ_four]
    rfl
  rw [e, Inversion.descartesForm, sub_eq_zero]

def blind72_stmt : Prop :=
  ∀ (k₁ k₂ k₃ k₄ : ℝ),
    BlindDescartesCurvatures ![k₁, k₂, k₃, k₄] ↔
      k₁ * k₂ + k₂ * k₃ + k₃ * k₁ ≥ 0 ∧
        (k₄ = k₁ + k₂ + k₃ + 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ∨
         k₄ = k₁ + k₂ + k₃ - 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁))

def blind73_stmt : Prop :=
  ∀ (k₁ k₂ k₃ kplus kminus : ℝ),
    BlindDescartesCurvatures ![k₁, k₂, k₃, kplus] →
    BlindDescartesCurvatures ![k₁, k₂, k₃, kminus] → kplus ≠ kminus →
    kplus + kminus = 2 * (k₁ + k₂ + k₃)

def blind74_stmt : Prop :=
  ∀ (k₁ k₂ k₃ kplus kminus : ℝ),
    BlindDescartesCurvatures ![k₁, k₂, k₃, kplus] →
    BlindDescartesCurvatures ![k₁, k₂, k₃, kminus] → kplus ≠ kminus →
    kplus * kminus = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) - (k₁ + k₂ + k₃) ^ 2

theorem solve_R_to_B : type_of% @Inversion.descartes_solve → blind72_stmt := by
  intro h k₁ k₂ k₃ k₄
  rw [blindDesc_iff, h, ge_iff_le]

theorem solve_B_to_R : blind72_stmt → type_of% @Inversion.descartes_solve := by
  intro h k₁ k₂ k₃ k₄
  rw [← blindDesc_iff, h, ge_iff_le]

theorem vieta_R_to_B : type_of% @Inversion.descartes_vieta → blind73_stmt ∧ blind74_stmt :=
  fun h ↦ ⟨fun _ _ _ _ _ hp hm hne ↦
      (h ((blindDesc_iff _ _ _ _).1 hp) ((blindDesc_iff _ _ _ _).1 hm) hne).1,
    fun _ _ _ _ _ hp hm hne ↦
      (h ((blindDesc_iff _ _ _ _).1 hp) ((blindDesc_iff _ _ _ _).1 hm) hne).2⟩

theorem vieta_B_to_R : blind73_stmt ∧ blind74_stmt → type_of% @Inversion.descartes_vieta :=
  fun h _ _ _ _ _ hp hm hne ↦
    ⟨h.1 _ _ _ _ _ ((blindDesc_iff _ _ _ _).2 hp) ((blindDesc_iff _ _ _ _).2 hm) hne,
      h.2 _ _ _ _ _ ((blindDesc_iff _ _ _ _).2 hp) ((blindDesc_iff _ _ _ _).2 hm) hne⟩

/-! ## thm:apollonian — `descartes_reflect` vs `blind_75` -/

def blind75_stmt : Prop :=
  ∀ (k₁ k₂ k₃ k₄ : ℝ), BlindDescartesCurvatures ![k₁, k₂, k₃, k₄] →
    BlindDescartesCurvatures ![k₁, k₂, k₃, 2 * (k₁ + k₂ + k₃) - k₄]

theorem reflect_R_to_B : type_of% @Inversion.descartes_reflect → blind75_stmt :=
  fun h _ _ _ _ hk ↦ (blindDesc_iff _ _ _ _).2 (h ((blindDesc_iff _ _ _ _).1 hk))

theorem reflect_B_to_R : blind75_stmt → type_of% @Inversion.descartes_reflect :=
  fun h _ _ _ _ hk ↦ (blindDesc_iff _ _ _ _).1 (h _ _ _ _ ((blindDesc_iff _ _ _ _).2 hk))

/-! ## thm:apollonian — `apollonian_integral` vs `blind_76` / `blind_77` (B→R only) -/

def blind76_stmt : Prop :=
  ∀ (k : Fin 4 → ℝ) (moves : List (Fin 4)), BlindDescartesCurvatures k →
    (∀ i, ∃ z : ℤ, k i = (z : ℝ)) →
    BlindDescartesCurvatures
      (moves.foldl (fun current i => BlindApollonianMove current i) k)

theorem move3 (k₁ k₂ k₃ k₄ : ℝ) :
    BlindApollonianMove ![k₁, k₂, k₃, k₄] 3 = ![k₁, k₂, k₃, 2 * (k₁ + k₂ + k₃) - k₄] := by
  funext j
  fin_cases j <;> simp [BlindApollonianMove, Finset.sum_erase_eq_sub, Fin.sum_univ_four]

theorem integral_B_to_R : blind76_stmt → type_of% @Inversion.apollonian_integral := by
  intro h k₁ k₂ k₃ k₄ hk
  refine ⟨?_, by push_cast; ring⟩
  have hR : Inversion.descartesForm k₁ k₂ k₃ k₄ = 0 := by
    have := congrArg (fun z : ℤ ↦ (z : ℝ)) hk
    simp only [Inversion.descartesFormZ, Int.cast_zero] at this
    push_cast at this
    simpa only [Inversion.descartesForm] using this
  have hb := h ![(k₁ : ℝ), k₂, k₃, k₄] [3] ((blindDesc_iff _ _ _ _).2 hR)
    (fun i ↦ by fin_cases i <;> simp)
  simp only [List.foldl_cons, List.foldl_nil, move3] at hb
  have hr := (blindDesc_iff _ _ _ _).1 hb
  have : ((Inversion.descartesFormZ k₁ k₂ k₃ (2 * (k₁ + k₂ + k₃) - k₄) : ℤ) : ℝ) = 0 := by
    simp only [Inversion.descartesFormZ]
    push_cast
    simpa only [Inversion.descartesForm] using hr
  exact_mod_cast this

end L13CmpInv
