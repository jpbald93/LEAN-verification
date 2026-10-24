import Clifford

open Affine EuclideanGeometry

noncomputable section

/-! Blind definitions, copied verbatim from `~/reformal/PaperDBlind.lean`. -/

def BlindP (ci cj : ℂ) : ℂ :=
  ((starRingEnd ℂ) ci * cj - ci * (starRingEnd ℂ) cj) / ((starRingEnd ℂ) ci - (starRingEnd ℂ) cj)

def BlindOnCircum (a b c z : ℂ) : Prop :=
  ∃ o : ℂ, dist o a = dist o b ∧ dist o b = dist o c ∧ dist o z = dist o a

def BlindOnGamma {n : ℕ} (c : Fin n → ℂ) (i j k : Fin n) (z : ℂ) : Prop :=
  BlindOnCircum (BlindP (c i) (c j)) (BlindP (c i) (c k)) (BlindP (c j) (c k)) z

def BlindCliffordHyp {n : ℕ} (c : Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, i < j → BlindP (c i) (c j) ≠ 0) ∧
  (∀ i j k : Fin n, i < j → j < k →
    ¬ Collinear ℝ ({BlindP (c i) (c j), BlindP (c i) (c k), BlindP (c j) (c k)} : Set ℂ))

def BlindIsCp {n : ℕ} (c : Fin n → ℂ) (T : Finset (Fin n)) (z : ℂ) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T, i < j → j < k → BlindOnGamma c i j k z

inductive BlindGenCircle
  | circle (o : ℂ) (r : ℝ) (hr : 0 ≤ r)
  | line (p v : ℂ) (hv : v ≠ 0)

def BlindGenCircle.carrier : BlindGenCircle → Set ℂ
  | .circle o r _ => Metric.sphere o r
  | .line p v _ => {z | ∃ t : ℝ, z = p + t * v}

def BlindOnGenCircle (S : Set ℂ) : Prop := ∃ g : BlindGenCircle, S ⊆ g.carrier

/-! Bridge lemmas (proved here from definitions + Mathlib; the only repository facts used are
`Clifford.mem_circumcircle_left/middle/right`, which state that `circumcircle A B C` passes
through `A, B, C`). -/

/-- `BlindP` is literally the repo's `secondInter`. -/
lemma blindP_eq (a b : ℂ) : BlindP a b = Clifford.secondInter a b := rfl

lemma eq_ccenter {A B C o : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (h1 : dist o A = dist o B) (h2 : dist o B = dist o C) : o = Clifford.ccenter A B C := by
  let t : Affine.Triangle ℝ ℂ := ⟨![A, B, C], affineIndependent_iff_not_collinear_set.mpr h⟩
  have hspan : affineSpan ℝ (Set.range t.points) = ⊤ := by
    rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp
  have hmem : ∀ p : ℂ, p ∈ affineSpan ℝ (Set.range t.points) := fun p => by
    rw [hspan]; exact AffineSubspace.mem_top _ _ _
  have hB := EuclideanGeometry.mem_sphere.1 (Clifford.mem_circumcircle_middle h)
  have hC := EuclideanGeometry.mem_sphere.1 (Clifford.mem_circumcircle_right h)
  simp only [Clifford.circumcircle] at hB hC
  have e1 : o = t.circumcenter := by
    apply t.eq_circumcenter_of_dist_eq (hmem o) (r := dist o A)
    intro i; fin_cases i
    · simp [t, dist_comm]
    · simp [t]; rw [dist_comm, ← h1, dist_comm]
    · simp [t]; rw [dist_comm, ← h2, ← h1, dist_comm]
  have e2 : Clifford.ccenter A B C = t.circumcenter := by
    apply t.eq_circumcenter_of_dist_eq (hmem _) (r := dist A (Clifford.ccenter A B C))
    intro i; fin_cases i
    · simp [t]
    · simpa [t] using hB
    · simpa [t] using hC
  rw [e1, e2]

/-- `BlindOnCircum` is membership in the repo's `circumcircle` (for non-collinear triples). -/
lemma onCircum_iff {A B C z : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) :
    BlindOnCircum A B C z ↔ z ∈ Clifford.circumcircle A B C := by
  have hB := EuclideanGeometry.mem_sphere.1 (Clifford.mem_circumcircle_middle h)
  have hC := EuclideanGeometry.mem_sphere.1 (Clifford.mem_circumcircle_right h)
  simp only [Clifford.circumcircle] at hB hC
  rw [EuclideanGeometry.mem_sphere]
  simp only [Clifford.circumcircle]
  constructor
  · rintro ⟨o, h1, h2, h3⟩
    have := eq_ccenter h h1 h2
    subst this
    rw [dist_comm, h3, dist_comm]
  · intro hz
    refine ⟨Clifford.ccenter A B C, ?_, ?_, ?_⟩
    · rw [dist_comm, ← hB, dist_comm]
    · rw [dist_comm, hB, ← hC, dist_comm]
    · rw [dist_comm, hz, dist_comm]

/-- On a nonempty set, "on one generalized circle" is "cospherical or collinear". -/
lemma onGen_iff {S : Set ℂ} (hS : S.Nonempty) :
    BlindOnGenCircle S ↔ Cospherical S ∨ Collinear ℝ S := by
  constructor
  · rintro ⟨g, hg⟩
    cases g with
    | circle o r hr =>
      left; exact ⟨o, r, fun p hp => by simpa [BlindGenCircle.carrier, dist_eq_norm] using hg hp⟩
    | line p v hv =>
      right
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨p, v, fun q hq => ?_⟩
      obtain ⟨t, ht⟩ := hg hq
      exact ⟨t, by rw [ht, vadd_eq_add, Complex.real_smul, add_comm]⟩
  · rintro (⟨o, r, h⟩ | h)
    · obtain ⟨x, hx⟩ := hS
      have hr : 0 ≤ r := by rw [← h x hx]; exact dist_nonneg
      exact ⟨.circle o r hr, fun q hq => by simpa [BlindGenCircle.carrier, dist_eq_norm] using h q hq⟩
    · rw [collinear_iff_exists_forall_eq_smul_vadd] at h
      obtain ⟨p, v, hv⟩ := h
      by_cases h0 : v = 0
      · refine ⟨.circle p 0 le_rfl, fun q hq => ?_⟩
        obtain ⟨t, ht⟩ := hv q hq
        simp [BlindGenCircle.carrier, ht, h0]
      · refine ⟨.line p v h0, fun q hq => ?_⟩
        obtain ⟨t, ht⟩ := hv q hq
        exact ⟨t, by rw [ht, vadd_eq_add, Complex.real_smul, add_comm]⟩

lemma gamma_iff {n : ℕ} (c : Fin n → ℂ) (h : BlindCliffordHyp c) {i j k : Fin n} (hij : i < j)
    (hjk : j < k) (z : ℂ) : BlindOnGamma c i j k z ↔ z ∈ Clifford.gam (c i) (c j) (c k) :=
  onCircum_iff (h.2 i j k hij hjk)

/-- blind_1 verbatim -/
def blind1_stmt : Prop :=
  ∀ (c : Fin 4 → ℂ) (h : BlindCliffordHyp c), ∃ z : ℂ, BlindIsCp c Finset.univ z

theorem rb_1 : (type_of% @Clifford.clifford_one) → blind1_stmt := by
  intro h c hc
  obtain ⟨P, p1, p2, p3, p4⟩ := h (c 0) (c 1) (c 2) (c 3)
    (hc.1 0 1 (by decide)) (hc.1 0 2 (by decide)) (hc.1 0 3 (by decide))
    (hc.1 1 2 (by decide)) (hc.1 1 3 (by decide)) (hc.1 2 3 (by decide))
    (hc.2 0 1 2 (by decide) (by decide)) (hc.2 0 1 3 (by decide) (by decide))
    (hc.2 0 2 3 (by decide) (by decide)) (hc.2 1 2 3 (by decide) (by decide))
  refine ⟨P, ?_⟩
  intro i _ j _ k _ hij hjk
  rw [gamma_iff c hc hij hjk]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | (exfalso; revert hij hjk; decide) | exact p1 | exact p2 | exact p3 | exact p4

theorem br_1 : blind1_stmt → (type_of% @Clifford.clifford_one) := by
  intro h c₁ c₂ c₃ c₄ h12 h13 h14 h23 h24 h34 n123 n124 n134 n234
  let c : Fin 4 → ℂ := ![c₁, c₂, c₃, c₄]
  have hc : BlindCliffordHyp c := by
    refine ⟨fun i j hij => ?_, fun i j k hij hjk => ?_⟩
    · fin_cases i <;> fin_cases j <;>
        first | (exfalso; revert hij; decide) | assumption
    · fin_cases i <;> fin_cases j <;> fin_cases k <;>
        first | (exfalso; revert hij hjk; decide) | assumption
  obtain ⟨z, hz⟩ := h c hc
  have g : ∀ i j k : Fin 4, i < j → j < k → z ∈ Clifford.gam (c i) (c j) (c k) :=
    fun i j k hij hjk => (gamma_iff c hc hij hjk z).1
      (hz i (Finset.mem_univ _) j (Finset.mem_univ _) k (Finset.mem_univ _) hij hjk)
  exact ⟨z, g 0 1 2 (by decide) (by decide), g 0 1 3 (by decide) (by decide),
    g 0 2 3 (by decide) (by decide), g 1 2 3 (by decide) (by decide)⟩
