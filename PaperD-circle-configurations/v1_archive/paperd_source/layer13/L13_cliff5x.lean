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

lemma range5 (P : Fin 5 → ℂ) : Set.range P = {P 0, P 1, P 2, P 3, P 4} := by
  ext z; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (h | h | h | h | h) <;> exact ⟨_, h.symm⟩

lemma hyp5 {c₁ c₂ c₃ c₄ c₅ : ℂ}
    (h12 : Clifford.secondInter c₁ c₂ ≠ 0) (h13 : Clifford.secondInter c₁ c₃ ≠ 0) (h14 : Clifford.secondInter c₁ c₄ ≠ 0)
    (h15 : Clifford.secondInter c₁ c₅ ≠ 0) (h23 : Clifford.secondInter c₂ c₃ ≠ 0) (h24 : Clifford.secondInter c₂ c₄ ≠ 0)
    (h25 : Clifford.secondInter c₂ c₅ ≠ 0) (h34 : Clifford.secondInter c₃ c₄ ≠ 0) (h35 : Clifford.secondInter c₃ c₅ ≠ 0)
    (h45 : Clifford.secondInter c₄ c₅ ≠ 0)
    (n123 : ¬ Collinear ℝ ({Clifford.secondInter c₁ c₂, Clifford.secondInter c₁ c₃, Clifford.secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({Clifford.secondInter c₁ c₂, Clifford.secondInter c₁ c₄, Clifford.secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({Clifford.secondInter c₁ c₂, Clifford.secondInter c₁ c₅, Clifford.secondInter c₂ c₅} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({Clifford.secondInter c₁ c₃, Clifford.secondInter c₁ c₄, Clifford.secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({Clifford.secondInter c₁ c₃, Clifford.secondInter c₁ c₅, Clifford.secondInter c₃ c₅} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({Clifford.secondInter c₁ c₄, Clifford.secondInter c₁ c₅, Clifford.secondInter c₄ c₅} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({Clifford.secondInter c₂ c₃, Clifford.secondInter c₂ c₄, Clifford.secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({Clifford.secondInter c₂ c₃, Clifford.secondInter c₂ c₅, Clifford.secondInter c₃ c₅} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({Clifford.secondInter c₂ c₄, Clifford.secondInter c₂ c₅, Clifford.secondInter c₄ c₅} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({Clifford.secondInter c₃ c₄, Clifford.secondInter c₃ c₅, Clifford.secondInter c₄ c₅} : Set ℂ)) :
    BlindCliffordHyp ![c₁, c₂, c₃, c₄, c₅] := by
  refine ⟨fun i j hij => ?_, fun i j k hij hjk => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hij; decide) | assumption
  · fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first | (exfalso; revert hij hjk; decide) | assumption

/-- blind_3 verbatim -/
def blind3_stmt : Prop :=
  ∀ (c : Fin 5 → ℂ) (h : BlindCliffordHyp c)
    (P : Fin 5 → ℂ) (hP : ∀ k, BlindIsCp c (Finset.univ.erase k) (P k)),
    BlindOnGenCircle (Set.range P)

open Clifford in
/-- NOT a repo theorem: the (unproved here) uniqueness of the common point of the four `Γ`.
This is exactly what separates blind_3 from `clifford_two_explicit` in the R→B direction. -/
def uniq_stmt : Prop :=
  ∀ (c₁ c₂ c₃ c₄ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (z : ℂ), z ∈ gam c₁ c₂ c₃ → z ∈ gam c₁ c₂ c₄ → z ∈ gam c₁ c₃ c₄ → z ∈ gam c₂ c₃ c₄ →
      z = cliffordPoint c₁ c₂ c₃ c₄

/-- R→B, conditional on the uniqueness statement `uniq_stmt` (taken as a premise). -/
theorem rb_3_given_uniq :
    (type_of% @Clifford.clifford_two_explicit) → uniq_stmt → blind3_stmt := by
  intro h hu c hc P hP
  have H := hc.1; have N := hc.2
  have g : ∀ m i j k : Fin 5, i ≠ m → j ≠ m → k ≠ m → i < j → j < k →
      P m ∈ Clifford.gam (c i) (c j) (c k) :=
    fun m i j k hi hj hk hij hjk => (gamma_iff _ hc hij hjk _).1
      (hP m i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩) j
        (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩) k
        (Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩) hij hjk)
  have e0 := hu (c 1) (c 2) (c 3) (c 4) (H 1 2 (by decide)) (H 1 3 (by decide))
    (H 1 4 (by decide)) (H 2 3 (by decide)) (H 2 4 (by decide)) (H 3 4 (by decide))
    (N 1 2 3 (by decide) (by decide)) (N 1 2 4 (by decide) (by decide))
    (N 1 3 4 (by decide) (by decide)) (N 2 3 4 (by decide) (by decide)) (P 0)
    (g 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
  have e1 := hu (c 0) (c 2) (c 3) (c 4) (H 0 2 (by decide)) (H 0 3 (by decide))
    (H 0 4 (by decide)) (H 2 3 (by decide)) (H 2 4 (by decide)) (H 3 4 (by decide))
    (N 0 2 3 (by decide) (by decide)) (N 0 2 4 (by decide) (by decide))
    (N 0 3 4 (by decide) (by decide)) (N 2 3 4 (by decide) (by decide)) (P 1)
    (g 1 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 1 0 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 1 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
  have e2 := hu (c 0) (c 1) (c 3) (c 4) (H 0 1 (by decide)) (H 0 3 (by decide))
    (H 0 4 (by decide)) (H 1 3 (by decide)) (H 1 4 (by decide)) (H 3 4 (by decide))
    (N 0 1 3 (by decide) (by decide)) (N 0 1 4 (by decide) (by decide))
    (N 0 3 4 (by decide) (by decide)) (N 1 3 4 (by decide) (by decide)) (P 2)
    (g 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 2 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 2 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 2 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
  have e3 := hu (c 0) (c 1) (c 2) (c 4) (H 0 1 (by decide)) (H 0 2 (by decide))
    (H 0 4 (by decide)) (H 1 2 (by decide)) (H 1 4 (by decide)) (H 2 4 (by decide))
    (N 0 1 2 (by decide) (by decide)) (N 0 1 4 (by decide) (by decide))
    (N 0 2 4 (by decide) (by decide)) (N 1 2 4 (by decide) (by decide)) (P 3)
    (g 3 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 3 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 3 0 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 3 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
  have e4 := hu (c 0) (c 1) (c 2) (c 3) (H 0 1 (by decide)) (H 0 2 (by decide))
    (H 0 3 (by decide)) (H 1 2 (by decide)) (H 1 3 (by decide)) (H 2 3 (by decide))
    (N 0 1 2 (by decide) (by decide)) (N 0 1 3 (by decide) (by decide))
    (N 0 2 3 (by decide) (by decide)) (N 1 2 3 (by decide) (by decide)) (P 4)
    (g 4 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 4 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 4 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (g 4 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [onGen_iff ⟨_, Set.mem_range_self 0⟩, range5, e0, e1, e2, e3, e4]
  exact h (c 0) (c 1) (c 2) (c 3) (c 4)
    (H 0 1 (by decide)) (H 0 2 (by decide)) (H 0 3 (by decide)) (H 0 4 (by decide))
    (H 1 2 (by decide)) (H 1 3 (by decide)) (H 1 4 (by decide)) (H 2 3 (by decide))
    (H 2 4 (by decide)) (H 3 4 (by decide))
    (N 0 1 2 (by decide) (by decide)) (N 0 1 3 (by decide) (by decide))
    (N 0 1 4 (by decide) (by decide)) (N 0 2 3 (by decide) (by decide))
    (N 0 2 4 (by decide) (by decide)) (N 0 3 4 (by decide) (by decide))
    (N 1 2 3 (by decide) (by decide)) (N 1 2 4 (by decide) (by decide))
    (N 1 3 4 (by decide) (by decide)) (N 2 3 4 (by decide) (by decide))

set_option maxHeartbeats 4000000 in
/-- B→R, conditional on the *statement* of `Clifford.cliffordPoint_mem_gams` taken as a
premise (the repo theorem itself is not used): one needs to know that the explicit
`cliffordPoint` is a common point before the blind statement can be instantiated with it. -/
theorem br_3_given_cp :
    blind3_stmt → (type_of% @Clifford.cliffordPoint_mem_gams) →
      (type_of% @Clifford.clifford_two_explicit) := by
  intro h hcp c₁ c₂ c₃ c₄ c₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    n123 n124 n125 n134 n135 n145 n234 n235 n245 n345
  have hc := hyp5 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    n123 n124 n125 n134 n135 n145 n234 n235 n245 n345
  obtain ⟨a1, a2, a3, a4⟩ := hcp _ _ _ _ h23 h24 h25 h34 h35 h45 n234 n235 n245 n345
  obtain ⟨b1, b2, b3, b4⟩ := hcp _ _ _ _ h13 h14 h15 h34 h35 h45 n134 n135 n145 n345
  obtain ⟨d1, d2, d3, d4⟩ := hcp _ _ _ _ h12 h14 h15 h24 h25 h45 n124 n125 n145 n245
  obtain ⟨e1, e2, e3, e4⟩ := hcp _ _ _ _ h12 h13 h15 h23 h25 h35 n123 n125 n135 n235
  obtain ⟨f1, f2, f3, f4⟩ := hcp _ _ _ _ h12 h13 h14 h23 h24 h34 n123 n124 n134 n234
  have := h _ hc ![Clifford.cliffordPoint c₂ c₃ c₄ c₅, Clifford.cliffordPoint c₁ c₃ c₄ c₅,
      Clifford.cliffordPoint c₁ c₂ c₄ c₅, Clifford.cliffordPoint c₁ c₂ c₃ c₅,
      Clifford.cliffordPoint c₁ c₂ c₃ c₄] (by
    intro m i hi j hj k hk hij hjk
    rw [gamma_iff _ hc hij hjk]
    fin_cases m <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first | (exfalso; revert hi hj hk hij hjk; decide) | assumption)
  rw [onGen_iff ⟨_, Set.mem_range_self 0⟩, range5] at this
  exact this
