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

/-- verbatim from the blind file -/
def BlindDesignated (S : Finset (Fin 6)) : Finset (Finset (Fin 6)) :=
  (S.sort (· ≤ ·)).reverse.take 3 |>.toFinset.image (fun x => S.erase x)

/-- blind_4 verbatim -/
def blind4_stmt : Prop :=
  ∀ (c : Fin 6 → ℂ) (h : BlindCliffordHyp c)
    (P : Finset (Fin 6) → ℂ) (hP : ∀ T : Finset (Fin 6), T.card = 4 → BlindIsCp c T (P T))
    (a b d : Finset (Fin 6) → Finset (Fin 6))
    (hdes : ∀ S : Finset (Fin 6), S.card = 5 → BlindDesignated S = {a S, b S, d S})
    (hnc : ∀ S : Finset (Fin 6), S.card = 5 →
      ¬ Collinear ℝ ({P (a S), P (b S), P (d S)} : Set ℂ)),
    (∀ S : Finset (Fin 6), S.card = 5 → ∀ T ⊆ S, T.card = 4 →
        BlindOnCircum (P (a S)) (P (b S)) (P (d S)) (P T)) ∧
      ∃ z : ℂ, ∀ S : Finset (Fin 6), S.card = 5 →
        BlindOnCircum (P (a S)) (P (b S)) (P (d S)) z

open Clifford in
/-- NOT a repo theorem: uniqueness of the common point of the four `Γ` (as in L13_cliff5x). -/
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

lemma onCircum_set (x y z w : ℂ) :
    BlindOnCircum x y z w ↔ ∃ o : ℂ, ∀ p ∈ ({x, y, z} : Set ℂ), dist o p = dist o w := by
  constructor
  · rintro ⟨o, h1, h2, h3⟩
    refine ⟨o, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact h3.symm
    · rw [← h1]; exact h3.symm
    · rw [← h2, ← h1]; exact h3.symm
  · rintro ⟨o, h⟩
    refine ⟨o, ?_, ?_, ?_⟩
    · rw [h x (by simp), h y (by simp)]
    · rw [h y (by simp), h z (by simp)]
    · rw [h x (by simp)]

lemma circ_congr {x y z x' y' z' : ℂ} (w : ℂ) (h : ({x, y, z} : Set ℂ) = {x', y', z'}) :
    BlindOnCircum x y z w ↔ BlindOnCircum x' y' z' w := by
  rw [onCircum_set, onCircum_set, h]

lemma s4 (a b c d : Fin 6) (h : a < b ∧ b < c ∧ c < d) :
    ({a, b, c, d} : Finset (Fin 6)).sort (· ≤ ·) = [a, b, c, d] := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [Finset.sort_insert (s := {b, c, d}) _ (by simp; omega) (by simp; omega),
    Finset.sort_insert (s := {c, d}) _ (by simp; omega) (by simp; omega),
    Finset.sort_insert (s := {d}) _ (by simp; omega) (by simp; omega), Finset.sort_singleton]

lemma s5 (a b c d e : Fin 6) (h : a < b ∧ b < c ∧ c < d ∧ d < e) :
    ({a, b, c, d, e} : Finset (Fin 6)).sort (· ≤ ·) = [a, b, c, d, e] := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Finset.sort_insert (s := {b, c, d, e}) _ (by simp; omega) (by simp; omega),
    Finset.sort_insert (s := {c, d, e}) _ (by simp; omega) (by simp; omega),
    Finset.sort_insert (s := {d, e}) _ (by simp; omega) (by simp; omega),
    Finset.sort_insert (s := {e}) _ (by simp; omega) (by simp; omega), Finset.sort_singleton]

lemma T15 : ∀ T : Finset (Fin 6), T.card = 4 → T = {0,1,2,3} ∨ T = {0,1,2,4} ∨ T = {0,1,2,5} ∨ T = {0,1,3,4} ∨ T = {0,1,3,5} ∨ T = {0,1,4,5} ∨ T = {0,2,3,4} ∨ T = {0,2,3,5} ∨ T = {0,2,4,5} ∨ T = {0,3,4,5} ∨ T = {1,2,3,4} ∨ T = {1,2,3,5} ∨ T = {1,2,4,5} ∨ T = {1,3,4,5} ∨ T = {2,3,4,5} := by decide

lemma S6 : ∀ S : Finset (Fin 6), S.card = 5 → S = {0,1,2,3,4} ∨ S = {0,1,2,3,5} ∨ S = {0,1,2,4,5} ∨ S = {0,1,3,4,5} ∨ S = {0,2,3,4,5} ∨ S = {1,2,3,4,5} := by decide

lemma des0 : BlindDesignated ({0,1,2,3,4} : Finset (Fin 6)) = {({0,1,2,3} : Finset (Fin 6)), ({0,1,2,4} : Finset (Fin 6)), ({0,1,3,4} : Finset (Fin 6))} := by
  rw [BlindDesignated, s5 0 1 2 3 4 (by decide)]; decide

lemma des1 : BlindDesignated ({0,1,2,3,5} : Finset (Fin 6)) = {({0,1,2,3} : Finset (Fin 6)), ({0,1,2,5} : Finset (Fin 6)), ({0,1,3,5} : Finset (Fin 6))} := by
  rw [BlindDesignated, s5 0 1 2 3 5 (by decide)]; decide

lemma des2 : BlindDesignated ({0,1,2,4,5} : Finset (Fin 6)) = {({0,1,2,4} : Finset (Fin 6)), ({0,1,2,5} : Finset (Fin 6)), ({0,1,4,5} : Finset (Fin 6))} := by
  rw [BlindDesignated, s5 0 1 2 4 5 (by decide)]; decide

lemma des3 : BlindDesignated ({0,1,3,4,5} : Finset (Fin 6)) = {({0,1,3,4} : Finset (Fin 6)), ({0,1,3,5} : Finset (Fin 6)), ({0,1,4,5} : Finset (Fin 6))} := by
  rw [BlindDesignated, s5 0 1 3 4 5 (by decide)]; decide

lemma des4 : BlindDesignated ({0,2,3,4,5} : Finset (Fin 6)) = {({0,2,3,4} : Finset (Fin 6)), ({0,2,3,5} : Finset (Fin 6)), ({0,2,4,5} : Finset (Fin 6))} := by
  rw [BlindDesignated, s5 0 2 3 4 5 (by decide)]; decide

lemma des5 : BlindDesignated ({1,2,3,4,5} : Finset (Fin 6)) = {({1,2,3,4} : Finset (Fin 6)), ({1,2,3,5} : Finset (Fin 6)), ({1,2,4,5} : Finset (Fin 6))} := by
  rw [BlindDesignated, s5 1 2 3 4 5 (by decide)]; decide

set_option maxHeartbeats 8000000 in
/-- R→B, conditional on `uniq_stmt` (not a repo theorem; genuine geometry). -/
theorem rb_4_given_uniq : (type_of% @Clifford.clifford_three) → uniq_stmt → blind4_stmt := by
  intro h hu c hc P hP a b d hdes hnc
  have H := hc.1; have N := hc.2
  have g : ∀ T : Finset (Fin 6), T.card = 4 → ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T, i < j → j < k →
      P T ∈ Clifford.gam (c i) (c j) (c k) :=
    fun T hT i hi j hj k hk hij hjk => (gamma_iff c hc hij hjk _).1 (hP T hT i hi j hj k hk hij hjk)
  have e0 : P ({0,1,2,3} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 3) :=
    hu _ _ _ _ (H 0 1 (by decide)) (H 0 2 (by decide)) (H 0 3 (by decide)) (H 1 2 (by decide)) (H 1 3 (by decide)) (H 2 3 (by decide)) (N 0 1 2 (by decide) (by decide)) (N 0 1 3 (by decide) (by decide)) (N 0 2 3 (by decide) (by decide)) (N 1 2 3 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 1 (by decide) 2 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 1 (by decide) 3 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 2 (by decide) 3 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 2 (by decide) 3 (by decide) (by decide) (by decide))
  have e1 : P ({0,1,2,4} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 4) :=
    hu _ _ _ _ (H 0 1 (by decide)) (H 0 2 (by decide)) (H 0 4 (by decide)) (H 1 2 (by decide)) (H 1 4 (by decide)) (H 2 4 (by decide)) (N 0 1 2 (by decide) (by decide)) (N 0 1 4 (by decide) (by decide)) (N 0 2 4 (by decide) (by decide)) (N 1 2 4 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 1 (by decide) 2 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 1 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 2 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 2 (by decide) 4 (by decide) (by decide) (by decide))
  have e2 : P ({0,1,2,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 5) :=
    hu _ _ _ _ (H 0 1 (by decide)) (H 0 2 (by decide)) (H 0 5 (by decide)) (H 1 2 (by decide)) (H 1 5 (by decide)) (H 2 5 (by decide)) (N 0 1 2 (by decide) (by decide)) (N 0 1 5 (by decide) (by decide)) (N 0 2 5 (by decide) (by decide)) (N 1 2 5 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 1 (by decide) 2 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 1 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 2 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 2 (by decide) 5 (by decide) (by decide) (by decide))
  have e3 : P ({0,1,3,4} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 4) :=
    hu _ _ _ _ (H 0 1 (by decide)) (H 0 3 (by decide)) (H 0 4 (by decide)) (H 1 3 (by decide)) (H 1 4 (by decide)) (H 3 4 (by decide)) (N 0 1 3 (by decide) (by decide)) (N 0 1 4 (by decide) (by decide)) (N 0 3 4 (by decide) (by decide)) (N 1 3 4 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 1 (by decide) 3 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 1 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 3 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 3 (by decide) 4 (by decide) (by decide) (by decide))
  have e4 : P ({0,1,3,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 5) :=
    hu _ _ _ _ (H 0 1 (by decide)) (H 0 3 (by decide)) (H 0 5 (by decide)) (H 1 3 (by decide)) (H 1 5 (by decide)) (H 3 5 (by decide)) (N 0 1 3 (by decide) (by decide)) (N 0 1 5 (by decide) (by decide)) (N 0 3 5 (by decide) (by decide)) (N 1 3 5 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 1 (by decide) 3 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 1 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 3 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 3 (by decide) 5 (by decide) (by decide) (by decide))
  have e5 : P ({0,1,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 4) (c 5) :=
    hu _ _ _ _ (H 0 1 (by decide)) (H 0 4 (by decide)) (H 0 5 (by decide)) (H 1 4 (by decide)) (H 1 5 (by decide)) (H 4 5 (by decide)) (N 0 1 4 (by decide) (by decide)) (N 0 1 5 (by decide) (by decide)) (N 0 4 5 (by decide) (by decide)) (N 1 4 5 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 1 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 1 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide))
  have e6 : P ({0,2,3,4} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 2) (c 3) (c 4) :=
    hu _ _ _ _ (H 0 2 (by decide)) (H 0 3 (by decide)) (H 0 4 (by decide)) (H 2 3 (by decide)) (H 2 4 (by decide)) (H 3 4 (by decide)) (N 0 2 3 (by decide) (by decide)) (N 0 2 4 (by decide) (by decide)) (N 0 3 4 (by decide) (by decide)) (N 2 3 4 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 2 (by decide) 3 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 2 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 3 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 2 (by decide) 3 (by decide) 4 (by decide) (by decide) (by decide))
  have e7 : P ({0,2,3,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 2) (c 3) (c 5) :=
    hu _ _ _ _ (H 0 2 (by decide)) (H 0 3 (by decide)) (H 0 5 (by decide)) (H 2 3 (by decide)) (H 2 5 (by decide)) (H 3 5 (by decide)) (N 0 2 3 (by decide) (by decide)) (N 0 2 5 (by decide) (by decide)) (N 0 3 5 (by decide) (by decide)) (N 2 3 5 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 2 (by decide) 3 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 2 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 3 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 2 (by decide) 3 (by decide) 5 (by decide) (by decide) (by decide))
  have e8 : P ({0,2,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 2) (c 4) (c 5) :=
    hu _ _ _ _ (H 0 2 (by decide)) (H 0 4 (by decide)) (H 0 5 (by decide)) (H 2 4 (by decide)) (H 2 5 (by decide)) (H 4 5 (by decide)) (N 0 2 4 (by decide) (by decide)) (N 0 2 5 (by decide) (by decide)) (N 0 4 5 (by decide) (by decide)) (N 2 4 5 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 2 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 2 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 2 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide))
  have e9 : P ({0,3,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 3) (c 4) (c 5) :=
    hu _ _ _ _ (H 0 3 (by decide)) (H 0 4 (by decide)) (H 0 5 (by decide)) (H 3 4 (by decide)) (H 3 5 (by decide)) (H 4 5 (by decide)) (N 0 3 4 (by decide) (by decide)) (N 0 3 5 (by decide) (by decide)) (N 0 4 5 (by decide) (by decide)) (N 3 4 5 (by decide) (by decide)) _ (g _ (by decide) 0 (by decide) 3 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 3 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 0 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 3 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide))
  have e10 : P ({1,2,3,4} : Finset (Fin 6)) = Clifford.cliffordPoint (c 1) (c 2) (c 3) (c 4) :=
    hu _ _ _ _ (H 1 2 (by decide)) (H 1 3 (by decide)) (H 1 4 (by decide)) (H 2 3 (by decide)) (H 2 4 (by decide)) (H 3 4 (by decide)) (N 1 2 3 (by decide) (by decide)) (N 1 2 4 (by decide) (by decide)) (N 1 3 4 (by decide) (by decide)) (N 2 3 4 (by decide) (by decide)) _ (g _ (by decide) 1 (by decide) 2 (by decide) 3 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 2 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 3 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 2 (by decide) 3 (by decide) 4 (by decide) (by decide) (by decide))
  have e11 : P ({1,2,3,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 1) (c 2) (c 3) (c 5) :=
    hu _ _ _ _ (H 1 2 (by decide)) (H 1 3 (by decide)) (H 1 5 (by decide)) (H 2 3 (by decide)) (H 2 5 (by decide)) (H 3 5 (by decide)) (N 1 2 3 (by decide) (by decide)) (N 1 2 5 (by decide) (by decide)) (N 1 3 5 (by decide) (by decide)) (N 2 3 5 (by decide) (by decide)) _ (g _ (by decide) 1 (by decide) 2 (by decide) 3 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 2 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 3 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 2 (by decide) 3 (by decide) 5 (by decide) (by decide) (by decide))
  have e12 : P ({1,2,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 1) (c 2) (c 4) (c 5) :=
    hu _ _ _ _ (H 1 2 (by decide)) (H 1 4 (by decide)) (H 1 5 (by decide)) (H 2 4 (by decide)) (H 2 5 (by decide)) (H 4 5 (by decide)) (N 1 2 4 (by decide) (by decide)) (N 1 2 5 (by decide) (by decide)) (N 1 4 5 (by decide) (by decide)) (N 2 4 5 (by decide) (by decide)) _ (g _ (by decide) 1 (by decide) 2 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 2 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 2 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide))
  have e13 : P ({1,3,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 1) (c 3) (c 4) (c 5) :=
    hu _ _ _ _ (H 1 3 (by decide)) (H 1 4 (by decide)) (H 1 5 (by decide)) (H 3 4 (by decide)) (H 3 5 (by decide)) (H 4 5 (by decide)) (N 1 3 4 (by decide) (by decide)) (N 1 3 5 (by decide) (by decide)) (N 1 4 5 (by decide) (by decide)) (N 3 4 5 (by decide) (by decide)) _ (g _ (by decide) 1 (by decide) 3 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 3 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 1 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 3 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide))
  have e14 : P ({2,3,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 2) (c 3) (c 4) (c 5) :=
    hu _ _ _ _ (H 2 3 (by decide)) (H 2 4 (by decide)) (H 2 5 (by decide)) (H 3 4 (by decide)) (H 3 5 (by decide)) (H 4 5 (by decide)) (N 2 3 4 (by decide) (by decide)) (N 2 3 5 (by decide) (by decide)) (N 2 4 5 (by decide) (by decide)) (N 3 4 5 (by decide) (by decide)) _ (g _ (by decide) 2 (by decide) 3 (by decide) 4 (by decide) (by decide) (by decide)) (g _ (by decide) 2 (by decide) 3 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 2 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide)) (g _ (by decide) 3 (by decide) 4 (by decide) 5 (by decide) (by decide) (by decide))
  have sS0 : ({P (a ({0,1,2,3,4} : Finset (Fin 6))), P (b ({0,1,2,3,4} : Finset (Fin 6))), P (d ({0,1,2,3,4} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 3), Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 4), Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 4)} := by
    have e := (hdes ({0,1,2,3,4} : Finset (Fin 6)) (by decide)).symm.trans des0
    have := congrArg (fun F : Finset (Finset (Fin 6)) => P '' (F : Set (Finset (Fin 6)))) e
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton] at this
    rw [this, e0, e1, e3]
  have m6 := hnc ({0,1,2,3,4} : Finset (Fin 6)) (by decide)
  rw [sS0] at m6
  have sS1 : ({P (a ({0,1,2,3,5} : Finset (Fin 6))), P (b ({0,1,2,3,5} : Finset (Fin 6))), P (d ({0,1,2,3,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 3), Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 5), Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 5)} := by
    have e := (hdes ({0,1,2,3,5} : Finset (Fin 6)) (by decide)).symm.trans des1
    have := congrArg (fun F : Finset (Finset (Fin 6)) => P '' (F : Set (Finset (Fin 6)))) e
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton] at this
    rw [this, e0, e2, e4]
  have m5 := hnc ({0,1,2,3,5} : Finset (Fin 6)) (by decide)
  rw [sS1] at m5
  have sS2 : ({P (a ({0,1,2,4,5} : Finset (Fin 6))), P (b ({0,1,2,4,5} : Finset (Fin 6))), P (d ({0,1,2,4,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 4), Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 5), Clifford.cliffordPoint (c 0) (c 1) (c 4) (c 5)} := by
    have e := (hdes ({0,1,2,4,5} : Finset (Fin 6)) (by decide)).symm.trans des2
    have := congrArg (fun F : Finset (Finset (Fin 6)) => P '' (F : Set (Finset (Fin 6)))) e
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton] at this
    rw [this, e1, e2, e5]
  have m4 := hnc ({0,1,2,4,5} : Finset (Fin 6)) (by decide)
  rw [sS2] at m4
  have sS3 : ({P (a ({0,1,3,4,5} : Finset (Fin 6))), P (b ({0,1,3,4,5} : Finset (Fin 6))), P (d ({0,1,3,4,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 4), Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 5), Clifford.cliffordPoint (c 0) (c 1) (c 4) (c 5)} := by
    have e := (hdes ({0,1,3,4,5} : Finset (Fin 6)) (by decide)).symm.trans des3
    have := congrArg (fun F : Finset (Finset (Fin 6)) => P '' (F : Set (Finset (Fin 6)))) e
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton] at this
    rw [this, e3, e4, e5]
  have m3 := hnc ({0,1,3,4,5} : Finset (Fin 6)) (by decide)
  rw [sS3] at m3
  have sS4 : ({P (a ({0,2,3,4,5} : Finset (Fin 6))), P (b ({0,2,3,4,5} : Finset (Fin 6))), P (d ({0,2,3,4,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 2) (c 3) (c 4), Clifford.cliffordPoint (c 0) (c 2) (c 3) (c 5), Clifford.cliffordPoint (c 0) (c 2) (c 4) (c 5)} := by
    have e := (hdes ({0,2,3,4,5} : Finset (Fin 6)) (by decide)).symm.trans des4
    have := congrArg (fun F : Finset (Finset (Fin 6)) => P '' (F : Set (Finset (Fin 6)))) e
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton] at this
    rw [this, e6, e7, e8]
  have m2 := hnc ({0,2,3,4,5} : Finset (Fin 6)) (by decide)
  rw [sS4] at m2
  have sS5 : ({P (a ({1,2,3,4,5} : Finset (Fin 6))), P (b ({1,2,3,4,5} : Finset (Fin 6))), P (d ({1,2,3,4,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 1) (c 2) (c 3) (c 4), Clifford.cliffordPoint (c 1) (c 2) (c 3) (c 5), Clifford.cliffordPoint (c 1) (c 2) (c 4) (c 5)} := by
    have e := (hdes ({1,2,3,4,5} : Finset (Fin 6)) (by decide)).symm.trans des5
    have := congrArg (fun F : Finset (Finset (Fin 6)) => P '' (F : Set (Finset (Fin 6)))) e
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton] at this
    rw [this, e10, e11, e12]
  have m1 := hnc ({1,2,3,4,5} : Finset (Fin 6)) (by decide)
  rw [sS5] at m1
  obtain ⟨Q, ⟨q0, Q0⟩, ⟨q1, Q1⟩, ⟨q2, Q2⟩, ⟨q3, Q3⟩, ⟨q4, Q4⟩, ⟨q5, Q5⟩⟩ := h (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)
    (H 0 1 (by decide)) (H 0 2 (by decide)) (H 0 3 (by decide)) (H 0 4 (by decide)) (H 0 5 (by decide)) (H 1 2 (by decide)) (H 1 3 (by decide)) (H 1 4 (by decide)) (H 1 5 (by decide)) (H 2 3 (by decide)) (H 2 4 (by decide)) (H 2 5 (by decide)) (H 3 4 (by decide)) (H 3 5 (by decide)) (H 4 5 (by decide))
    (N 0 1 2 (by decide) (by decide)) (N 0 1 3 (by decide) (by decide)) (N 0 1 4 (by decide) (by decide)) (N 0 1 5 (by decide) (by decide)) (N 0 2 3 (by decide) (by decide)) (N 0 2 4 (by decide) (by decide)) (N 0 2 5 (by decide) (by decide)) (N 0 3 4 (by decide) (by decide)) (N 0 3 5 (by decide) (by decide)) (N 0 4 5 (by decide) (by decide)) (N 1 2 3 (by decide) (by decide)) (N 1 2 4 (by decide) (by decide)) (N 1 2 5 (by decide) (by decide)) (N 1 3 4 (by decide) (by decide)) (N 1 3 5 (by decide) (by decide)) (N 1 4 5 (by decide) (by decide)) (N 2 3 4 (by decide) (by decide)) (N 2 3 5 (by decide) (by decide)) (N 2 4 5 (by decide) (by decide)) (N 3 4 5 (by decide) (by decide))
    m6 m5 m4 m3 m2 m1
  refine ⟨?_, Q, ?_⟩
  · intro S hS T hTS hT
    rcases S6 S hS with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [circ_congr _ sS0]
      rcases T15 T hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hTS; decide) | (simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]; exact (onCircum_iff m6).2 (q0 _ (by simp)))
    · rw [circ_congr _ sS1]
      rcases T15 T hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hTS; decide) | (simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]; exact (onCircum_iff m5).2 (q1 _ (by simp)))
    · rw [circ_congr _ sS2]
      rcases T15 T hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hTS; decide) | (simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]; exact (onCircum_iff m4).2 (q2 _ (by simp)))
    · rw [circ_congr _ sS3]
      rcases T15 T hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hTS; decide) | (simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]; exact (onCircum_iff m3).2 (q3 _ (by simp)))
    · rw [circ_congr _ sS4]
      rcases T15 T hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hTS; decide) | (simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]; exact (onCircum_iff m2).2 (q4 _ (by simp)))
    · rw [circ_congr _ sS5]
      rcases T15 T hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | (exfalso; revert hTS; decide) | (simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]; exact (onCircum_iff m1).2 (q5 _ (by simp)))
  · intro S hS
    rcases S6 S hS with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [circ_congr _ sS0]; exact (onCircum_iff m6).2 Q0
    · rw [circ_congr _ sS1]; exact (onCircum_iff m5).2 Q1
    · rw [circ_congr _ sS2]; exact (onCircum_iff m4).2 Q2
    · rw [circ_congr _ sS3]; exact (onCircum_iff m3).2 Q3
    · rw [circ_congr _ sS4]; exact (onCircum_iff m2).2 Q4
    · rw [circ_congr _ sS5]; exact (onCircum_iff m1).2 Q5

/-- the blind writer's designated subsets, as functions -/
def dA (S : Finset (Fin 6)) : Finset (Fin 6) := S.erase (((S.sort (· ≤ ·)).reverse).getD 0 0)
def dB (S : Finset (Fin 6)) : Finset (Fin 6) := S.erase (((S.sort (· ≤ ·)).reverse).getD 1 0)
def dD (S : Finset (Fin 6)) : Finset (Fin 6) := S.erase (((S.sort (· ≤ ·)).reverse).getD 2 0)

/-- explicit point of a 4-subset (the repo's `cliffordPoint` of the sorted subset) -/
def cpT (c : Fin 6 → ℂ) (T : Finset (Fin 6)) : ℂ :=
  let l := T.sort (· ≤ ·)
  Clifford.cliffordPoint (c (l.getD 0 0)) (c (l.getD 1 0)) (c (l.getD 2 0)) (c (l.getD 3 0))

lemma cpT0 (c : Fin 6 → ℂ) : cpT c ({0,1,2,3} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 3) := by
  simp only [cpT, s4 0 1 2 3 (by decide)]; rfl
lemma cpT1 (c : Fin 6 → ℂ) : cpT c ({0,1,2,4} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 4) := by
  simp only [cpT, s4 0 1 2 4 (by decide)]; rfl
lemma cpT2 (c : Fin 6 → ℂ) : cpT c ({0,1,2,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 5) := by
  simp only [cpT, s4 0 1 2 5 (by decide)]; rfl
lemma cpT3 (c : Fin 6 → ℂ) : cpT c ({0,1,3,4} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 4) := by
  simp only [cpT, s4 0 1 3 4 (by decide)]; rfl
lemma cpT4 (c : Fin 6 → ℂ) : cpT c ({0,1,3,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 5) := by
  simp only [cpT, s4 0 1 3 5 (by decide)]; rfl
lemma cpT5 (c : Fin 6 → ℂ) : cpT c ({0,1,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 1) (c 4) (c 5) := by
  simp only [cpT, s4 0 1 4 5 (by decide)]; rfl
lemma cpT6 (c : Fin 6 → ℂ) : cpT c ({0,2,3,4} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 2) (c 3) (c 4) := by
  simp only [cpT, s4 0 2 3 4 (by decide)]; rfl
lemma cpT7 (c : Fin 6 → ℂ) : cpT c ({0,2,3,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 2) (c 3) (c 5) := by
  simp only [cpT, s4 0 2 3 5 (by decide)]; rfl
lemma cpT8 (c : Fin 6 → ℂ) : cpT c ({0,2,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 2) (c 4) (c 5) := by
  simp only [cpT, s4 0 2 4 5 (by decide)]; rfl
lemma cpT9 (c : Fin 6 → ℂ) : cpT c ({0,3,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 0) (c 3) (c 4) (c 5) := by
  simp only [cpT, s4 0 3 4 5 (by decide)]; rfl
lemma cpT10 (c : Fin 6 → ℂ) : cpT c ({1,2,3,4} : Finset (Fin 6)) = Clifford.cliffordPoint (c 1) (c 2) (c 3) (c 4) := by
  simp only [cpT, s4 1 2 3 4 (by decide)]; rfl
lemma cpT11 (c : Fin 6 → ℂ) : cpT c ({1,2,3,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 1) (c 2) (c 3) (c 5) := by
  simp only [cpT, s4 1 2 3 5 (by decide)]; rfl
lemma cpT12 (c : Fin 6 → ℂ) : cpT c ({1,2,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 1) (c 2) (c 4) (c 5) := by
  simp only [cpT, s4 1 2 4 5 (by decide)]; rfl
lemma cpT13 (c : Fin 6 → ℂ) : cpT c ({1,3,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 1) (c 3) (c 4) (c 5) := by
  simp only [cpT, s4 1 3 4 5 (by decide)]; rfl
lemma cpT14 (c : Fin 6 → ℂ) : cpT c ({2,3,4,5} : Finset (Fin 6)) = Clifford.cliffordPoint (c 2) (c 3) (c 4) (c 5) := by
  simp only [cpT, s4 2 3 4 5 (by decide)]; rfl
lemma abd0 : dA ({0,1,2,3,4} : Finset (Fin 6)) = ({0,1,2,3} : Finset (Fin 6)) ∧ dB ({0,1,2,3,4} : Finset (Fin 6)) = ({0,1,2,4} : Finset (Fin 6)) ∧ dD ({0,1,2,3,4} : Finset (Fin 6)) = ({0,1,3,4} : Finset (Fin 6)) := by
  simp only [dA, dB, dD, s5 0 1 2 3 4 (by decide)]; decide
lemma abd1 : dA ({0,1,2,3,5} : Finset (Fin 6)) = ({0,1,2,3} : Finset (Fin 6)) ∧ dB ({0,1,2,3,5} : Finset (Fin 6)) = ({0,1,2,5} : Finset (Fin 6)) ∧ dD ({0,1,2,3,5} : Finset (Fin 6)) = ({0,1,3,5} : Finset (Fin 6)) := by
  simp only [dA, dB, dD, s5 0 1 2 3 5 (by decide)]; decide
lemma abd2 : dA ({0,1,2,4,5} : Finset (Fin 6)) = ({0,1,2,4} : Finset (Fin 6)) ∧ dB ({0,1,2,4,5} : Finset (Fin 6)) = ({0,1,2,5} : Finset (Fin 6)) ∧ dD ({0,1,2,4,5} : Finset (Fin 6)) = ({0,1,4,5} : Finset (Fin 6)) := by
  simp only [dA, dB, dD, s5 0 1 2 4 5 (by decide)]; decide
lemma abd3 : dA ({0,1,3,4,5} : Finset (Fin 6)) = ({0,1,3,4} : Finset (Fin 6)) ∧ dB ({0,1,3,4,5} : Finset (Fin 6)) = ({0,1,3,5} : Finset (Fin 6)) ∧ dD ({0,1,3,4,5} : Finset (Fin 6)) = ({0,1,4,5} : Finset (Fin 6)) := by
  simp only [dA, dB, dD, s5 0 1 3 4 5 (by decide)]; decide
lemma abd4 : dA ({0,2,3,4,5} : Finset (Fin 6)) = ({0,2,3,4} : Finset (Fin 6)) ∧ dB ({0,2,3,4,5} : Finset (Fin 6)) = ({0,2,3,5} : Finset (Fin 6)) ∧ dD ({0,2,3,4,5} : Finset (Fin 6)) = ({0,2,4,5} : Finset (Fin 6)) := by
  simp only [dA, dB, dD, s5 0 2 3 4 5 (by decide)]; decide
lemma abd5 : dA ({1,2,3,4,5} : Finset (Fin 6)) = ({1,2,3,4} : Finset (Fin 6)) ∧ dB ({1,2,3,4,5} : Finset (Fin 6)) = ({1,2,3,5} : Finset (Fin 6)) ∧ dD ({1,2,3,4,5} : Finset (Fin 6)) = ({1,2,4,5} : Finset (Fin 6)) := by
  simp only [dA, dB, dD, s5 1 2 3 4 5 (by decide)]; decide

set_option maxHeartbeats 8000000 in
/-- B→R, conditional on the *statement* of `Clifford.cliffordPoint_mem_gams` (premise; the
repo theorem itself is not used). -/
theorem br_4_given_cp :
    blind4_stmt → (type_of% @Clifford.cliffordPoint_mem_gams) →
      (type_of% @Clifford.clifford_three) := by
  intro h hcp c₁ c₂ c₃ c₄ c₅ c₆ h12 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
    n123 n124 n125 n126 n134 n135 n136 n145 n146 n156 n234 n235 n236 n245 n246 n256 n345 n346 n356 n456
    m6 m5 m4 m3 m2 m1
  let c : Fin 6 → ℂ := ![c₁, c₂, c₃, c₄, c₅, c₆]
  have hc : BlindCliffordHyp c := by
    refine ⟨fun i j hij => ?_, fun i j k hij hjk => ?_⟩
    · fin_cases i <;> fin_cases j <;>
        first | (exfalso; revert hij; decide) | assumption
    · fin_cases i <;> fin_cases j <;> fin_cases k <;>
        first | (exfalso; revert hij hjk; decide) | assumption
  have H := hc.1; have N := hc.2
  have g0 := hcp (c 0) (c 1) (c 2) (c 3) (H 0 1 (by decide)) (H 0 2 (by decide)) (H 0 3 (by decide)) (H 1 2 (by decide)) (H 1 3 (by decide)) (H 2 3 (by decide)) (N 0 1 2 (by decide) (by decide)) (N 0 1 3 (by decide) (by decide)) (N 0 2 3 (by decide) (by decide)) (N 1 2 3 (by decide) (by decide))
  have g1 := hcp (c 0) (c 1) (c 2) (c 4) (H 0 1 (by decide)) (H 0 2 (by decide)) (H 0 4 (by decide)) (H 1 2 (by decide)) (H 1 4 (by decide)) (H 2 4 (by decide)) (N 0 1 2 (by decide) (by decide)) (N 0 1 4 (by decide) (by decide)) (N 0 2 4 (by decide) (by decide)) (N 1 2 4 (by decide) (by decide))
  have g2 := hcp (c 0) (c 1) (c 2) (c 5) (H 0 1 (by decide)) (H 0 2 (by decide)) (H 0 5 (by decide)) (H 1 2 (by decide)) (H 1 5 (by decide)) (H 2 5 (by decide)) (N 0 1 2 (by decide) (by decide)) (N 0 1 5 (by decide) (by decide)) (N 0 2 5 (by decide) (by decide)) (N 1 2 5 (by decide) (by decide))
  have g3 := hcp (c 0) (c 1) (c 3) (c 4) (H 0 1 (by decide)) (H 0 3 (by decide)) (H 0 4 (by decide)) (H 1 3 (by decide)) (H 1 4 (by decide)) (H 3 4 (by decide)) (N 0 1 3 (by decide) (by decide)) (N 0 1 4 (by decide) (by decide)) (N 0 3 4 (by decide) (by decide)) (N 1 3 4 (by decide) (by decide))
  have g4 := hcp (c 0) (c 1) (c 3) (c 5) (H 0 1 (by decide)) (H 0 3 (by decide)) (H 0 5 (by decide)) (H 1 3 (by decide)) (H 1 5 (by decide)) (H 3 5 (by decide)) (N 0 1 3 (by decide) (by decide)) (N 0 1 5 (by decide) (by decide)) (N 0 3 5 (by decide) (by decide)) (N 1 3 5 (by decide) (by decide))
  have g5 := hcp (c 0) (c 1) (c 4) (c 5) (H 0 1 (by decide)) (H 0 4 (by decide)) (H 0 5 (by decide)) (H 1 4 (by decide)) (H 1 5 (by decide)) (H 4 5 (by decide)) (N 0 1 4 (by decide) (by decide)) (N 0 1 5 (by decide) (by decide)) (N 0 4 5 (by decide) (by decide)) (N 1 4 5 (by decide) (by decide))
  have g6 := hcp (c 0) (c 2) (c 3) (c 4) (H 0 2 (by decide)) (H 0 3 (by decide)) (H 0 4 (by decide)) (H 2 3 (by decide)) (H 2 4 (by decide)) (H 3 4 (by decide)) (N 0 2 3 (by decide) (by decide)) (N 0 2 4 (by decide) (by decide)) (N 0 3 4 (by decide) (by decide)) (N 2 3 4 (by decide) (by decide))
  have g7 := hcp (c 0) (c 2) (c 3) (c 5) (H 0 2 (by decide)) (H 0 3 (by decide)) (H 0 5 (by decide)) (H 2 3 (by decide)) (H 2 5 (by decide)) (H 3 5 (by decide)) (N 0 2 3 (by decide) (by decide)) (N 0 2 5 (by decide) (by decide)) (N 0 3 5 (by decide) (by decide)) (N 2 3 5 (by decide) (by decide))
  have g8 := hcp (c 0) (c 2) (c 4) (c 5) (H 0 2 (by decide)) (H 0 4 (by decide)) (H 0 5 (by decide)) (H 2 4 (by decide)) (H 2 5 (by decide)) (H 4 5 (by decide)) (N 0 2 4 (by decide) (by decide)) (N 0 2 5 (by decide) (by decide)) (N 0 4 5 (by decide) (by decide)) (N 2 4 5 (by decide) (by decide))
  have g9 := hcp (c 0) (c 3) (c 4) (c 5) (H 0 3 (by decide)) (H 0 4 (by decide)) (H 0 5 (by decide)) (H 3 4 (by decide)) (H 3 5 (by decide)) (H 4 5 (by decide)) (N 0 3 4 (by decide) (by decide)) (N 0 3 5 (by decide) (by decide)) (N 0 4 5 (by decide) (by decide)) (N 3 4 5 (by decide) (by decide))
  have g10 := hcp (c 1) (c 2) (c 3) (c 4) (H 1 2 (by decide)) (H 1 3 (by decide)) (H 1 4 (by decide)) (H 2 3 (by decide)) (H 2 4 (by decide)) (H 3 4 (by decide)) (N 1 2 3 (by decide) (by decide)) (N 1 2 4 (by decide) (by decide)) (N 1 3 4 (by decide) (by decide)) (N 2 3 4 (by decide) (by decide))
  have g11 := hcp (c 1) (c 2) (c 3) (c 5) (H 1 2 (by decide)) (H 1 3 (by decide)) (H 1 5 (by decide)) (H 2 3 (by decide)) (H 2 5 (by decide)) (H 3 5 (by decide)) (N 1 2 3 (by decide) (by decide)) (N 1 2 5 (by decide) (by decide)) (N 1 3 5 (by decide) (by decide)) (N 2 3 5 (by decide) (by decide))
  have g12 := hcp (c 1) (c 2) (c 4) (c 5) (H 1 2 (by decide)) (H 1 4 (by decide)) (H 1 5 (by decide)) (H 2 4 (by decide)) (H 2 5 (by decide)) (H 4 5 (by decide)) (N 1 2 4 (by decide) (by decide)) (N 1 2 5 (by decide) (by decide)) (N 1 4 5 (by decide) (by decide)) (N 2 4 5 (by decide) (by decide))
  have g13 := hcp (c 1) (c 3) (c 4) (c 5) (H 1 3 (by decide)) (H 1 4 (by decide)) (H 1 5 (by decide)) (H 3 4 (by decide)) (H 3 5 (by decide)) (H 4 5 (by decide)) (N 1 3 4 (by decide) (by decide)) (N 1 3 5 (by decide) (by decide)) (N 1 4 5 (by decide) (by decide)) (N 3 4 5 (by decide) (by decide))
  have g14 := hcp (c 2) (c 3) (c 4) (c 5) (H 2 3 (by decide)) (H 2 4 (by decide)) (H 2 5 (by decide)) (H 3 4 (by decide)) (H 3 5 (by decide)) (H 4 5 (by decide)) (N 2 3 4 (by decide) (by decide)) (N 2 3 5 (by decide) (by decide)) (N 2 4 5 (by decide) (by decide)) (N 3 4 5 (by decide) (by decide))
  have hP : ∀ T : Finset (Fin 6), T.card = 4 → BlindIsCp c T (cpT c T) := by
    intro T hT
    rcases T15 T hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [cpT0]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g0
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT1]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g1
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT2]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g2
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT3]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g3
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT4]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g4
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT5]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g5
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT6]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g6
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT7]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g7
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT8]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g8
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT9]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g9
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT10]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g10
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT11]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g11
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT12]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g12
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT13]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g13
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
    · rw [cpT14]
      intro i hi j hj k hk hij hjk
      rw [gamma_iff c hc hij hjk]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
      obtain ⟨x1, x2, x3, x4⟩ := g14
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
        first | (exfalso; revert hij hjk; decide) | assumption
  have hdes : ∀ S : Finset (Fin 6), S.card = 5 → BlindDesignated S = {dA S, dB S, dD S} := by
    intro S hS
    rcases S6 S hS with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨x, y, z⟩ := abd0; rw [des0, x, y, z]
    · obtain ⟨x, y, z⟩ := abd1; rw [des1, x, y, z]
    · obtain ⟨x, y, z⟩ := abd2; rw [des2, x, y, z]
    · obtain ⟨x, y, z⟩ := abd3; rw [des3, x, y, z]
    · obtain ⟨x, y, z⟩ := abd4; rw [des4, x, y, z]
    · obtain ⟨x, y, z⟩ := abd5; rw [des5, x, y, z]
  have sS0 : ({cpT c (dA ({0,1,2,3,4} : Finset (Fin 6))), cpT c (dB ({0,1,2,3,4} : Finset (Fin 6))), cpT c (dD ({0,1,2,3,4} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 3), Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 4), Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 4)} := by
    obtain ⟨x, y, z⟩ := abd0; rw [x, y, z, cpT0, cpT1, cpT3]
  have sS1 : ({cpT c (dA ({0,1,2,3,5} : Finset (Fin 6))), cpT c (dB ({0,1,2,3,5} : Finset (Fin 6))), cpT c (dD ({0,1,2,3,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 3), Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 5), Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 5)} := by
    obtain ⟨x, y, z⟩ := abd1; rw [x, y, z, cpT0, cpT2, cpT4]
  have sS2 : ({cpT c (dA ({0,1,2,4,5} : Finset (Fin 6))), cpT c (dB ({0,1,2,4,5} : Finset (Fin 6))), cpT c (dD ({0,1,2,4,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 4), Clifford.cliffordPoint (c 0) (c 1) (c 2) (c 5), Clifford.cliffordPoint (c 0) (c 1) (c 4) (c 5)} := by
    obtain ⟨x, y, z⟩ := abd2; rw [x, y, z, cpT1, cpT2, cpT5]
  have sS3 : ({cpT c (dA ({0,1,3,4,5} : Finset (Fin 6))), cpT c (dB ({0,1,3,4,5} : Finset (Fin 6))), cpT c (dD ({0,1,3,4,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 4), Clifford.cliffordPoint (c 0) (c 1) (c 3) (c 5), Clifford.cliffordPoint (c 0) (c 1) (c 4) (c 5)} := by
    obtain ⟨x, y, z⟩ := abd3; rw [x, y, z, cpT3, cpT4, cpT5]
  have sS4 : ({cpT c (dA ({0,2,3,4,5} : Finset (Fin 6))), cpT c (dB ({0,2,3,4,5} : Finset (Fin 6))), cpT c (dD ({0,2,3,4,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 0) (c 2) (c 3) (c 4), Clifford.cliffordPoint (c 0) (c 2) (c 3) (c 5), Clifford.cliffordPoint (c 0) (c 2) (c 4) (c 5)} := by
    obtain ⟨x, y, z⟩ := abd4; rw [x, y, z, cpT6, cpT7, cpT8]
  have sS5 : ({cpT c (dA ({1,2,3,4,5} : Finset (Fin 6))), cpT c (dB ({1,2,3,4,5} : Finset (Fin 6))), cpT c (dD ({1,2,3,4,5} : Finset (Fin 6)))} : Set ℂ) = {Clifford.cliffordPoint (c 1) (c 2) (c 3) (c 4), Clifford.cliffordPoint (c 1) (c 2) (c 3) (c 5), Clifford.cliffordPoint (c 1) (c 2) (c 4) (c 5)} := by
    obtain ⟨x, y, z⟩ := abd5; rw [x, y, z, cpT10, cpT11, cpT12]
  have hnc : ∀ S : Finset (Fin 6), S.card = 5 →
      ¬ Collinear ℝ ({cpT c (dA S), cpT c (dB S), cpT c (dD S)} : Set ℂ) := by
    intro S hS
    rcases S6 S hS with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [sS0]; exact m6
    · rw [sS1]; exact m5
    · rw [sS2]; exact m4
    · rw [sS3]; exact m3
    · rw [sS4]; exact m2
    · rw [sS5]; exact m1
  obtain ⟨h1, z, hz⟩ := h c hc (cpT c) hP dA dB dD hdes hnc
  refine ⟨z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have q := fun T (hT : T ⊆ ({0,1,2,3,4} : Finset (Fin 6))) (hc4 : T.card = 4) => (onCircum_iff m6).1 ((circ_congr _ sS0).1 (h1 ({0,1,2,3,4} : Finset (Fin 6)) (by decide) T hT hc4))
    refine ⟨fun p hp => ?_, (onCircum_iff m6).1 ((circ_congr _ sS0).1 (hz ({0,1,2,3,4} : Finset (Fin 6)) (by decide)))⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (by have := q ({0,1,2,3} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT0] at this)
    · exact (by have := q ({0,1,2,4} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT1] at this)
    · exact (by have := q ({0,1,3,4} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT3] at this)
    · exact (by have := q ({0,2,3,4} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT6] at this)
    · exact (by have := q ({1,2,3,4} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT10] at this)
  · have q := fun T (hT : T ⊆ ({0,1,2,3,5} : Finset (Fin 6))) (hc4 : T.card = 4) => (onCircum_iff m5).1 ((circ_congr _ sS1).1 (h1 ({0,1,2,3,5} : Finset (Fin 6)) (by decide) T hT hc4))
    refine ⟨fun p hp => ?_, (onCircum_iff m5).1 ((circ_congr _ sS1).1 (hz ({0,1,2,3,5} : Finset (Fin 6)) (by decide)))⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (by have := q ({0,1,2,3} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT0] at this)
    · exact (by have := q ({0,1,2,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT2] at this)
    · exact (by have := q ({0,1,3,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT4] at this)
    · exact (by have := q ({0,2,3,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT7] at this)
    · exact (by have := q ({1,2,3,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT11] at this)
  · have q := fun T (hT : T ⊆ ({0,1,2,4,5} : Finset (Fin 6))) (hc4 : T.card = 4) => (onCircum_iff m4).1 ((circ_congr _ sS2).1 (h1 ({0,1,2,4,5} : Finset (Fin 6)) (by decide) T hT hc4))
    refine ⟨fun p hp => ?_, (onCircum_iff m4).1 ((circ_congr _ sS2).1 (hz ({0,1,2,4,5} : Finset (Fin 6)) (by decide)))⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (by have := q ({0,1,2,4} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT1] at this)
    · exact (by have := q ({0,1,2,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT2] at this)
    · exact (by have := q ({0,1,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT5] at this)
    · exact (by have := q ({0,2,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT8] at this)
    · exact (by have := q ({1,2,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT12] at this)
  · have q := fun T (hT : T ⊆ ({0,1,3,4,5} : Finset (Fin 6))) (hc4 : T.card = 4) => (onCircum_iff m3).1 ((circ_congr _ sS3).1 (h1 ({0,1,3,4,5} : Finset (Fin 6)) (by decide) T hT hc4))
    refine ⟨fun p hp => ?_, (onCircum_iff m3).1 ((circ_congr _ sS3).1 (hz ({0,1,3,4,5} : Finset (Fin 6)) (by decide)))⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (by have := q ({0,1,3,4} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT3] at this)
    · exact (by have := q ({0,1,3,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT4] at this)
    · exact (by have := q ({0,1,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT5] at this)
    · exact (by have := q ({0,3,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT9] at this)
    · exact (by have := q ({1,3,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT13] at this)
  · have q := fun T (hT : T ⊆ ({0,2,3,4,5} : Finset (Fin 6))) (hc4 : T.card = 4) => (onCircum_iff m2).1 ((circ_congr _ sS4).1 (h1 ({0,2,3,4,5} : Finset (Fin 6)) (by decide) T hT hc4))
    refine ⟨fun p hp => ?_, (onCircum_iff m2).1 ((circ_congr _ sS4).1 (hz ({0,2,3,4,5} : Finset (Fin 6)) (by decide)))⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (by have := q ({0,2,3,4} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT6] at this)
    · exact (by have := q ({0,2,3,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT7] at this)
    · exact (by have := q ({0,2,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT8] at this)
    · exact (by have := q ({0,3,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT9] at this)
    · exact (by have := q ({2,3,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT14] at this)
  · have q := fun T (hT : T ⊆ ({1,2,3,4,5} : Finset (Fin 6))) (hc4 : T.card = 4) => (onCircum_iff m1).1 ((circ_congr _ sS5).1 (h1 ({1,2,3,4,5} : Finset (Fin 6)) (by decide) T hT hc4))
    refine ⟨fun p hp => ?_, (onCircum_iff m1).1 ((circ_congr _ sS5).1 (hz ({1,2,3,4,5} : Finset (Fin 6)) (by decide)))⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (by have := q ({1,2,3,4} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT10] at this)
    · exact (by have := q ({1,2,3,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT11] at this)
    · exact (by have := q ({1,2,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT12] at this)
    · exact (by have := q ({1,3,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT13] at this)
    · exact (by have := q ({2,3,4,5} : Finset (Fin 6)) (by decide) (by decide); rwa [cpT14] at this)
