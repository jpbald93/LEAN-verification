import Kosnita

/-! L13 comparer scratch: blind_10 vs `Kosnita.kosnita`.
Bridge lemmas from the repo used: `Kosnita.dist_sq`, `Kosnita.cross_of_collinear`,
`Kosnita.collinear_of_cross` (coordinate descriptions of `dist` / `Collinear`). -/

open Affine EuclideanGeometry

abbrev BlindPlane := EuclideanSpace ℝ (Fin 2)

/-- blind_10 verbatim. -/
def blind10_stmt : Prop :=
  ∀ (t : Affine.Triangle ℝ BlindPlane) (Oa Ob Oc : BlindPlane)
    (hnA : t.circumcenter ≠ midpoint ℝ (t.points 1) (t.points 2))
    (hnB : t.circumcenter ≠ midpoint ℝ (t.points 2) (t.points 0))
    (hnC : t.circumcenter ≠ midpoint ℝ (t.points 0) (t.points 1))
    (hS : dist (t.points 0) (t.points 1) ^ 2 + dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 ≠ 5 * t.circumradius ^ 2)
    (hOa : dist Oa t.circumcenter = dist Oa (t.points 1) ∧ dist Oa (t.points 1) = dist Oa (t.points 2))
    (hOb : dist Ob t.circumcenter = dist Ob (t.points 2) ∧ dist Ob (t.points 2) = dist Ob (t.points 0))
    (hOc : dist Oc t.circumcenter = dist Oc (t.points 0) ∧ dist Oc (t.points 0) = dist Oc (t.points 1)),
    ∃ X : BlindPlane, X ∈ line[ℝ, t.points 0, Oa] ∧ X ∈ line[ℝ, t.points 1, Ob] ∧
      X ∈ line[ℝ, t.points 2, Oc]

/-- type of `Kosnita.kosnita`, verbatim. -/
def real10_stmt : Prop :=
  ∀ (A B C O Oa Ob Oc : Kosnita.Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Kosnita.Plane))
    (hOA : dist O A = dist O B) (hOC : dist O A = dist O C)
    (hOBC : ¬ Collinear ℝ ({O, B, C} : Set Kosnita.Plane))
    (hOCA : ¬ Collinear ℝ ({O, C, A} : Set Kosnita.Plane))
    (hOAB : ¬ Collinear ℝ ({O, A, B} : Set Kosnita.Plane))
    (hOa1 : dist Oa O = dist Oa B) (hOa2 : dist Oa O = dist Oa C)
    (hOb1 : dist Ob O = dist Ob C) (hOb2 : dist Ob O = dist Ob A)
    (hOc1 : dist Oc O = dist Oc A) (hOc2 : dist Oc O = dist Oc B)
    (hS : dist A B ^ 2 + dist B C ^ 2 + dist C A ^ 2 ≠ 5 * dist O A ^ 2),
    ∃ P : Kosnita.Plane, Collinear ℝ ({A, Oa, P} : Set Kosnita.Plane) ∧
      Collinear ℝ ({B, Ob, P} : Set Kosnita.Plane) ∧ Collinear ℝ ({C, Oc, P} : Set Kosnita.Plane)

-- type check only: `real10_stmt` is the type of the published theorem (not used below)
example : real10_stmt := @Kosnita.kosnita

lemma ne_or_of_ne (B C : BlindPlane) (h : B ≠ C) : B 0 - C 0 ≠ 0 ∨ B 1 - C 1 ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h; ext i; fin_cases i
  · simpa [sub_eq_zero] using hn.1
  · simpa [sub_eq_zero] using hn.2

/-- An equidistant point `O` of `B ≠ C` is collinear with them iff it is their midpoint. -/
lemma collinear_iff_midpoint (O B C : BlindPlane) (hBC : B ≠ C) (h : dist O B = dist O C) :
    Collinear ℝ ({O, B, C} : Set BlindPlane) ↔ O = midpoint ℝ B C := by
  constructor
  · intro hc
    have hx := Kosnita.cross_of_collinear O B C hc
    have he := congrArg (· ^ 2) h
    simp only [Kosnita.dist_sq] at he
    unfold Kosnita.cross at hx
    have hd := ne_or_of_ne B C hBC
    have k1 : (B 0 - O 0 + (C 0 - O 0)) * (B 0 - C 0) + (B 1 - O 1 + (C 1 - O 1)) * (B 1 - C 1) = 0 := by
      linear_combination he
    have k2 : (B 0 - O 0 + (C 0 - O 0)) * (B 1 - C 1) - (B 1 - O 1 + (C 1 - O 1)) * (B 0 - C 0) = 0 := by
      linear_combination (-2) * hx
    have hp : (B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2 ≠ 0 := by
      rcases hd with hd | hd
      · have := pow_pos (abs_pos.mpr hd) 2; rw [sq_abs] at this; positivity
      · have := pow_pos (abs_pos.mpr hd) 2; rw [sq_abs] at this; positivity
    have e1 : (B 0 - O 0 + (C 0 - O 0)) * ((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2) = 0 := by
      linear_combination (B 0 - C 0) * k1 + (B 1 - C 1) * k2
    have e2 : (B 1 - O 1 + (C 1 - O 1)) * ((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2) = 0 := by
      linear_combination (B 1 - C 1) * k1 - (B 0 - C 0) * k2
    have s1 := (mul_eq_zero.mp e1).resolve_right hp
    have s2 := (mul_eq_zero.mp e2).resolve_right hp
    rw [midpoint_eq_smul_add]
    ext i; fin_cases i
    · simp; linarith
    · simp; linarith
  · rintro rfl
    apply Kosnita.collinear_of_cross
    rw [midpoint_eq_smul_add]
    simp [Kosnita.cross]; ring

/-- If `X` (on the circle with centre `O` through `X, Y, Z`, `Y ≠ Z`) is itself equidistant from
`O, Y, Z`, then `XY² + YZ² + ZX² = 5 OX²`. -/
lemma sumSq_of_eq (O X Y Z : BlindPlane) (hYZ : Y ≠ Z)
    (h1 : dist O X = dist O Y) (h2 : dist O X = dist O Z)
    (h3 : dist X O = dist X Y) (h4 : dist X O = dist X Z) :
    dist X Y ^ 2 + dist Y Z ^ 2 + dist Z X ^ 2 = 5 * dist O X ^ 2 := by
  have e1 := congrArg (· ^ 2) h1; have e2 := congrArg (· ^ 2) h2
  have e3 := congrArg (· ^ 2) h3; have e4 := congrArg (· ^ 2) h4
  simp only [Kosnita.dist_sq] at e1 e2 e3 e4 ⊢
  have hd := ne_or_of_ne Y Z hYZ
  have hd' : (Y 0 - Z 0) ^ 2 + (Y 1 - Z 1) ^ 2 ≠ 0 := by
    rcases hd with hd | hd
    · have := pow_pos (abs_pos.mpr hd) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.mpr hd) 2; rw [sq_abs] at this; positivity
  -- coordinates relative to O
  obtain ⟨a1, ha1⟩ : ∃ a, a = X 0 - O 0 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a, a = X 1 - O 1 := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ a, a = Y 0 - O 0 := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ a, a = Y 1 - O 1 := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ a, a = Z 0 - O 0 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ a, a = Z 1 - O 1 := ⟨_, rfl⟩
  have rX0 : X 0 = a1 + O 0 := by linarith
  have rX1 : X 1 = a2 + O 1 := by linarith
  have rY0 : Y 0 = b1 + O 0 := by linarith
  have rY1 : Y 1 = b2 + O 1 := by linarith
  have rZ0 : Z 0 = c1 + O 0 := by linarith
  have rZ1 : Z 1 = c2 + O 1 := by linarith
  simp only [rX0, rX1, rY0, rY1, rZ0, rZ1] at e1 e2 e3 e4 hd' ⊢
  ring_nf at e1 e2 e3 e4 hd' ⊢
  have hd2 : (b1 - c1) ^ 2 + (b2 - c2) ^ 2 ≠ 0 := by
    intro h0; apply hd'; linear_combination h0
  -- e1: |b|² = |a|², e2: |c|² = |a|², e3: |a-b|² = |a|², e4: |a-c|² = |a|²
  have k1 : a1 * (b1 - c1) + a2 * (b2 - c2) = 0 := by linarith
  have k2 : (b1 + c1) * (b1 - c1) + (b2 + c2) * (b2 - c2) = 0 := by linear_combination e2 - e1
  have hx : a1 * (b2 + c2) - a2 * (b1 + c1) = 0 := by
    have q : (a1 * (b2 + c2) - a2 * (b1 + c1)) * ((b1 - c1) ^ 2 + (b2 - c2) ^ 2) = 0 := by
      linear_combination ((b2 + c2) * (b1 - c1) - (b1 + c1) * (b2 - c2)) * k1 +
        (a1 * (b2 - c2) - a2 * (b1 - c1)) * k2
    exact (mul_eq_zero.mp q).resolve_right hd2
  have as : a1 * (b1 + c1) + a2 * (b2 + c2) = a1 ^ 2 + a2 ^ 2 := by
    linarith
  have hρ : a1 ^ 2 + a2 ^ 2 ≠ 0 := by
    intro h0
    have : a1 * (b1 + c1) + a2 * (b2 + c2) = 0 := by rw [as, h0]
    have hb : b1 ^ 2 + b2 ^ 2 = 0 := by linarith
    have hc : c1 ^ 2 + c2 ^ 2 = 0 := by linarith
    have q1 : b1 = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linarith only [hb, sq_nonneg b1, sq_nonneg b2])
    have q2 : b2 = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linarith only [hb, sq_nonneg b2, sq_nonneg b1])
    have q3 : c1 = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linarith only [hc, sq_nonneg c1, sq_nonneg c2])
    have q4 : c2 = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linarith only [hc, sq_nonneg c2, sq_nonneg c1])
    apply hd2; rw [q1, q2, q3, q4]; ring
  have lag : (a1 * (b1 + c1) + a2 * (b2 + c2)) ^ 2 + (a1 * (b2 + c2) - a2 * (b1 + c1)) ^ 2 =
      (a1 ^ 2 + a2 ^ 2) * ((b1 + c1) ^ 2 + (b2 + c2) ^ 2) := by ring
  rw [as, hx] at lag
  have hs : (b1 + c1) ^ 2 + (b2 + c2) ^ 2 = a1 ^ 2 + a2 ^ 2 := by
    have := mul_left_cancel₀ hρ (show (a1 ^ 2 + a2 ^ 2) * ((b1 + c1) ^ 2 + (b2 + c2) ^ 2) =
      (a1 ^ 2 + a2 ^ 2) * (a1 ^ 2 + a2 ^ 2) by linear_combination -lag)
    exact this
  linarith [hs, as, e1, e2, e3, e4]

lemma not_collinear_of_triangle (t : Affine.Triangle ℝ BlindPlane) :
    ¬ Collinear ℝ ({t.points 0, t.points 1, t.points 2} : Set BlindPlane) := by
  have : t.points = ![t.points 0, t.points 1, t.points 2] := by
    ext i : 1; fin_cases i <;> rfl
  have hi := t.independent
  rw [this] at hi
  exact affineIndependent_iff_not_collinear_set.mp hi

theorem rb_10 : real10_stmt → blind10_stmt := by
  intro h t Oa Ob Oc hnA hnB hnC hS hOa hOb hOc
  set A := t.points 0; set B := t.points 1; set C := t.points 2
  set O := t.circumcenter
  have dA : dist O A = t.circumradius := (dist_comm _ _).trans (t.dist_circumcenter_eq_circumradius 0)
  have dB : dist O B = t.circumradius := (dist_comm _ _).trans (t.dist_circumcenter_eq_circumradius 1)
  have dC : dist O C = t.circumradius := (dist_comm _ _).trans (t.dist_circumcenter_eq_circumradius 2)
  have hAB : A ≠ B := t.independent.injective.ne (by decide)
  have hBC : B ≠ C := t.independent.injective.ne (by decide)
  have hCA : C ≠ A := t.independent.injective.ne (by decide)
  have hS0 : dist A B ^ 2 + dist B C ^ 2 + dist C A ^ 2 ≠ 5 * dist O A ^ 2 := by rwa [dA]
  have hAOa : A ≠ Oa := by
    rintro rfl
    exact hS0 (sumSq_of_eq O A B C hBC (by rw [dA, dB]) (by rw [dA, dC])
      hOa.1 (hOa.1.trans hOa.2))
  have hBOb : B ≠ Ob := by
    rintro rfl
    have := sumSq_of_eq O B C A hCA (by rw [dB, dC]) (by rw [dB, dA])
      hOb.1 (hOb.1.trans hOb.2)
    apply hS0; rw [dA, ← dB, ← this, dist_comm A B]; ring
  have hCOc : C ≠ Oc := by
    rintro rfl
    have := sumSq_of_eq O C A B hAB (by rw [dC, dA]) (by rw [dC, dB])
      hOc.1 (hOc.1.trans hOc.2)
    apply hS0; rw [dA, ← dC, ← this]; ring
  have hOBC : ¬ Collinear ℝ ({O, B, C} : Set BlindPlane) := fun hc =>
    hnA ((collinear_iff_midpoint O B C hBC (dB.trans dC.symm)).mp hc)
  have hOCA : ¬ Collinear ℝ ({O, C, A} : Set BlindPlane) := fun hc =>
    hnB ((collinear_iff_midpoint O C A hCA (dC.trans dA.symm)).mp hc)
  have hOAB : ¬ Collinear ℝ ({O, A, B} : Set BlindPlane) := fun hc =>
    hnC ((collinear_iff_midpoint O A B hAB (dA.trans dB.symm)).mp hc)
  obtain ⟨P, h1, h2, h3⟩ := h A B C O Oa Ob Oc (not_collinear_of_triangle t)
    (dA.trans dB.symm) (dA.trans dC.symm) hOBC hOCA hOAB
    hOa.1 (hOa.1.trans hOa.2) hOb.1 (hOb.1.trans hOb.2) hOc.1 (hOc.1.trans hOc.2) hS0
  refine ⟨P, ?_, ?_, ?_⟩
  · exact h1.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAOa
  · exact h2.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBOb
  · exact h3.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hCOc

theorem br_10 : blind10_stmt → real10_stmt := by
  intro h A B C O Oa Ob Oc hABC hOA hOC hOBC hOCA hOAB hOa1 hOa2 hOb1 hOb2 hOc1 hOc2 hS
  let t : Affine.Triangle ℝ BlindPlane :=
    ⟨![A, B, C], affineIndependent_iff_not_collinear_set.mpr hABC⟩
  have hspan : affineSpan ℝ (Set.range t.points) = ⊤ := by
    rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp
  have hO : O = t.circumcenter := by
    apply t.eq_circumcenter_of_dist_eq (r := dist O A)
      (by rw [hspan]; exact AffineSubspace.mem_top _ _ _)
    intro i; fin_cases i
    · simp [t, dist_comm]
    · simp [t, dist_comm, hOA]; rw [dist_comm, ← hOA, dist_comm]
    · simp [t, dist_comm, hOC]; rw [dist_comm, ← hOC, dist_comm]
  have hR : t.circumradius = dist O A := by
    rw [← t.dist_circumcenter_eq_circumradius 0, ← hO, dist_comm]; rfl
  have hAB : A ≠ B := fun e => hABC (by rw [e]; simp [collinear_pair])
  have hBC : B ≠ C := fun e => hABC (by rw [e]; simp [collinear_pair])
  have hCA : C ≠ A := fun e => hABC (by rw [e]; simp [collinear_pair])
  have hmid : ∀ X Y : BlindPlane, X ≠ Y → dist O X = dist O Y →
      ¬ Collinear ℝ ({O, X, Y} : Set BlindPlane) → O ≠ midpoint ℝ X Y :=
    fun X Y hXY hd hc e => hc ((collinear_iff_midpoint O X Y hXY hd).mpr e)
  obtain ⟨X, h1, h2, h3⟩ := h t Oa Ob Oc
    (by rw [← hO]; exact hmid B C hBC (hOA.symm.trans hOC) hOBC)
    (by rw [← hO]; exact hmid C A hCA hOC.symm hOCA)
    (by rw [← hO]; exact hmid A B hAB hOA hOAB)
    (by rw [hR]; exact hS)
    (by rw [← hO]; exact ⟨hOa1, hOa1.symm.trans hOa2⟩)
    (by rw [← hO]; exact ⟨hOb1, hOb1.symm.trans hOb2⟩)
    (by rw [← hO]; exact ⟨hOc1, hOc1.symm.trans hOc2⟩)
  exact ⟨X, collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair _ _ _)
      (right_mem_affineSpan_pair _ _ _) h1,
    collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair _ _ _)
      (right_mem_affineSpan_pair _ _ _) h2,
    collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair _ _ _)
      (right_mem_affineSpan_pair _ _ _) h3⟩
