import scratch.BridgeBlind
import Clifford.Bridge
import Clifford.BridgeL10

set_option maxHeartbeats 5000000

/-!
# Direct construction of the writer's all-n Clifford statement

Stage A: the level-3 object for three circles in `BlindGenPos`.
Stage B: the level-4 point in the nondegenerate (all triples `GenTriple`) case.
-/

open OnePoint
open Complex ComplexConjugate
open PaperLBlind BlindCompareFull
open EuclideanGeometry

noncomputable section

namespace BlindChain

/-- If three centres are collinear and distinct, the three circles through `0` have the same
second intersection. -/
lemma second_eq_of_collinear {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hcol : Collinear ℝ ({a, b, c} : Set ℂ)) :
    Clifford.second a b = Clifford.second a c := by
  have hw : conj (b - a) * (c - a) = (b - a) * conj (c - a) :=
    Clifford.collinear_iff_conj_mul a b c |>.1 hcol
  let w : ℂ := (c - a) / (b - a)
  have hwr : conj w = w := by
    dsimp [w]
    rw [map_div₀]
    rw [div_eq_div_iff ((map_ne_zero conj).2 (sub_ne_zero.2 (Ne.symm hab)))
      (sub_ne_zero.2 (Ne.symm hab))]
    simp only [map_sub] at hw ⊢
    linear_combination -hw
  obtain ⟨t, ht⟩ : ∃ t : ℝ, w = (t : ℂ) := Complex.conj_eq_iff_real.1 hwr
  have hc_eq : c = a + (t : ℂ) * (b - a) := by
    rw [← ht]
    simp [w]
    field_simp [sub_ne_zero.2 (Ne.symm hab)]
    ring
  have ht0 : (t : ℂ) ≠ 0 := by
    intro h0
    apply hac
    rw [hc_eq, h0]
    simp
  have hden : conj a - conj (a + (t : ℂ) * (b - a)) ≠ 0 := by
    simp only [map_add, map_mul, Complex.conj_ofReal]
    rw [show conj a - (conj a + (t : ℂ) * conj (b - a)) = -(t : ℂ) * conj (b - a) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr ht0) ((map_ne_zero conj).2 (sub_ne_zero.2 (Ne.symm hab)))
  rw [hc_eq]
  unfold Clifford.second
  field_simp [hden, Clifford.conj_sub_ne_zero hab]
  simp only [map_add, map_sub, map_mul, Complex.conj_ofReal]
  ring

/-- Level 3: the three second intersections are distinct, hence lie on a generalized circle in
the writer's sense, whether the three are cospherical or collinear. -/
lemma blindChain_three {c : Fin 3 → ℂ} (hc : BlindGenPos c) :
    ∃ Y : Set BlindS, BlindCliffordP false 3 c Y := by
  let p01 : ℂ := Clifford.second (c 0) (c 1)
  let p02 : ℂ := Clifford.second (c 0) (c 2)
  let p12 : ℂ := Clifford.second (c 1) (c 2)
  have ht01 : Clifford.Transversal (c 0) (c 1) := blindTransversal_iff.1 (hc.1 0 1 (by decide))
  have ht02 : Clifford.Transversal (c 0) (c 2) := blindTransversal_iff.1 (hc.1 0 2 (by decide))
  have ht12 : Clifford.Transversal (c 1) (c 2) := blindTransversal_iff.1 (hc.1 1 2 (by decide))
  have he01_02 : p01 ≠ p02 := by
    have h := (hc.2 0 1 2 (by decide) (by decide) (by decide)).2.1
    simpa [p01, p02, BlindSecond_eq ht01, BlindSecond_eq ht02] using h
  obtain ⟨X, hX, hsub⟩ :=
    Clifford.exists_gcircle (Clifford.cospherical_or_collinear p01 p02 p12)
  have hp01mem : p01 ∈ X := hsub (by simp)
  have hp02mem : p02 ∈ X := hsub (by simp)
  have hp12mem : p12 ∈ X := hsub (by simp)
  obtain ⟨Y, hYgc, hmemY⟩ :=
    blindIsGCircle_of_isGCircle_of_two hX hp01mem hp02mem he01_02
  refine ⟨Y, ?_⟩
  rw [BlindCliffordP, if_pos (by decide : Odd 3)]
  simp only [Bool.false_eq_true, false_implies, true_and]
  refine ⟨hYgc, ?_⟩
  intro i
  fin_cases i
  · refine ⟨(p12 : BlindS), ?_, ?_⟩
    · simpa [BlindCliffordP, BlindDelete, Fin.succAbove, Fin.succAbove, p12, BlindSecond_eq ht12]
    · exact hmemY p12 hp12mem
  · refine ⟨(p02 : BlindS), ?_, ?_⟩
    · simpa [BlindCliffordP, BlindDelete, Fin.succAbove, Fin.succAbove, p02, BlindSecond_eq ht02]
    · exact hmemY p02 hp02mem
  · refine ⟨(p01 : BlindS), ?_, ?_⟩
    · simpa [BlindCliffordP, BlindDelete, Fin.succAbove, Fin.succAbove, p01, BlindSecond_eq ht01]
    · exact hmemY p01 hp01mem

/-- Pairwise transversality plus distinct blind second points forces the three centres to be
non-collinear: collinear centres give one common second intersection. -/
lemma noncollinear_centres_of_blind {a b c : ℂ}
    (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
    (hne : BlindSecond a b ≠ BlindSecond a c) :
    ¬ Collinear ℝ ({a, b, c} : Set ℂ) := by
  intro hcol
  apply hne
  rw [BlindSecond_eq hab, BlindSecond_eq hac]
  exact second_eq_of_collinear hab.ne hac.ne hcol

/-- Under `BlindGenPos`, a triple with non-collinear second intersections is a library
`GenTriple`. -/
lemma genTriple_of_blind {a b c : ℂ}
    (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
    (hbc : Clifford.Transversal b c)
    (hne : BlindSecond a b ≠ BlindSecond a c)
    (hsec : ¬ Collinear ℝ ({Clifford.second a b, Clifford.second a c,
      Clifford.second b c} : Set ℂ)) :
    Clifford.GenTriple a b c := by
  apply (Clifford.genTriple_iff hab hac hbc).2
  exact ⟨noncollinear_centres_of_blind hab hac hne, hsec⟩

/-- A `GenPos4` quadruple gives `GenPosN` on every deleted triple. -/
lemma genPosN_three_of_genPos4 {c : Fin 4 → ℂ} (hc : BlindGenPos c)
    (h : Clifford.GenPos4 (c 0) (c 1) (c 2) (c 3)) (i : Fin 4) :
    Clifford.GenPosN (c ∘ i.succAbove) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply blindTransversal_iff.1
    apply hc.1 (i.succAbove a) (i.succAbove b)
    intro heq
    exact hab ((Fin.succAboveEmb i).injective heq)
  · intro a b d hab hbd
    fin_cases i <;>
      fin_cases a <;> fin_cases b <;> fin_cases d <;>
      simp at hab hbd ⊢ <;>
      first | exact h.bcd | exact h.acd | exact h.abd | exact h.abc

/-- `BlindGenPos` plus non-collinearity of every triple of second points gives the library's
`GenPos4`. -/
lemma genPos4_of_blindGenPos {c : Fin 4 → ℂ} (hc : BlindGenPos c)
    (h012 : ¬ Collinear ℝ ({Clifford.second (c 0) (c 1), Clifford.second (c 0) (c 2),
      Clifford.second (c 1) (c 2)} : Set ℂ))
    (h013 : ¬ Collinear ℝ ({Clifford.second (c 0) (c 1), Clifford.second (c 0) (c 3),
      Clifford.second (c 1) (c 3)} : Set ℂ))
    (h023 : ¬ Collinear ℝ ({Clifford.second (c 0) (c 2), Clifford.second (c 0) (c 3),
      Clifford.second (c 2) (c 3)} : Set ℂ))
    (h123 : ¬ Collinear ℝ ({Clifford.second (c 1) (c 2), Clifford.second (c 1) (c 3),
      Clifford.second (c 2) (c 3)} : Set ℂ)) :
    Clifford.GenPos4 (c 0) (c 1) (c 2) (c 3) := by
  let t01 : Clifford.Transversal (c 0) (c 1) := blindTransversal_iff.1 (hc.1 0 1 (by decide))
  let t02 : Clifford.Transversal (c 0) (c 2) := blindTransversal_iff.1 (hc.1 0 2 (by decide))
  let t03 : Clifford.Transversal (c 0) (c 3) := blindTransversal_iff.1 (hc.1 0 3 (by decide))
  let t12 : Clifford.Transversal (c 1) (c 2) := blindTransversal_iff.1 (hc.1 1 2 (by decide))
  let t13 : Clifford.Transversal (c 1) (c 3) := blindTransversal_iff.1 (hc.1 1 3 (by decide))
  let t23 : Clifford.Transversal (c 2) (c 3) := blindTransversal_iff.1 (hc.1 2 3 (by decide))
  refine ⟨t01, t02, t03, t12, t13, t23, ?_, ?_, ?_, ?_⟩
  · exact genTriple_of_blind t01 t02 t12
      ((hc.2 0 1 2 (by decide) (by decide) (by decide)).2.1) h012
  · exact genTriple_of_blind t01 t03 t13
      ((hc.2 0 1 3 (by decide) (by decide) (by decide)).2.1) h013
  · exact genTriple_of_blind t02 t03 t23
      ((hc.2 0 2 3 (by decide) (by decide) (by decide)).2.1) h023
  · exact genTriple_of_blind t12 t13 t23
      ((hc.2 1 2 3 (by decide) (by decide) (by decide)).2.1) h123

/-- The constant coefficient of the circle equation of a transversal triple is nonzero. -/
lemma gq0_ne_zero_of_transversal {a b c : ℂ}
    (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
    (hbc : Clifford.Transversal b c) :
    Clifford.gq0 a b c (conj a) (conj b) (conj c) ≠ 0 := by
  have heq : Clifford.gq0 a b c (conj a) (conj b) (conj c) =
      - (Clifford.crs a b (conj a) (conj b) * Clifford.crs a c (conj a) (conj c) *
        Clifford.crs b c (conj b) (conj c)) := by
    unfold Clifford.gq0 Clifford.det3 Clifford.crs
    ring
  rw [heq]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac))
    (sub_ne_zero.mpr hbc))

/-- Degenerate level 4: when `cycP` of a triple vanishes, the Miquel point and the three second
intersections of that triple lie on a generalized circle. -/
lemma degenerate_gcircle_of_cycP_zero {a b c d : ℂ}
    (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
    (had : Clifford.Transversal a d) (hbc : Clifford.Transversal b c)
    (hbd : Clifford.Transversal b d) (hcd : Clifford.Transversal c d)
    (hcyc : Clifford.cycP a b c (conj a) (conj b) (conj c) = 0)
    (hD : Clifford.mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0) :
    Cospherical ({Clifford.second a b, Clifford.second a c, Clifford.second b c,
      Clifford.miquel a b c d} : Set ℂ) ∨
    Collinear ℝ ({Clifford.second a b, Clifford.second a c, Clifford.second b c,
      Clifford.miquel a b c d} : Set ℂ) := by
  let g0 := Clifford.gq0 a b c (conj a) (conj b) (conj c)
  let g1 := Clifford.gq1 a b c (conj a) (conj b) (conj c)
  let g2 := Clifford.gq2 a b c (conj a) (conj b) (conj c)
  let q := Clifford.miquel a b c d
  have hDb : Clifford.mD (conj a) (conj b) (conj c) (conj d) a b c d ≠ 0 := by
    rw [← Clifford.conj_mD]
    exact (map_ne_zero _).2 hD
  have hGab : g0 - Clifford.second a b * g1 - conj (Clifford.second a b) * g2 = 0 := by
    have h := Clifford.second_on hab.ne (Clifford.gq_P12 a b c (conj a) (conj b) (conj c))
    simpa [g0, g1, g2, hcyc] using h
  have hGac : g0 - Clifford.second a c * g1 - conj (Clifford.second a c) * g2 = 0 := by
    have h := Clifford.second_on hac.ne (Clifford.gq_P13 a b c (conj a) (conj b) (conj c))
    simpa [g0, g1, g2, hcyc] using h
  have hGbc : g0 - Clifford.second b c * g1 - conj (Clifford.second b c) * g2 = 0 := by
    have h := Clifford.second_on hbc.ne (Clifford.gq_P23 a b c (conj a) (conj b) (conj c))
    simpa [g0, g1, g2, hcyc] using h
  have hGq : g0 - q * g1 - conj q * g2 = 0 := by
    dsimp [q]
    rw [Clifford.conj_miquel]
    have h := Clifford.ratio_on hD hDb
      (Clifford.certA₁ a b c d (conj a) (conj b) (conj c) (conj d))
      (Clifford.certA₂ a b c d (conj a) (conj b) (conj c) (conj d))
    simpa [g0, g1, g2, hcyc, Clifford.miquel] using h
  have hg0c : conj g0 = -g0 := by
    dsimp [g0]
    rw [Clifford.map_gq0, Clifford.gq0_swap]
    simp only [starRingEnd_self_apply]
  have hg2c : conj g2 = -g1 := by
    dsimp [g1, g2]
    rw [Clifford.map_gq2, Clifford.gq2_swap]
    simp only [starRingEnd_self_apply]
  have hg0ne : g0 ≠ 0 := by
    dsimp [g0]
    exact gq0_ne_zero_of_transversal hab hac hbc
  have hg0re : g0.re = 0 := by
    have h := congrArg Complex.re hg0c
    simp only [Complex.conj_re, Complex.neg_re] at h
    linarith
  have hg2re : g2.re = -g1.re := by
    have h := congrArg Complex.re hg2c
    simp only [Complex.conj_re, Complex.neg_re] at h
    linarith
  have hg2im : g2.im = g1.im := by
    have h := congrArg Complex.im hg2c
    simp only [Complex.conj_im, Complex.neg_im] at h
    linarith
  have hg0im : g0.im ≠ 0 := by
    intro h0
    apply hg0ne
    apply Complex.ext <;> simp [hg0re, h0]
  let B : ℝ := -2 * g1.im
  let C : ℝ := -2 * g1.re
  let D : ℝ := g0.im
  have hnon : ¬ ((0 : ℝ) = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0) := by
    rintro ⟨-, -, -, hD0⟩
    exact hg0im (by simpa [D] using hD0)
  have hReal : ∀ z : ℂ, g0 - z * g1 - conj z * g2 = 0 → B * z.re + C * z.im + D = 0 := by
    intro z hz
    have hi := congrArg Complex.im hz
    simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im] at hi
    rw [hg2re, hg2im] at hi
    simp at hi
    dsimp [B, C, D]
    linear_combination hi
  refine Clifford.cospherical_or_collinear_of_eqn 0 B C D hnon
    (Clifford.second a b) (by simp) ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · simpa using hReal (Clifford.second a b) hGab
  · simpa using hReal (Clifford.second a c) hGac
  · simpa using hReal (Clifford.second b c) hGbc
  · simpa [q] using hReal q hGq

/-- Two vanishing `cycP`s sharing a transversal pair force the other two to vanish. -/
lemma cycP_all_zero_of_two {a b c d : ℂ}
    (hab : Clifford.Transversal a b)
    (h1 : Clifford.cycP a b c (conj a) (conj b) (conj c) = 0)
    (h2 : Clifford.cycP a b d (conj a) (conj b) (conj d) = 0) :
    Clifford.cycP a c d (conj a) (conj c) (conj d) = 0 ∧
    Clifford.cycP b c d (conj b) (conj c) (conj d) = 0 := by
  have hid1 : Clifford.crs a b (conj a) (conj b) *
      Clifford.cycP a c d (conj a) (conj c) (conj d) =
      - Clifford.crs a d (conj a) (conj d) *
          Clifford.cycP a b c (conj a) (conj b) (conj c) +
        Clifford.crs a c (conj a) (conj c) *
          Clifford.cycP a b d (conj a) (conj b) (conj d) := by
    unfold Clifford.crs Clifford.cycP Clifford.det3
    ring
  have hid2 : Clifford.crs a b (conj a) (conj b) *
      Clifford.cycP b c d (conj b) (conj c) (conj d) =
      - Clifford.crs b d (conj b) (conj d) *
          Clifford.cycP a b c (conj a) (conj b) (conj c) +
        Clifford.crs b c (conj b) (conj c) *
          Clifford.cycP a b d (conj a) (conj b) (conj d) := by
    unfold Clifford.crs Clifford.cycP Clifford.det3
    ring
  have hz1 : Clifford.crs a b (conj a) (conj b) *
      Clifford.cycP a c d (conj a) (conj c) (conj d) = 0 := by
    rw [hid1, h1, h2]
    ring
  have hz2 : Clifford.crs a b (conj a) (conj b) *
      Clifford.cycP b c d (conj b) (conj c) (conj d) = 0 := by
    rw [hid2, h1, h2]
    ring
  exact ⟨(mul_eq_zero.mp hz1).resolve_left (sub_ne_zero.mpr hab),
    (mul_eq_zero.mp hz2).resolve_left (sub_ne_zero.mpr hab)⟩

/-- Any two degenerate triples of a transversal quadruple force all four to be degenerate. -/
lemma all_collinear_of_two_degenerate {a b c d : ℂ}
    (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
    (had : Clifford.Transversal a d) (hbc : Clifford.Transversal b c)
    (hbd : Clifford.Transversal b d) (hcd : Clifford.Transversal c d)
    (hnabc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hnabd : ¬ Collinear ℝ ({a, b, d} : Set ℂ))
    (hnacd : ¬ Collinear ℝ ({a, c, d} : Set ℂ))
    (hnbcd : ¬ Collinear ℝ ({b, c, d} : Set ℂ))
    (h1 : Collinear ℝ ({Clifford.second a b, Clifford.second a c,
      Clifford.second b c} : Set ℂ))
    (h2 : Collinear ℝ ({Clifford.second a b, Clifford.second a d,
      Clifford.second b d} : Set ℂ)) :
    Collinear ℝ ({Clifford.second a c, Clifford.second a d,
      Clifford.second c d} : Set ℂ) ∧
    Collinear ℝ ({Clifford.second b c, Clifford.second b d,
      Clifford.second c d} : Set ℂ) := by
  have hcyc1 : Clifford.cycP a b c (conj a) (conj b) (conj c) = 0 := by
    by_contra hn
    exact ((Clifford.cycP_ne_zero_iff hab hac hbc hnabc).1 hn) h1
  have hcyc2 : Clifford.cycP a b d (conj a) (conj b) (conj d) = 0 := by
    by_contra hn
    exact ((Clifford.cycP_ne_zero_iff hab had hbd hnabd).1 hn) h2
  obtain ⟨hcyc3, hcyc4⟩ := cycP_all_zero_of_two hab hcyc1 hcyc2
  constructor
  · by_contra hn
    exact ((Clifford.cycP_ne_zero_iff hac had hcd hnacd).2 hn) hcyc3
  · by_contra hn
    exact ((Clifford.cycP_ne_zero_iff hbc hbd hcd hnbcd).2 hn) hcyc4

/-- The second intersection point is symmetric in its two centres. -/
lemma blind_second_symm (a b : ℂ) : Clifford.second b a = Clifford.second a b := by
  unfold Clifford.second
  rw [show conj b - conj a = -(conj a - conj b) by ring]
  rw [div_neg]
  ring

/-- Two degenerate triples sharing a pair give all four degenerate triples. -/
lemma all_four_collinear_of_two_degenerate {a b c d : ℂ}
    (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
    (had : Clifford.Transversal a d) (hbc : Clifford.Transversal b c)
    (hbd : Clifford.Transversal b d) (hcd : Clifford.Transversal c d)
    (hnabc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hnabd : ¬ Collinear ℝ ({a, b, d} : Set ℂ))
    (hnacd : ¬ Collinear ℝ ({a, c, d} : Set ℂ))
    (hnbcd : ¬ Collinear ℝ ({b, c, d} : Set ℂ))
    (h1 : Collinear ℝ ({Clifford.second a b, Clifford.second a c,
      Clifford.second b c} : Set ℂ))
    (h2 : Collinear ℝ ({Clifford.second a b, Clifford.second a d,
      Clifford.second b d} : Set ℂ)) :
    Collinear ℝ ({Clifford.second a b, Clifford.second a c, Clifford.second b c} : Set ℂ) ∧
    Collinear ℝ ({Clifford.second a b, Clifford.second a d, Clifford.second b d} : Set ℂ) ∧
    Collinear ℝ ({Clifford.second a c, Clifford.second a d, Clifford.second c d} : Set ℂ) ∧
    Collinear ℝ ({Clifford.second b c, Clifford.second b d, Clifford.second c d} : Set ℂ) := by
  obtain ⟨h3, h4⟩ := all_collinear_of_two_degenerate hab hac had hbc hbd hcd
    hnabc hnabd hnacd hnbcd h1 h2
  exact ⟨h1, h2, h3, h4⟩

/-- `BlindGenPos` restricts to every deleted subfamily. -/
lemma blindGenPos_succAbove {m : ℕ} {c : Fin (m + 1) → ℂ} (hc : BlindGenPos c)
    (i : Fin (m + 1)) : BlindGenPos (c ∘ i.succAbove) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    exact hc.1 (i.succAbove a) (i.succAbove b)
      (fun heq => hab ((Fin.succAboveEmb i).injective heq))
  · intro a b d hab hbd hbc
    simpa using hc.2 (i.succAbove a) (i.succAbove b) (i.succAbove d)
      (fun heq => hab ((Fin.succAboveEmb i).injective heq))
      (fun heq => hbd ((Fin.succAboveEmb i).injective heq))
      (fun heq => hbc ((Fin.succAboveEmb i).injective heq))

/-- Level 3 of a triple whose second points and the extra point lie on one generalized circle. -/
lemma blindChain_three_of_gcircle {d : Fin 3 → ℂ} (hd : BlindGenPos d) {q : ℂ}
    (hg : Cospherical ({Clifford.second (d 0) (d 1), Clifford.second (d 0) (d 2),
      Clifford.second (d 1) (d 2), q} : Set ℂ) ∨
      Collinear ℝ ({Clifford.second (d 0) (d 1), Clifford.second (d 0) (d 2),
      Clifford.second (d 1) (d 2), q} : Set ℂ)) :
    ∃ Y : Set BlindS, BlindCliffordP false 3 d Y ∧ BlindIsGCircle Y ∧ (q : BlindS) ∈ Y := by
  let p01 : ℂ := Clifford.second (d 0) (d 1)
  let p02 : ℂ := Clifford.second (d 0) (d 2)
  let p12 : ℂ := Clifford.second (d 1) (d 2)
  have ht01 : Clifford.Transversal (d 0) (d 1) := blindTransversal_iff.1 (hd.1 0 1 (by decide))
  have ht02 : Clifford.Transversal (d 0) (d 2) := blindTransversal_iff.1 (hd.1 0 2 (by decide))
  have ht12 : Clifford.Transversal (d 1) (d 2) := blindTransversal_iff.1 (hd.1 1 2 (by decide))
  have he01_02 : p01 ≠ p02 := by
    have h := (hd.2 0 1 2 (by decide) (by decide) (by decide)).2.1
    simpa [p01, p02, BlindSecond_eq ht01, BlindSecond_eq ht02] using h
  obtain ⟨X, hX, hsub⟩ := Clifford.exists_gcircle hg
  have hp01X : p01 ∈ X := by apply hsub; simp [p01]
  have hp02X : p02 ∈ X := by apply hsub; simp [p02]
  have hp12X : p12 ∈ X := by apply hsub; simp [p12]
  have hqX : q ∈ X := by apply hsub; simp
  obtain ⟨Y, hYgc, hmemY⟩ :=
    blindIsGCircle_of_isGCircle_of_two hX hp01X hp02X he01_02
  refine ⟨Y, ?_, hYgc, hmemY q hqX⟩
  rw [BlindCliffordP, if_pos (by decide : Odd 3)]
  simp only [Bool.false_eq_true, false_implies, true_and]
  refine ⟨hYgc, ?_⟩
  intro i
  fin_cases i
  · refine ⟨(p12 : BlindS), ?_, ?_⟩
    · simpa [BlindCliffordP, BlindDelete, Fin.succAbove, Fin.succAbove, p12, BlindSecond_eq ht12]
    · exact hmemY p12 hp12X
  · refine ⟨(p02 : BlindS), ?_, ?_⟩
    · simpa [BlindCliffordP, BlindDelete, Fin.succAbove, Fin.succAbove, p02, BlindSecond_eq ht02]
    · exact hmemY p02 hp02X
  · refine ⟨(p01 : BlindS), ?_, ?_⟩
    · simpa [BlindCliffordP, BlindDelete, Fin.succAbove, Fin.succAbove, p01, BlindSecond_eq ht01]
    · exact hmemY p01 hp01X

/-- Level 3 of a triple of collinear second points, with infinity on the object. -/
lemma blindChain_three_of_collinear {d : Fin 3 → ℂ} (hd : BlindGenPos d)
    (hcol : Collinear ℝ ({Clifford.second (d 0) (d 1), Clifford.second (d 0) (d 2),
      Clifford.second (d 1) (d 2)} : Set ℂ)) :
    ∃ Y : Set BlindS, BlindCliffordP false 3 d Y ∧ BlindIsGCircle Y ∧ ∞ ∈ Y := by
  let p01 : ℂ := Clifford.second (d 0) (d 1)
  let p02 : ℂ := Clifford.second (d 0) (d 2)
  let p12 : ℂ := Clifford.second (d 1) (d 2)
  have ht01 : Clifford.Transversal (d 0) (d 1) := blindTransversal_iff.1 (hd.1 0 1 (by decide))
  have ht02 : Clifford.Transversal (d 0) (d 2) := blindTransversal_iff.1 (hd.1 0 2 (by decide))
  have ht12 : Clifford.Transversal (d 1) (d 2) := blindTransversal_iff.1 (hd.1 1 2 (by decide))
  have he01_02 : p01 ≠ p02 := by
    have h := (hd.2 0 1 2 (by decide) (by decide) (by decide)).2.1
    simpa [p01, p02, BlindSecond_eq ht01, BlindSecond_eq ht02] using h
  obtain ⟨p, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).1 hcol
  have hv0 : v ≠ 0 := by
    intro hvz
    rcases hv p01 (by simp [p01]) with ⟨r, hr⟩
    rcases hv p02 (by simp [p02]) with ⟨s, hs⟩
    have hp1 : p01 = p := by simpa [hvz] using hr
    have hp2 : p02 = p := by simpa [hvz] using hs
    exact he01_02 (hp1.trans hp2.symm)
  let Y : Set BlindS := Clifford.lineS p v
  have hp01Y : (p01 : BlindS) ∈ Y := by
    rcases hv p01 (by simp [p01]) with ⟨r, hr⟩
    exact Or.inr ⟨p01, ⟨r, by simpa [vadd_eq_add, add_comm] using hr⟩, rfl⟩
  have hp02Y : (p02 : BlindS) ∈ Y := by
    rcases hv p02 (by simp [p02]) with ⟨r, hr⟩
    exact Or.inr ⟨p02, ⟨r, by simpa [vadd_eq_add, add_comm] using hr⟩, rfl⟩
  have hp12Y : (p12 : BlindS) ∈ Y := by
    rcases hv p12 (by simp [p12]) with ⟨r, hr⟩
    exact Or.inr ⟨p12, ⟨r, by simpa [vadd_eq_add, add_comm] using hr⟩, rfl⟩
  refine ⟨Y, ?_, blindIsGCircle_lineS p v hv0, ?_⟩
  · rw [BlindCliffordP, if_pos (by decide : Odd 3)]
    simp only [Bool.false_eq_true, false_implies, true_and]
    refine ⟨blindIsGCircle_lineS p v hv0, ?_⟩
    intro i
    fin_cases i
    · refine ⟨(p12 : BlindS), ?_, hp12Y⟩
      simpa [BlindCliffordP, BlindDelete, Fin.succAbove, Fin.succAbove, p12, BlindSecond_eq ht12]
    · refine ⟨(p02 : BlindS), ?_, hp02Y⟩
      simpa [BlindCliffordP, BlindDelete, Fin.succAbove, Fin.succAbove, p02, BlindSecond_eq ht02]
    · refine ⟨(p01 : BlindS), ?_, hp01Y⟩
      simpa [BlindCliffordP, BlindDelete, Fin.succAbove, Fin.succAbove, p01, BlindSecond_eq ht01]
  · simp [Y, Clifford.lineS]

/-- Stage B, nondegenerate case: the level-4 point is the Miquel point, and the four level-3
objects are transported from the library. -/
lemma blindChain_four_of_genPos4 {c : Fin 4 → ℂ} (hc : BlindGenPos c)
    (hpos : Clifford.GenPos4 (c 0) (c 1) (c 2) (c 3)) :
    ∃ p : BlindS, BlindCliffordP false 4 c {p} := by
  have _ := hc
  let q : ℂ := Clifford.miquel (c 0) (c 1) (c 2) (c 3)
  have hchain : Clifford.ChainS 4 c {(q : BlindS)} := by
    simpa [q] using Clifford.chain4_ofS c hpos
  have hchildren : ∀ i : Fin 4, ∃ Y : Set BlindS,
      Clifford.ChainS 3 (c ∘ i.succAbove) Y ∧ (q : BlindS) ∈ Y := by
    simpa [Clifford.ChainS] using hchain
  refine ⟨(q : BlindS), ?_⟩
  rw [BlindCliffordP, if_neg (by decide : ¬ Odd 4)]
  simp only [Bool.false_eq_true, false_implies, true_and]
  refine ⟨(q : BlindS), rfl, ?_⟩
  intro i
  rcases hchildren i with ⟨Y, hYchain, hqY⟩
  have hYblind := blindCliffordP3_of_chainS (genPosN_three_of_genPos4 hc hpos i) hYchain
  have hYgc : BlindIsGCircle Y := by
    have htmp := hYblind
    rw [BlindCliffordP, if_pos (by decide : Odd 3)] at htmp
    have hmem3 : BlindIsGCircle Y ∧ ∀ j : Fin 3, ∃ q : BlindS,
        BlindCliffordP false 2 (BlindDelete (c ∘ i.succAbove) j) {q} ∧ q ∈ Y := by
      simpa only [Bool.false_eq_true, false_implies, implies_true, true_and] using htmp
    exact hmem3.1
  exact ⟨Y, hYblind, hYgc, hqY⟩

/-- With exactly one degenerate triple, the Miquel point lies on a generalized circle through
each of the four triples of second intersections. -/
lemma miquel_gcircles_of_one_degenerate {a b c d : ℂ}
    (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
    (had : Clifford.Transversal a d) (hbc : Clifford.Transversal b c)
    (hbd : Clifford.Transversal b d) (hcd : Clifford.Transversal c d)
    (hnabc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hnabd : ¬ Collinear ℝ ({a, b, d} : Set ℂ))
    (hnacd : ¬ Collinear ℝ ({a, c, d} : Set ℂ))
    (hnbcd : ¬ Collinear ℝ ({b, c, d} : Set ℂ))
    (hbsab_ac : BlindSecond a b ≠ BlindSecond a c)
    (hbsab_ad : BlindSecond a b ≠ BlindSecond a d)
    (hbsac_ad : BlindSecond a c ≠ BlindSecond a d)
    (hbsbc_bd : BlindSecond b c ≠ BlindSecond b d)
    (hcolabc : Collinear ℝ ({Clifford.second a b, Clifford.second a c,
      Clifford.second b c} : Set ℂ))
    (hncolabd : ¬ Collinear ℝ ({Clifford.second a b, Clifford.second a d,
      Clifford.second b d} : Set ℂ))
    (hncolacd : ¬ Collinear ℝ ({Clifford.second a c, Clifford.second a d,
      Clifford.second c d} : Set ℂ))
    (hncolbcd : ¬ Collinear ℝ ({Clifford.second b c, Clifford.second b d,
      Clifford.second c d} : Set ℂ)) :
    ∃ q : ℂ,
      (Cospherical ({Clifford.second a b, Clifford.second a c, Clifford.second b c, q} : Set ℂ) ∨
        Collinear ℝ ({Clifford.second a b, Clifford.second a c, Clifford.second b c, q} : Set ℂ)) ∧
      (Cospherical ({Clifford.second a b, Clifford.second a d, Clifford.second b d, q} : Set ℂ) ∨
        Collinear ℝ ({Clifford.second a b, Clifford.second a d, Clifford.second b d, q} : Set ℂ)) ∧
      (Cospherical ({Clifford.second a c, Clifford.second a d, Clifford.second c d, q} : Set ℂ) ∨
        Collinear ℝ ({Clifford.second a c, Clifford.second a d, Clifford.second c d, q} : Set ℂ)) ∧
      (Cospherical ({Clifford.second b c, Clifford.second b d, Clifford.second c d, q} : Set ℂ) ∨
        Collinear ℝ ({Clifford.second b c, Clifford.second b d, Clifford.second c d, q} : Set ℂ)) := by
  let genabd : Clifford.GenTriple a b d :=
    genTriple_of_blind hab had hbd hbsab_ad hncolabd
  let genacd : Clifford.GenTriple a c d :=
    genTriple_of_blind hac had hcd hbsac_ad hncolacd
  let genbcd : Clifford.GenTriple b c d :=
    genTriple_of_blind hbc hbd hcd hbsbc_bd hncolbcd
  have hDabd' : Clifford.mD a b d c (conj a) (conj b) (conj d) (conj c) ≠ 0 :=
    Clifford.mD_ne_zero hab had hbd hac hbc (Clifford.cd_symm hcd) genabd
  have hDabd : Clifford.mD a b d c (conj a) (conj b) (conj d) (conj c) ≠ 0 := hDabd'
  have hDabc : Clifford.mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0 := by
    intro h
    apply hDabd'
    rw [Clifford.mD_p1243, h, neg_zero]
  have hcycabc : Clifford.cycP a b c (conj a) (conj b) (conj c) = 0 := by
    by_contra hn
    exact ((Clifford.cycP_ne_zero_iff hab hac hbc hnabc).1 hn) hcolabc
  let q : ℂ := Clifford.miquel a b c d
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact degenerate_gcircle_of_cycP_zero hab hac had hbc hbd hcd hcycabc hDabc
  · have h := Clifford.gamma_cospherical hab had hbd genabd hDabd
    exact Or.inl (by simpa [q, Clifford.miquel_p1243] using h)
  · have hDacd : Clifford.mD a c d b (conj a) (conj c) (conj d) (conj b) ≠ 0 :=
      Clifford.mD_ne_zero hac had hcd hab (Clifford.cd_symm hbc) (Clifford.cd_symm hbd) genacd
    have h := Clifford.gamma_cospherical hac had hcd genacd hDacd
    exact Or.inl (by simpa [q, Clifford.miquel_p1342] using h)
  · have hDbcd : Clifford.mD b c d a (conj b) (conj c) (conj d) (conj a) ≠ 0 :=
      Clifford.mD_ne_zero hbc hbd hcd (Clifford.cd_symm hab) (Clifford.cd_symm hac)
        (Clifford.cd_symm had) genbcd
    have h := Clifford.gamma_cospherical hbc hbd hcd genbcd hDbcd
    exact Or.inl (by simpa [q, Clifford.miquel_p2341] using h)

/-- Stage B. The generic branch, the mixed-degenerate branch and the all-degenerate branch
(`∞` is on every line) together prove the level-4 statement. -/
lemma blindChain_four {c : Fin 4 → ℂ} (hc : BlindGenPos c) :
    ∃ p : BlindS, BlindCliffordP false 4 c {p} := by
  let p01 : ℂ := Clifford.second (c 0) (c 1)
  let p02 : ℂ := Clifford.second (c 0) (c 2)
  let p03 : ℂ := Clifford.second (c 0) (c 3)
  let p12 : ℂ := Clifford.second (c 1) (c 2)
  let p13 : ℂ := Clifford.second (c 1) (c 3)
  let p23 : ℂ := Clifford.second (c 2) (c 3)
  have set4_eq_of_mem {α : Type} [DecidableEq α] {a b c d e f g h : α}
      (he : e ∈ ({a, b, c, d} : Set α)) (hf : f ∈ ({a, b, c, d} : Set α))
      (hg : g ∈ ({a, b, c, d} : Set α)) (hh : h ∈ ({a, b, c, d} : Set α))
      (ha : a ∈ ({e, f, g, h} : Set α)) (hb : b ∈ ({e, f, g, h} : Set α))
      (hc : c ∈ ({e, f, g, h} : Set α)) (hd : d ∈ ({e, f, g, h} : Set α)) :
      ({a, b, c, d} : Set α) = ({e, f, g, h} : Set α) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
    constructor
    · intro hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    · intro hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have s10 : Clifford.second (c 1) (c 0) = Clifford.second (c 0) (c 1) := blind_second_symm (c 0) (c 1)
  have s20 : Clifford.second (c 2) (c 0) = Clifford.second (c 0) (c 2) := blind_second_symm (c 0) (c 2)
  have s30 : Clifford.second (c 3) (c 0) = Clifford.second (c 0) (c 3) := blind_second_symm (c 0) (c 3)
  have s21 : Clifford.second (c 2) (c 1) = Clifford.second (c 1) (c 2) := blind_second_symm (c 1) (c 2)
  have s31 : Clifford.second (c 3) (c 1) = Clifford.second (c 1) (c 3) := blind_second_symm (c 1) (c 3)
  have s32 : Clifford.second (c 3) (c 2) = Clifford.second (c 2) (c 3) := blind_second_symm (c 2) (c 3)
  have ht01 : Clifford.Transversal (c 0) (c 1) := blindTransversal_iff.1 (hc.1 0 1 (by decide))
  have ht02 : Clifford.Transversal (c 0) (c 2) := blindTransversal_iff.1 (hc.1 0 2 (by decide))
  have ht03 : Clifford.Transversal (c 0) (c 3) := blindTransversal_iff.1 (hc.1 0 3 (by decide))
  have ht12 : Clifford.Transversal (c 1) (c 2) := blindTransversal_iff.1 (hc.1 1 2 (by decide))
  have ht13 : Clifford.Transversal (c 1) (c 3) := blindTransversal_iff.1 (hc.1 1 3 (by decide))
  have ht23 : Clifford.Transversal (c 2) (c 3) := blindTransversal_iff.1 (hc.1 2 3 (by decide))
  have hbs01_02 : BlindSecond (c 0) (c 1) ≠ BlindSecond (c 0) (c 2) :=
    (hc.2 0 1 2 (by decide) (by decide) (by decide)).2.1
  have hbs01_12 : BlindSecond (c 0) (c 1) ≠ BlindSecond (c 1) (c 2) :=
    (hc.2 0 1 2 (by decide) (by decide) (by decide)).2.2.1
  have hbs01_03 : BlindSecond (c 0) (c 1) ≠ BlindSecond (c 0) (c 3) :=
    (hc.2 0 1 3 (by decide) (by decide) (by decide)).2.1
  have hbs01_13 : BlindSecond (c 0) (c 1) ≠ BlindSecond (c 1) (c 3) :=
    (hc.2 0 1 3 (by decide) (by decide) (by decide)).2.2.1
  have hbs02_03 : BlindSecond (c 0) (c 2) ≠ BlindSecond (c 0) (c 3) :=
    (hc.2 0 2 3 (by decide) (by decide) (by decide)).2.1
  have hbs02_23 : BlindSecond (c 0) (c 2) ≠ BlindSecond (c 2) (c 3) :=
    (hc.2 0 2 3 (by decide) (by decide) (by decide)).2.2.1
  have hbs12_13 : BlindSecond (c 1) (c 2) ≠ BlindSecond (c 1) (c 3) :=
    (hc.2 1 2 3 (by decide) (by decide) (by decide)).2.1
  have hbs12_23 : BlindSecond (c 1) (c 2) ≠ BlindSecond (c 2) (c 3) :=
    (hc.2 1 2 3 (by decide) (by decide) (by decide)).2.2.1
  have hbs12_10 : BlindSecond (c 1) (c 2) ≠ BlindSecond (c 1) (c 0) := by
    intro h
    apply hbs01_12
    rw [BlindSecond_eq ht12, BlindSecond_eq (Clifford.cd_symm ht01)] at h
    rw [blind_second_symm (c 0) (c 1)] at h
    rw [BlindSecond_eq ht01, BlindSecond_eq ht12]
    exact h.symm
  have hbs13_10 : BlindSecond (c 1) (c 3) ≠ BlindSecond (c 1) (c 0) := by
    intro h
    apply hbs01_13
    rw [BlindSecond_eq ht13, BlindSecond_eq (Clifford.cd_symm ht01)] at h
    rw [blind_second_symm (c 0) (c 1)] at h
    rw [BlindSecond_eq ht01, BlindSecond_eq ht13]
    exact h.symm
  have hbs23_20 : BlindSecond (c 2) (c 3) ≠ BlindSecond (c 2) (c 0) := by
    intro h
    apply hbs02_23
    rw [BlindSecond_eq ht23, BlindSecond_eq (Clifford.cd_symm ht02)] at h
    rw [blind_second_symm (c 0) (c 2)] at h
    rw [BlindSecond_eq ht02, BlindSecond_eq ht23]
    exact h.symm
  have hbs23_21 : BlindSecond (c 2) (c 3) ≠ BlindSecond (c 2) (c 1) := by
    intro h
    apply hbs12_23
    have h1 : BlindSecond (c 1) (c 2) = BlindSecond (c 2) (c 1) := by
      rw [BlindSecond_eq ht12, BlindSecond_eq (Clifford.cd_symm ht12), blind_second_symm]
    exact h1.trans h.symm
  have hnc012 : ¬ Collinear ℝ ({c 0, c 1, c 2} : Set ℂ) :=
    noncollinear_centres_of_blind ht01 ht02 hbs01_02
  have hnc013 : ¬ Collinear ℝ ({c 0, c 1, c 3} : Set ℂ) :=
    noncollinear_centres_of_blind ht01 ht03 hbs01_03
  have hnc023 : ¬ Collinear ℝ ({c 0, c 2, c 3} : Set ℂ) :=
    noncollinear_centres_of_blind ht02 ht03 hbs02_03
  have hnc123 : ¬ Collinear ℝ ({c 1, c 2, c 3} : Set ℂ) :=
    noncollinear_centres_of_blind ht12 ht13 hbs12_13
  have col_perm {A B : Set ℂ} (hset : A = B) (h : Collinear ℝ A) :
      Collinear ℝ B := by simpa [hset] using h
  have ncol_perm {A B : Set ℂ} (hset : A = B) (h : ¬ Collinear ℝ A) :
      ¬ Collinear ℝ B := by simpa [hset] using h
  have gc_perm {A B : Set ℂ} (hset : A = B)
      (h : Cospherical A ∨ Collinear ℝ A) : Cospherical B ∨ Collinear ℝ B := by
    simpa [hset] using h
  have hall_of_012_013 (hA : Collinear ℝ ({p01, p02, p12} : Set ℂ))
      (hB : Collinear ℝ ({p01, p03, p13} : Set ℂ)) :
      Collinear ℝ ({p01, p02, p12} : Set ℂ) ∧
      Collinear ℝ ({p01, p03, p13} : Set ℂ) ∧
      Collinear ℝ ({p02, p03, p23} : Set ℂ) ∧
      Collinear ℝ ({p12, p13, p23} : Set ℂ) := by
    obtain ⟨_, _, h3, h4⟩ := all_four_collinear_of_two_degenerate
      ht01 ht02 ht03 ht12 ht13 ht23 hnc012 hnc013 hnc023 hnc123
      (by simpa [p01, p02, p12] using hA) (by simpa [p01, p03, p13] using hB)
    exact ⟨hA, hB, col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h3,
      col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h4⟩
  have hall_of_012_023 (hA : Collinear ℝ ({p01, p02, p12} : Set ℂ))
      (hB : Collinear ℝ ({p02, p03, p23} : Set ℂ)) :
      Collinear ℝ ({p01, p02, p12} : Set ℂ) ∧
      Collinear ℝ ({p01, p03, p13} : Set ℂ) ∧
      Collinear ℝ ({p02, p03, p23} : Set ℂ) ∧
      Collinear ℝ ({p12, p13, p23} : Set ℂ) := by
    obtain ⟨_, _, h3, h4⟩ := all_four_collinear_of_two_degenerate
      ht02 ht01 ht03 (Clifford.cd_symm ht12) ht23 ht13
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc012) hnc023
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc013)
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc123)
      (col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hA)
      (by simpa [p02, p03, p23] using hB)
    exact ⟨hA, col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h3, hB,
      col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h4⟩
  have hall_of_012_123 (hA : Collinear ℝ ({p01, p02, p12} : Set ℂ))
      (hB : Collinear ℝ ({p12, p13, p23} : Set ℂ)) :
      Collinear ℝ ({p01, p02, p12} : Set ℂ) ∧
      Collinear ℝ ({p01, p03, p13} : Set ℂ) ∧
      Collinear ℝ ({p02, p03, p23} : Set ℂ) ∧
      Collinear ℝ ({p12, p13, p23} : Set ℂ) := by
    obtain ⟨_, _, h3, h4⟩ := all_four_collinear_of_two_degenerate
      ht12 (Clifford.cd_symm ht01) ht13 (Clifford.cd_symm ht02) ht23 ht03
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc012) hnc123
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc013)
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc023)
      (col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hA)
      (by simpa [p12, p13, p23] using hB)
    exact ⟨hA, col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h3,
      col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h4, hB⟩
  have hall_of_013_023 (hA : Collinear ℝ ({p01, p03, p13} : Set ℂ))
      (hB : Collinear ℝ ({p02, p03, p23} : Set ℂ)) :
      Collinear ℝ ({p01, p02, p12} : Set ℂ) ∧
      Collinear ℝ ({p01, p03, p13} : Set ℂ) ∧
      Collinear ℝ ({p02, p03, p23} : Set ℂ) ∧
      Collinear ℝ ({p12, p13, p23} : Set ℂ) := by
    obtain ⟨_, _, h3, h4⟩ := all_four_collinear_of_two_degenerate
      ht03 ht01 ht02 (Clifford.cd_symm ht13) (Clifford.cd_symm ht23) ht12
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc013)
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc023) hnc012
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc123)
      (col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hA)
      (col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hB)
    exact ⟨col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h3, hA, hB,
      col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h4⟩
  have hall_of_013_123 (hA : Collinear ℝ ({p01, p03, p13} : Set ℂ))
      (hB : Collinear ℝ ({p12, p13, p23} : Set ℂ)) :
      Collinear ℝ ({p01, p02, p12} : Set ℂ) ∧
      Collinear ℝ ({p01, p03, p13} : Set ℂ) ∧
      Collinear ℝ ({p02, p03, p23} : Set ℂ) ∧
      Collinear ℝ ({p12, p13, p23} : Set ℂ) := by
    obtain ⟨_, _, h3, h4⟩ := all_four_collinear_of_two_degenerate
      ht13 (Clifford.cd_symm ht01) ht12 (Clifford.cd_symm ht03) (Clifford.cd_symm ht23) ht02
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc013)
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc123)
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc012)
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc023)
      (col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hA)
      (col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hB)
    exact ⟨col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h3, hA,
      col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h4, hB⟩
  have hall_of_023_123 (hA : Collinear ℝ ({p02, p03, p23} : Set ℂ))
      (hB : Collinear ℝ ({p12, p13, p23} : Set ℂ)) :
      Collinear ℝ ({p01, p02, p12} : Set ℂ) ∧
      Collinear ℝ ({p01, p03, p13} : Set ℂ) ∧
      Collinear ℝ ({p02, p03, p23} : Set ℂ) ∧
      Collinear ℝ ({p12, p13, p23} : Set ℂ) := by
    obtain ⟨_, _, h3, h4⟩ := all_four_collinear_of_two_degenerate
      ht23 (Clifford.cd_symm ht02) (Clifford.cd_symm ht12) (Clifford.cd_symm ht03) (Clifford.cd_symm ht13)
      ht01
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc023)
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc123)
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc012)
      (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc013)
      (col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hA)
      (col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hB)
    exact ⟨col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h3,
      col_perm (by ext z; simp [Fin.succAbove, BlindDelete, p01, p02, p03, p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) h4, hA, hB⟩
  by_cases hdeg :
      Collinear ℝ ({p01, p02, p12} : Set ℂ) ∨
      Collinear ℝ ({p01, p03, p13} : Set ℂ) ∨
      Collinear ℝ ({p02, p03, p23} : Set ℂ) ∨
      Collinear ℝ ({p12, p13, p23} : Set ℂ)
  · by_cases hall :
      Collinear ℝ ({p01, p02, p12} : Set ℂ) ∧
      Collinear ℝ ({p01, p03, p13} : Set ℂ) ∧
      Collinear ℝ ({p02, p03, p23} : Set ℂ) ∧
      Collinear ℝ ({p12, p13, p23} : Set ℂ)
    · refine ⟨∞, ?_⟩
      rw [BlindCliffordP, if_neg (by decide : ¬ Odd 4)]
      simp only [Bool.false_eq_true, false_implies, true_and]
      refine ⟨(∞ : BlindS), rfl, ?_⟩
      intro i
      fin_cases i
      · exact blindChain_three_of_collinear (blindGenPos_succAbove hc 0)
          (col_perm (by ext z; simp [BlindDelete, Fin.succAbove, p12, p13, p23]) hall.2.2.2)
      · exact blindChain_three_of_collinear (blindGenPos_succAbove hc 1)
          (col_perm (by ext z; simp [BlindDelete, Fin.succAbove, p02, p03, p23]) hall.2.2.1)
      · exact blindChain_three_of_collinear (blindGenPos_succAbove hc 2)
          (col_perm (by ext z; simp [BlindDelete, Fin.succAbove, p01, p03, p13]) hall.2.1)
      · exact blindChain_three_of_collinear (blindGenPos_succAbove hc 3)
          (col_perm (by ext z; simp [BlindDelete, Fin.succAbove, p01, p02, p12]) hall.1)
    · rcases hdeg with h012 | h013 | h023 | h123
      · have hn013 : ¬ Collinear ℝ ({p01, p03, p13} : Set ℂ) := by
          intro h
          exact hall (hall_of_012_013 h012 h)
        have hn023 : ¬ Collinear ℝ ({p02, p03, p23} : Set ℂ) := by
          intro h
          exact hall (hall_of_012_023 h012 h)
        have hn123 : ¬ Collinear ℝ ({p12, p13, p23} : Set ℂ) := by
          intro h
          exact hall (hall_of_012_123 h012 h)
        obtain ⟨q, habc, habd, hacd, hbcd⟩ := miquel_gcircles_of_one_degenerate
          ht01 ht02 ht03 ht12 ht13 ht23 hnc012 hnc013 hnc023 hnc123
          hbs01_02 hbs01_03 hbs02_03 hbs12_13
          (by simpa [p01, p02, p12] using h012)
          (by simpa [p01, p03, p13] using hn013)
          (by simpa [p02, p03, p23] using hn023)
          (by simpa [p12, p13, p23] using hn123)
        refine ⟨(q : BlindS), ?_⟩
        rw [BlindCliffordP, if_neg (by decide : ¬ Odd 4)]
        simp only [Bool.false_eq_true, false_implies, true_and]
        refine ⟨(q : BlindS), rfl, ?_⟩
        intro i
        fin_cases i
        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 0) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p12, p13, p23, s10, s20, s30, s21, s31, s32]) hbcd

        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 1) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p02, p03, p23, s10, s20, s30, s21, s31, s32]) hacd

        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 2) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p01, p03, p13, s10, s20, s30, s21, s31, s32]) habd

        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 3) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p01, p02, p12, s10, s20, s30, s21, s31, s32]) habc

      · have hn012 : ¬ Collinear ℝ ({p01, p02, p12} : Set ℂ) := by
          intro h
          exact hall (hall_of_012_013 h h013)
        have hn023 : ¬ Collinear ℝ ({p02, p03, p23} : Set ℂ) := by
          intro h
          exact hall (hall_of_013_023 h013 h)
        have hn123 : ¬ Collinear ℝ ({p12, p13, p23} : Set ℂ) := by
          intro h
          exact hall (hall_of_013_123 h013 h)
        obtain ⟨q, habc, habd, hacd, hbcd⟩ := miquel_gcircles_of_one_degenerate
          ht01 ht03 ht02 ht13 ht12 (Clifford.cd_symm ht23) hnc013 hnc012
          (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc023)
          (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc123)
          hbs01_03 hbs01_02 hbs02_03.symm hbs12_13.symm
          (by simpa [p01, p03, p13] using h013)
          (by simpa [p01, p02, p12] using hn012)
          (ncol_perm (by ext z; simp [p02, p03, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hn023)
          (ncol_perm (by ext z; simp [p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hn123)
        refine ⟨(q : BlindS), ?_⟩
        rw [BlindCliffordP, if_neg (by decide : ¬ Odd 4)]
        simp only [Bool.false_eq_true, false_implies, true_and]
        refine ⟨(q : BlindS), rfl, ?_⟩
        intro i
        fin_cases i
        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 0) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p12, p13, p23, s10, s20, s30, s21, s31, s32]) hbcd
        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 1) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p02, p03, p23, s10, s20, s30, s21, s31, s32]) hacd

        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 2) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p01, p03, p13, s10, s20, s30, s21, s31, s32]) habc

        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 3) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p01, p02, p12, s10, s20, s30, s21, s31, s32]) habd
      · have hn012 : ¬ Collinear ℝ ({p01, p02, p12} : Set ℂ) := by
          intro h
          exact hall (hall_of_012_023 h h023)
        have hn013 : ¬ Collinear ℝ ({p01, p03, p13} : Set ℂ) := by
          intro h
          exact hall (hall_of_013_023 h h023)
        have hn123 : ¬ Collinear ℝ ({p12, p13, p23} : Set ℂ) := by
          intro h
          exact hall (hall_of_023_123 h023 h)
        obtain ⟨q, habc, habd, hacd, hbcd⟩ := miquel_gcircles_of_one_degenerate
          ht02 ht03 ht01 ht23 (Clifford.cd_symm ht12) (Clifford.cd_symm ht13)
          hnc023 (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc012)
          (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc013)
          (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc123)
          hbs02_03 hbs01_02.symm hbs01_03.symm hbs23_21
          (by simpa [p02, p03, p23] using h023)
          (ncol_perm (by ext z; simp [p01, p02, p12, blind_second_symm, or_assoc, or_comm, or_left_comm]) hn012)
          (ncol_perm (by ext z; simp [p01, p03, p13, blind_second_symm, or_assoc, or_comm, or_left_comm]) hn013)
          (ncol_perm (by ext z; simp [p12, p13, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hn123)
        refine ⟨(q : BlindS), ?_⟩
        rw [BlindCliffordP, if_neg (by decide : ¬ Odd 4)]
        simp only [Bool.false_eq_true, false_implies, true_and]
        refine ⟨(q : BlindS), rfl, ?_⟩
        intro i
        fin_cases i
        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 0) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p12, p13, p23, s10, s20, s30, s21, s31, s32]) hbcd
        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 1) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p02, p03, p23, s10, s20, s30, s21, s31, s32]) habc

        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 2) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p01, p03, p13, s10, s20, s30, s21, s31, s32]) hacd
        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 3) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p01, p02, p12, s10, s20, s30, s21, s31, s32]) habd
      · have hn012 : ¬ Collinear ℝ ({p01, p02, p12} : Set ℂ) := by
          intro h
          exact hall (hall_of_012_123 h h123)
        have hn013 : ¬ Collinear ℝ ({p01, p03, p13} : Set ℂ) := by
          intro h
          exact hall (hall_of_013_123 h h123)
        have hn023 : ¬ Collinear ℝ ({p02, p03, p23} : Set ℂ) := by
          intro h
          exact hall (hall_of_023_123 h h123)
        obtain ⟨q, habc, habd, hacd, hbcd⟩ := miquel_gcircles_of_one_degenerate
          ht12 ht13 (Clifford.cd_symm ht01) ht23 (Clifford.cd_symm ht02) (Clifford.cd_symm ht03)
          hnc123 (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc012)
          (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc013)
          (ncol_perm (by ext z; simp [or_assoc, or_comm, or_left_comm]) hnc023)
          hbs12_13 hbs12_10 hbs13_10 hbs23_20
          (by simpa [p12, p13, p23] using h123)
          (ncol_perm (by ext z; simp [p01, p02, p12, blind_second_symm, or_assoc, or_comm, or_left_comm]) hn012)
          (ncol_perm (by ext z; simp [p01, p03, p13, blind_second_symm, or_assoc, or_comm, or_left_comm]) hn013)
          (ncol_perm (by ext z; simp [p02, p03, p23, blind_second_symm, or_assoc, or_comm, or_left_comm]) hn023)
        refine ⟨(q : BlindS), ?_⟩
        rw [BlindCliffordP, if_neg (by decide : ¬ Odd 4)]
        simp only [Bool.false_eq_true, false_implies, true_and]
        refine ⟨(q : BlindS), rfl, ?_⟩
        intro i
        fin_cases i
        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 0) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p12, p13, p23, s10, s20, s30, s21, s31, s32]) habc

        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 1) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p02, p03, p23, s10, s20, s30, s21, s31, s32]) hbcd

        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 2) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p01, p03, p13, s10, s20, s30, s21, s31, s32]) hacd

        · refine blindChain_three_of_gcircle (blindGenPos_succAbove hc 3) ?_
          exact gc_perm (by apply set4_eq_of_mem <;> simp [BlindDelete, Fin.succAbove, p01, p02, p12, s10, s20, s30, s21, s31, s32]) habd

  · have h012 : ¬ Collinear ℝ ({Clifford.second (c 0) (c 1), Clifford.second (c 0) (c 2),
        Clifford.second (c 1) (c 2)} : Set ℂ) := by
      intro h
      exact hdeg (Or.inl (by simpa [p01, p02, p12] using h))
    have h013 : ¬ Collinear ℝ ({Clifford.second (c 0) (c 1), Clifford.second (c 0) (c 3),
        Clifford.second (c 1) (c 3)} : Set ℂ) := by
      intro h
      exact hdeg (Or.inr (Or.inl (by simpa [p01, p03, p13] using h)))
    have h023 : ¬ Collinear ℝ ({Clifford.second (c 0) (c 2), Clifford.second (c 0) (c 3),
        Clifford.second (c 2) (c 3)} : Set ℂ) := by
      intro h
      exact hdeg (Or.inr (Or.inr (Or.inl (by simpa [p02, p03, p23] using h))))
    have h123 : ¬ Collinear ℝ ({Clifford.second (c 1) (c 2), Clifford.second (c 1) (c 3),
        Clifford.second (c 2) (c 3)} : Set ℂ) := by
      intro h
      exact hdeg (Or.inr (Or.inr (Or.inr (by simpa [p12, p13, p23] using h))))
    exact blindChain_four_of_genPos4 hc (genPos4_of_blindGenPos hc h012 h013 h023 h123)

/-- Level 5 under the library's general position: the five Miquel points of the five deletions
lie on a generalized circle by `Clifford.clifford_two_clean`; that circle is transported to a
blind generalized circle, with the radius-zero circle replaced by a genuine circle through the
common point. -/
lemma blindChain_five_of_genPos5 {c : Fin 5 → ℂ} (h : Clifford.GenPosN c) :
    ∃ Y : Set BlindS, BlindCliffordP false 5 c Y := by
  let m : Fin 5 → ℂ := fun i =>
    Clifford.miquel (c (i.succAbove 0)) (c (i.succAbove 1))
      (c (i.succAbove 2)) (c (i.succAbove 3))
  have hm4 : ∀ i : Fin 5, BlindCliffordP false 4 (BlindDelete c i) {((m i : ℂ) : BlindS)} := by
    intro i
    have hp : Clifford.GenPos4 ((c ∘ i.succAbove) 0) ((c ∘ i.succAbove) 1)
        ((c ∘ i.succAbove) 2) ((c ∘ i.succAbove) 3) := (h.comp_succAbove i).pos4
    have hc4 : Clifford.ChainS 4 (c ∘ i.succAbove) {((m i : ℂ) : BlindS)} := by
      simpa [m, Function.comp_def] using Clifford.chain4_ofS (c ∘ i.succAbove) hp
    have hb4 := blindCliffordP4_of_chainS (h.comp_succAbove i) ⟨m i, rfl⟩ hc4
    change BlindCliffordP false 4 (c ∘ i.succAbove) {((m i : ℂ) : BlindS)}
    exact hb4
  have hmem (i : Fin 5) : m i ∈ ({m 0, m 1, m 2, m 3, m 4} : Set ℂ) := by
    fin_cases i <;> simp
  have hset : ({m 0, m 1, m 2, m 3, m 4} : Set ℂ) =
      ({Clifford.miquel (c 0) (c 1) (c 2) (c 3),
        Clifford.miquel (c 0) (c 1) (c 2) (c 4),
        Clifford.miquel (c 0) (c 1) (c 3) (c 4),
        Clifford.miquel (c 0) (c 2) (c 3) (c 4),
        Clifford.miquel (c 1) (c 2) (c 3) (c 4)} : Set ℂ) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp [m, Fin.succAbove]
    · intro hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp [m, Fin.succAbove]
  have hgc : Cospherical ({m 0, m 1, m 2, m 3, m 4} : Set ℂ) ∨
      Collinear ℝ ({m 0, m 1, m 2, m 3, m 4} : Set ℂ) := by
    simpa [hset] using Clifford.clifford_two_clean h.pos5
  obtain ⟨X, hX, hsub⟩ := Clifford.exists_gcircle hgc
  rcases hX with ⟨o, r, rfl⟩ | ⟨p, v, hv, rfl⟩
  · by_cases hr : 0 < r
    · refine ⟨BlindEmb (Metric.sphere o r), ?_⟩
      rw [BlindCliffordP, if_pos (by decide : Odd 5)]
      simp only [Bool.false_eq_true, false_implies, true_and]
      refine ⟨Or.inl ⟨o, r, hr, rfl⟩, ?_⟩
      intro i
      refine ⟨((m i : ℂ) : BlindS), hm4 i, ?_⟩
      exact ⟨m i, hsub (hmem i), rfl⟩
    · have hr0 : r = 0 := by
        have hnonneg : 0 ≤ r := by
          have hd := (Metric.mem_sphere.mp (hsub (hmem 0)))
          rw [← hd]
          exact dist_nonneg
        exact le_antisymm (le_of_not_gt hr) hnonneg
      have hm0 : m 0 = o := by
        apply dist_eq_zero.mp
        simpa [hr0] using (Metric.mem_sphere.mp
          (hsub (hmem 0)))
      refine ⟨BlindEmb (Metric.sphere (o + 1) 1), ?_⟩
      rw [BlindCliffordP, if_pos (by decide : Odd 5)]
      simp only [Bool.false_eq_true, false_implies, true_and]
      refine ⟨Or.inl ⟨o + 1, 1, by norm_num, rfl⟩, ?_⟩
      intro i
      refine ⟨((m i : ℂ) : BlindS), hm4 i, ?_⟩
      have hmi : m i = o := by
        apply dist_eq_zero.mp
        simpa [hr0] using (Metric.mem_sphere.mp
          (hsub (hmem i)))
      rw [hmi]
      refine ⟨o, ?_, rfl⟩
      rw [Metric.mem_sphere, Complex.dist_eq]
      norm_num
  · refine ⟨Clifford.lineS p v, ?_⟩
    rw [BlindCliffordP, if_pos (by decide : Odd 5)]
    simp only [Bool.false_eq_true, false_implies, true_and]
    refine ⟨blindIsGCircle_lineS p v hv, ?_⟩
    intro i
    refine ⟨((m i : ℂ) : BlindS), hm4 i, ?_⟩
    rcases hsub (hmem i) with ⟨t, ht⟩
    exact Clifford.mem_lineS ht

/-- Clifford's second theorem in the form available under `BlindGenPos` when all five level-4
points are finite: the hypotheses are pairwise transversality, noncollinearity of every triple
of centres and nonvanishing of `mD` on every four-subset. These are exactly the hypotheses that
`GenPos5` supplies, but they also hold when some triples of second intersections are collinear. -/
lemma clifford_two_clean_blind {a b c d e : ℂ}
    (hab : Clifford.Transversal a b) (hac : Clifford.Transversal a c)
    (had : Clifford.Transversal a d) (hae : Clifford.Transversal a e)
    (hbc : Clifford.Transversal b c) (hbd : Clifford.Transversal b d)
    (hbe : Clifford.Transversal b e) (hcd : Clifford.Transversal c d)
    (hce : Clifford.Transversal c e) (hde : Clifford.Transversal d e)
    (hnabc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hnabd : ¬ Collinear ℝ ({a, b, d} : Set ℂ))
    (hnabe : ¬ Collinear ℝ ({a, b, e} : Set ℂ))
    (hnacd : ¬ Collinear ℝ ({a, c, d} : Set ℂ))
    (hnace : ¬ Collinear ℝ ({a, c, e} : Set ℂ))
    (hnade : ¬ Collinear ℝ ({a, d, e} : Set ℂ))
    (hnbcd : ¬ Collinear ℝ ({b, c, d} : Set ℂ))
    (hnbce : ¬ Collinear ℝ ({b, c, e} : Set ℂ))
    (hnbde : ¬ Collinear ℝ ({b, d, e} : Set ℂ))
    (hncde : ¬ Collinear ℝ ({c, d, e} : Set ℂ))
    (hDabcd : Clifford.mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0)
    (hDabce : Clifford.mD a b c e (conj a) (conj b) (conj c) (conj e) ≠ 0)
    (hDabde : Clifford.mD a b d e (conj a) (conj b) (conj d) (conj e) ≠ 0)
    (hDacde : Clifford.mD a c d e (conj a) (conj c) (conj d) (conj e) ≠ 0)
    (hDbcde : Clifford.mD b c d e (conj b) (conj c) (conj d) (conj e) ≠ 0) :
    Cospherical ({Clifford.miquel a b c d, Clifford.miquel a b c e, Clifford.miquel a b d e,
      Clifford.miquel a c d e, Clifford.miquel b c d e} : Set ℂ) ∨
    Collinear ℝ ({Clifford.miquel a b c d, Clifford.miquel a b c e, Clifford.miquel a b d e,
      Clifford.miquel a c d e, Clifford.miquel b c d e} : Set ℂ) := by
  let S : Set ℂ := {Clifford.miquel a b c d, Clifford.miquel a b c e, Clifford.miquel a b d e,
      Clifford.miquel a c d e, Clifford.miquel b c d e}
  have ha : a ≠ 0 := hab.left_ne_zero
  have hb : b ≠ 0 := hbc.left_ne_zero
  have hc : c ≠ 0 := hcd.left_ne_zero
  have hd : d ≠ 0 := hde.left_ne_zero
  have he : e ≠ 0 := hde.right_ne_zero
  have ht_abc : Clifford.triP a b c (conj a) (conj b) (conj c) ≠ 0 :=
    (Clifford.triP_ne_zero_iff a b c).2 hnabc
  have ht_abd : Clifford.triP a b d (conj a) (conj b) (conj d) ≠ 0 :=
    (Clifford.triP_ne_zero_iff a b d).2 hnabd
  have ht_abe : Clifford.triP a b e (conj a) (conj b) (conj e) ≠ 0 :=
    (Clifford.triP_ne_zero_iff a b e).2 hnabe
  have ht_acd : Clifford.triP a c d (conj a) (conj c) (conj d) ≠ 0 :=
    (Clifford.triP_ne_zero_iff a c d).2 hnacd
  have ht_ace : Clifford.triP a c e (conj a) (conj c) (conj e) ≠ 0 :=
    (Clifford.triP_ne_zero_iff a c e).2 hnace
  have ht_ade : Clifford.triP a d e (conj a) (conj d) (conj e) ≠ 0 :=
    (Clifford.triP_ne_zero_iff a d e).2 hnade
  have ht_bcd : Clifford.triP b c d (conj b) (conj c) (conj d) ≠ 0 :=
    (Clifford.triP_ne_zero_iff b c d).2 hnbcd
  have ht_bce : Clifford.triP b c e (conj b) (conj c) (conj e) ≠ 0 :=
    (Clifford.triP_ne_zero_iff b c e).2 hnbce
  have ht_bde : Clifford.triP b d e (conj b) (conj d) (conj e) ≠ 0 :=
    (Clifford.triP_ne_zero_iff b d e).2 hnbde
  have ht_cde : Clifford.triP c d e (conj c) (conj d) (conj e) ≠ 0 :=
    (Clifford.triP_ne_zero_iff c d e).2 hncde
  have hon : ∀ z ∈ S, Clifford.cliffordEq a b c d e z = 0 := by
    intro z hz
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact Clifford.cliffordEq_miquel ha hb hc ht_abc hDabcd
    · have h1 := Clifford.cliffordEq_miquel (d := e) (e := d) ha hb hc ht_abc hDabce
      rw [Clifford.cliffordEq, Clifford.kK_p12354, neg_eq_zero] at h1
      exact h1
    · have h1 := Clifford.cliffordEq_miquel (c := d) (d := e) (e := c)
        ha hb hd ht_abd hDabde
      rw [Clifford.cliffordEq, Clifford.kK_p12453] at h1
      exact h1
    · have h1 := Clifford.cliffordEq_miquel (b := c) (c := d) (d := e) (e := b)
        ha hc hd ht_acd hDacde
      rw [Clifford.cliffordEq, Clifford.kK_p13452, neg_eq_zero] at h1
      exact h1
    · have h1 := Clifford.cliffordEq_miquel (a := b) (b := c) (c := d) (d := e) (e := a)
        hb hc hd ht_bcd hDbcde
      rw [Clifford.cliffordEq, Clifford.kK_p23451] at h1
      exact h1
  by_cases hk : Clifford.CliffordNondeg a b c d e
  · left
    let g0 := Clifford.k0 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)
    let g1 := Clifford.k1 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)
    let g2 := Clifford.k2 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)
    have hcy : (conj (g2 / Clifford.k3 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e))) =
        g1 / Clifford.k3 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) := by
      rw [map_div₀, Clifford.map_k2, Clifford.map_k3]
      simp only [starRingEnd_self_apply]
      rw [Clifford.k2_swap, Clifford.k3_swap]
    refine Clifford.cospherical_of_eq (g₀ := g0) (g₁ := g1) (g₂ := g2)
      (cy := Clifford.k3 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)) hk hcy ?_
    intro z hz
    have hz' := hon z hz
    rw [Clifford.cliffordEq, Clifford.kK_expand] at hz'
    simpa [g0, g1, g2] using hz'
  · have hk3 : Clifford.k3 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) = 0 :=
      not_not.1 hk
    have hconj : conj (Clifford.k1 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)) =
        Clifford.k2 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) := by
      rw [Clifford.map_k1]
      simp only [starRingEnd_self_apply]
      rw [Clifford.k2_swap]
    by_cases hk1 : Clifford.k1 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) = 0
    · left
      have hk2 : Clifford.k2 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) = 0 := by
        rw [← hconj, hk1, map_zero]
      have hk0 : Clifford.k0 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) = 0 := by
        have h1 := hon (Clifford.miquel a b c d) (by simp [S])
        rw [Clifford.cliffordEq, Clifford.kK_expand, hk1, hk2, hk3] at h1
        linear_combination h1
      have H : ∀ z Z, Clifford.kK a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) z Z = 0 := by
        intro z Z
        rw [Clifford.kK_expand, hk0, hk1, hk2, hk3]
        ring
      have hall : ∀ z ∈ S, z = Clifford.miquel a b c d := by
        intro z hz
        simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · rfl
        · exact (Clifford.miquel_eq_of_kK_zero ha hb hc hd he hDabcd hDabce H).symm
        · rw [← Clifford.miquel_p1243 a b c d]
          refine Clifford.miquel_eq_of_kK_zero (a := a) (b := b) (c := d) (d := e) (e := c)
            ha hb hd he hc hDabde ?_ (fun z Z => by rw [Clifford.kK_p12453]; exact H z Z)
          rw [Clifford.mD_p1243]
          exact neg_ne_zero.2 hDabcd
        · rw [← Clifford.miquel_p1342 a b c d]
          refine Clifford.miquel_eq_of_kK_zero (a := a) (b := c) (c := d) (d := e) (e := b)
            ha hc hd he hb hDacde ?_ (fun z Z => by rw [Clifford.kK_p13452, H, neg_zero])
          rw [Clifford.mD_p1342]
          exact hDabcd
        · rw [← Clifford.miquel_p2341 a b c d]
          refine Clifford.miquel_eq_of_kK_zero (a := b) (b := c) (c := d) (d := e) (e := a)
            hb hc hd he ha hDbcde ?_ (fun z Z => by rw [Clifford.kK_p23451]; exact H z Z)
          rw [Clifford.mD_p2341]
          exact neg_ne_zero.2 hDabcd
      exact ⟨Clifford.miquel a b c d, 0, fun z hz => by rw [hall z hz, dist_self]⟩
    · right
      refine Clifford.collinear_of_line hk1
        (g₀ := Clifford.k0 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)) ?_
      intro z hz
      have h1 := hon z hz
      rw [Clifford.cliffordEq, Clifford.kK_expand, hk3, ← hconj] at h1
      linear_combination h1

/-- Assembling a blind level-5 object from five finite level-4 points on one plane
generalized circle. The radius-zero circle is replaced by a genuine circle through the common
point; a line is taken together with `∞`. -/
lemma blindCliffordP5_of_five_points {c : Fin 5 → ℂ} (m : Fin 5 → ℂ)
    (hm4 : ∀ i : Fin 5, BlindCliffordP false 4 (BlindDelete c i) {((m i : ℂ) : BlindS)})
    (hgc : Cospherical ({m 0, m 1, m 2, m 3, m 4} : Set ℂ) ∨
      Collinear ℝ ({m 0, m 1, m 2, m 3, m 4} : Set ℂ)) :
    ∃ Y : Set BlindS, BlindCliffordP false 5 c Y := by
  have hmem (i : Fin 5) : m i ∈ ({m 0, m 1, m 2, m 3, m 4} : Set ℂ) := by
    fin_cases i <;> simp
  obtain ⟨X, hX, hsub⟩ := Clifford.exists_gcircle hgc
  rcases hX with ⟨o, r, rfl⟩ | ⟨p, v, hv, rfl⟩
  · by_cases hr : 0 < r
    · refine ⟨BlindEmb (Metric.sphere o r), ?_⟩
      rw [BlindCliffordP, if_pos (by decide : Odd 5)]
      simp only [Bool.false_eq_true, false_implies, true_and]
      refine ⟨Or.inl ⟨o, r, hr, rfl⟩, ?_⟩
      intro i
      refine ⟨((m i : ℂ) : BlindS), hm4 i, ?_⟩
      exact ⟨m i, hsub (hmem i), rfl⟩
    · have hr0 : r = 0 := by
        have hnonneg : 0 ≤ r := by
          have hd := Metric.mem_sphere.mp (hsub (hmem 0))
          rw [← hd]
          exact dist_nonneg
        exact le_antisymm (le_of_not_gt hr) hnonneg
      refine ⟨BlindEmb (Metric.sphere (o + 1) 1), ?_⟩
      rw [BlindCliffordP, if_pos (by decide : Odd 5)]
      simp only [Bool.false_eq_true, false_implies, true_and]
      refine ⟨Or.inl ⟨o + 1, 1, by norm_num, rfl⟩, ?_⟩
      intro i
      refine ⟨((m i : ℂ) : BlindS), hm4 i, ?_⟩
      have hmi : m i = o := by
        apply dist_eq_zero.mp
        simpa [hr0] using (Metric.mem_sphere.mp (hsub (hmem i)))
      rw [hmi]
      refine ⟨o, ?_, rfl⟩
      rw [Metric.mem_sphere, Complex.dist_eq]
      norm_num
  · refine ⟨Clifford.lineS p v, ?_⟩
    rw [BlindCliffordP, if_pos (by decide : Odd 5)]
    simp only [Bool.false_eq_true, false_implies, true_and]
    refine ⟨blindIsGCircle_lineS p v hv, ?_⟩
    intro i
    refine ⟨((m i : ℂ) : BlindS), hm4 i, ?_⟩
    rcases hsub (hmem i) with ⟨t, ht⟩
    exact Clifford.mem_lineS ht

/-- Level 5 in the finite/Miquel case under `BlindGenPos`: if the five level-4 objects are the
Miquel points of the five deletions and all five `mD` are nonzero, Clifford's second theorem
still holds (with collinear triples allowed), and the level-5 object exists. -/
lemma blindChain_five_of_finite_miquel {c : Fin 5 → ℂ} (hc : BlindGenPos c)
    (hm4 : ∀ i : Fin 5, BlindCliffordP false 4 (BlindDelete c i)
      {((Clifford.miquel (c (i.succAbove 0)) (c (i.succAbove 1))
          (c (i.succAbove 2)) (c (i.succAbove 3)) : ℂ) : BlindS)})
    (hD : ∀ i : Fin 5,
      Clifford.mD (c (i.succAbove 0)) (c (i.succAbove 1))
        (c (i.succAbove 2)) (c (i.succAbove 3)) (conj (c (i.succAbove 0)))
        (conj (c (i.succAbove 1))) (conj (c (i.succAbove 2))) (conj (c (i.succAbove 3))) ≠ 0) :
    ∃ Y : Set BlindS, BlindCliffordP false 5 c Y := by
  let m : Fin 5 → ℂ := fun i =>
    Clifford.miquel (c (i.succAbove 0)) (c (i.succAbove 1))
      (c (i.succAbove 2)) (c (i.succAbove 3))
  have hset : ({m 0, m 1, m 2, m 3, m 4} : Set ℂ) =
      ({Clifford.miquel (c 0) (c 1) (c 2) (c 3),
        Clifford.miquel (c 0) (c 1) (c 2) (c 4),
        Clifford.miquel (c 0) (c 1) (c 3) (c 4),
        Clifford.miquel (c 0) (c 2) (c 3) (c 4),
        Clifford.miquel (c 1) (c 2) (c 3) (c 4)} : Set ℂ) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp [m, Fin.succAbove]
    · intro hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp [m, Fin.succAbove]
  have ht (i j : Fin 5) (hij : i ≠ j) : Clifford.Transversal (c i) (c j) :=
    blindTransversal_iff.1 (hc.1 i j hij)
  have hnc (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ¬ Collinear ℝ ({c i, c j, c k} : Set ℂ) :=
    noncollinear_centres_of_blind (ht i j hij) (ht i k hik)
      ((hc.2 i j k hij hik hjk).2.1)
  have hgc : Cospherical ({m 0, m 1, m 2, m 3, m 4} : Set ℂ) ∨
      Collinear ℝ ({m 0, m 1, m 2, m 3, m 4} : Set ℂ) := by
    rw [hset]
    apply clifford_two_clean_blind
    · exact ht 0 1 (by decide)
    · exact ht 0 2 (by decide)
    · exact ht 0 3 (by decide)
    · exact ht 0 4 (by decide)
    · exact ht 1 2 (by decide)
    · exact ht 1 3 (by decide)
    · exact ht 1 4 (by decide)
    · exact ht 2 3 (by decide)
    · exact ht 2 4 (by decide)
    · exact ht 3 4 (by decide)
    · exact hnc 0 1 2 (by decide) (by decide) (by decide)
    · exact hnc 0 1 3 (by decide) (by decide) (by decide)
    · exact hnc 0 1 4 (by decide) (by decide) (by decide)
    · exact hnc 0 2 3 (by decide) (by decide) (by decide)
    · exact hnc 0 2 4 (by decide) (by decide) (by decide)
    · exact hnc 0 3 4 (by decide) (by decide) (by decide)
    · exact hnc 1 2 3 (by decide) (by decide) (by decide)
    · exact hnc 1 2 4 (by decide) (by decide) (by decide)
    · exact hnc 1 3 4 (by decide) (by decide) (by decide)
    · exact hnc 2 3 4 (by decide) (by decide) (by decide)
    · simpa [Fin.succAbove] using hD 4
    · simpa [Fin.succAbove] using hD 3
    · simpa [Fin.succAbove] using hD 2
    · simpa [Fin.succAbove] using hD 1
    · simpa [Fin.succAbove] using hD 0
  apply blindCliffordP5_of_five_points m
  · intro i
    simpa [m] using hm4 i
  · exact hgc

/-- The remaining geometric gap: given the `m` level-`m` objects of the `m` deletions of a
`BlindGenPos` `(m+1)`-tuple, they assemble into one level-`(m+1)` object. For odd `m+1` this is
the statement that the `m` level-`m` points lie on one blind generalized circle; for even `m+1`
it is the dual statement that the `m` level-`m` circles have a common point. The case `m = 4`
is `blindChain_five` and is proved above under `GenPosN`; the degenerate blind cases at `m = 4`
and all cases `m ≥ 5` remain open. -/
lemma blindClifford_second (m : ℕ) (hm : 3 ≤ m) {c : Fin (m + 1) → ℂ}
    (hc : BlindGenPos c)
    (hdel : ∀ i : Fin (m + 1), ∃ X : Set BlindS, BlindCliffordP false m (BlindDelete c i) X) :
    ∃ X : Set BlindS, BlindCliffordP false (m + 1) c X := by
  sorry

/-- The induction step in the form quoted by the paper: the level-`m` objects of all deletions
assemble into the level-`(m+1)` object. -/
lemma blindChain_succ (m : ℕ) (hm : 3 ≤ m) {c : Fin (m + 1) → ℂ}
    (hc : BlindGenPos c)
    (hdel : ∀ i : Fin (m + 1), ∃ X : Set BlindS, BlindCliffordP false m (BlindDelete c i) X) :
    ∃ X : Set BlindS, BlindCliffordP false (m + 1) c X :=
  blindClifford_second m hm hc hdel

/-- The target of the brief. Levels 1-5 are proved here (level 5 under `Clifford.GenPosN`);
the general induction uses `blindClifford_second` above. -/
theorem blindN1_direct : ∀ (n : ℕ), 1 ≤ n → ∀ c : Fin n → ℂ, BlindGenPos c →
    ∃ X : Set BlindS, BlindClifford n c X := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn c hc
      match n with
      | 0 => omega
      | 1 =>
          refine ⟨BlindEmb (BlindCircle (c 0)), ?_⟩
          simp [BlindClifford, BlindCliffordP]
      | 2 =>
          refine ⟨{((BlindSecond (c 0) (c 1) : ℂ) : BlindS)}, ?_⟩
          simp [BlindClifford, BlindCliffordP]
      | 3 =>
          rcases blindChain_three hc with ⟨Y, hY⟩
          exact ⟨Y, by simpa [BlindClifford] using hY⟩
      | 4 =>
          rcases blindChain_four hc with ⟨p, hp⟩
          exact ⟨{p}, by simpa [BlindClifford] using hp⟩
      | k + 5 =>
          have hdel : ∀ i : Fin (k + 5), ∃ X : Set BlindS,
              BlindCliffordP false (k + 4) (BlindDelete c i) X := by
            intro i
            have hci : BlindGenPos (BlindDelete c i) := by
              change BlindGenPos (c ∘ i.succAbove)
              exact blindGenPos_succAbove hc i
            rcases ih (k + 4) (by omega) (by omega) (BlindDelete c i) hci with ⟨X, hX⟩
            exact ⟨X, by simpa [BlindClifford] using hX⟩
          rcases blindClifford_second (k + 4) (by omega) hc hdel with ⟨X, hX⟩
          exact ⟨X, by simpa [BlindClifford] using hX⟩

end BlindChain
