import Inversion

/-!
# Ptolemy's equality case, direction (⇒) (L15 item I2b)

For pairwise distinct `A B C D` in the Euclidean plane,
`|AB|·|CD| + |BC|·|DA| = |AC|·|BD|` implies that either the four points are concyclic and the
diagonals `AC`, `BD` cross, or they are collinear in the cyclic order `A, B, C, D`.

Proof: invert at `B` (`a = A - B`, …). Equality becomes `Wbtw a' d' c'` for the images, i.e.
`d' = (1-t)a' + t c'` with `0 < t < 1`. Undoing the inversion, `d = α a + β c` with `α, β > 0`,
`‖d‖² = α‖a‖² + β‖c‖²`, and strict convexity of `‖·‖²` gives `α + β > 1`; hence
`X = d/(α+β)` lies strictly inside both diagonals. If `0, a, c` are not collinear, the
circumcircle of `0, a, c` contains `d` (from `‖d‖² = α‖a‖² + β‖c‖²`). If they are collinear,
`c = s a`, `d = r a` and `s (s - r) (r - 1) > 0`, which is exactly a cyclic order of
`1, 0, s, r` on the line.
-/

open EuclideanGeometry Inversion

local notation "E2" => EuclideanSpace ℝ (Fin 2)

noncomputable section

namespace PtolemyOrder

/-- Verbatim from `PaperIClassical.lean` (as in `scratch/L15_compare.lean`). -/
def ClassicalLineCyclicOrder (A B C D : E2) : Prop :=
  (Sbtw ℝ A B C ∧ Sbtw ℝ B C D) ∨ (Sbtw ℝ B C D ∧ Sbtw ℝ C D A) ∨
    (Sbtw ℝ C D A ∧ Sbtw ℝ D A B) ∨ (Sbtw ℝ D A B ∧ Sbtw ℝ A B C)

theorem inner2 (x y : E2) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem normsq2 (x : E2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]

/-- Zero cross product gives proportionality. -/
theorem eq_smul_of_cross {x y : E2} (hx : x ≠ 0) (h : x 1 * y 0 - x 0 * y 1 = 0) :
    y = (inner ℝ y x / ‖x‖ ^ 2) • x := by
  have hpos : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.2 hx; positivity
  rw [inner2]; rw [normsq2] at hpos ⊢
  ext i; fin_cases i
  · simp; field_simp; linear_combination (x 1) * h
  · simp; field_simp; linear_combination -(x 0) * h

/-- Real-line ordering: four distinct reals with `(a-b)(b-c)(c-d)(d-a) < 0` are monotone in one
of the 8 rotations/reflections of the cyclic order `a, b, c, d`. -/
theorem real_order (a b c d : ℝ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (h : (a - b) * (b - c) * ((c - d) * (d - a)) < 0) :
    (a<b ∧ b<c ∧ c<d) ∨ (d<c ∧ c<b ∧ b<a) ∨ (b<c ∧ c<d ∧ d<a) ∨ (a<d ∧ d<c ∧ c<b) ∨
    (c<d ∧ d<a ∧ a<b) ∨ (b<a ∧ a<d ∧ d<c) ∨ (d<a ∧ a<b ∧ b<c) ∨ (c<b ∧ b<a ∧ a<d) := by
  rcases hab.lt_or_gt with h1 | h1 <;> rcases hbc.lt_or_gt with h4 | h4 <;>
  rcases hcd.lt_or_gt with h6 | h6 <;> rcases had.lt_or_gt with h3 | h3 <;>
  have hP := mul_pos (mul_pos (sub_pos.2 h1) (sub_pos.2 h4))
    (mul_pos (sub_pos.2 h6) (sub_pos.2 h3)) <;>
  rcases hac.lt_or_gt with h2 | h2 <;> rcases hbd.lt_or_gt with h5 | h5 <;>
  first
  | (exfalso; linarith)
  | tauto

/-- Points `B + t • a` on a line: monotone parameters give strict betweenness. -/
theorem sbtw_param {B a : E2} (ha : a ≠ 0) {x y z : ℝ} (h : (x < y ∧ y < z) ∨ (z < y ∧ y < x)) :
    Sbtw ℝ (B + x • a) (B + y • a) (B + z • a) := by
  have key : ∀ {x y z : ℝ}, x < y → y < z → Sbtw ℝ (B + x • a) (B + y • a) (B + z • a) := by
    intro x y z hxy hyz
    have hzx : z - x ≠ 0 := by linarith
    have hne : B + x • a ≠ B + z • a := by
      intro he
      have : (z - x) • a = 0 := by rw [sub_smul]; rw [add_right_inj] at he; rw [he, sub_self]
      exact hzx ((smul_eq_zero.1 this).resolve_right ha)
    have hl : B + y • a = AffineMap.lineMap (B + x • a) (B + z • a) ((y - x) / (z - x)) := by
      rw [AffineMap.lineMap_apply_module', show B + z • a - (B + x • a) = (z - x) • a by
        rw [sub_smul]; abel, smul_smul, div_mul_cancel₀ _ hzx, sub_smul]; abel
    rw [hl, sbtw_lineMap_iff]
    exact ⟨hne, div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key h1 h2
  · exact (key h1 h2).symm

/-- Convexity identity for `‖·‖²`. -/
theorem norm_sq_convex (t : ℝ) (x y : E2) :
    ‖(1 - t) • x + t • y‖ ^ 2 = (1 - t) * ‖x‖ ^ 2 + t * ‖y‖ ^ 2 - t * (1 - t) * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

theorem invPt_one_injective {x y : E2} (h : invPt 1 x = invPt 1 y) : x = y := by
  rw [← invPt_invPt one_ne_zero x, h, invPt_invPt one_ne_zero]

/-- **Core (origin at `B`).** From betweenness of the inverted images, `d` is a positive
combination of `a, c` with coefficient sum `> 1`. -/
theorem core {a c d : E2} (ha : a ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hac : a ≠ c) (had : a ≠ d)
    (hcd : c ≠ d) (h : Wbtw ℝ (invPt 1 a) (invPt 1 d) (invPt 1 c)) :
    ∃ α β t : ℝ, 0 < t ∧ t < 1 ∧ α = ‖d‖ ^ 2 * (1 - t) / ‖a‖ ^ 2 ∧
      β = ‖d‖ ^ 2 * t / ‖c‖ ^ 2 ∧ 1 < α + β ∧ d = α • a + β • c := by
  obtain ⟨t, ⟨ht0, ht1⟩, hdt⟩ := h
  rw [AffineMap.lineMap_apply_module] at hdt
  have hna : 0 < ‖a‖ ^ 2 := by have := norm_pos_iff.2 ha; positivity
  have hnc : 0 < ‖c‖ ^ 2 := by have := norm_pos_iff.2 hc; positivity
  have hnd : 0 < ‖d‖ ^ 2 := by have := norm_pos_iff.2 hd; positivity
  have t0 : t ≠ 0 := by
    rintro rfl; apply had; apply invPt_one_injective; rw [← hdt]; simp
  have t1 : t ≠ 1 := by
    rintro rfl; apply hcd; apply invPt_one_injective; rw [← hdt]; simp
  have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm t0)
  have ht1' : t < 1 := lt_of_le_of_ne ht1 t1
  refine ⟨‖d‖ ^ 2 * (1 - t) / ‖a‖ ^ 2, ‖d‖ ^ 2 * t / ‖c‖ ^ 2, t, ht0', ht1', rfl, rfl, ?_, ?_⟩
  · have hconv := norm_sq_convex t (invPt 1 a) (invPt 1 c)
    rw [hdt, norm_sq_invPt, norm_sq_invPt, norm_sq_invPt] at hconv
    have hne : invPt (1 : ℝ) a ≠ invPt 1 c := fun he => hac (invPt_one_injective he)
    have hδ : 0 < ‖invPt (1 : ℝ) a - invPt 1 c‖ ^ 2 := by
      have := norm_pos_iff.2 (sub_ne_zero.2 hne); positivity
    have h1t : 0 < 1 - t := by linarith
    have hδ' : 0 < t * (1 - t) * ‖invPt (1 : ℝ) a - invPt 1 c‖ ^ 2 := by positivity
    have e : ‖d‖ ^ 2 * (1 - t) / ‖a‖ ^ 2 + ‖d‖ ^ 2 * t / ‖c‖ ^ 2 =
        ‖d‖ ^ 2 * ((1 - t) * (1 ^ 4 / ‖a‖ ^ 2) + t * (1 ^ 4 / ‖c‖ ^ 2)) := by ring
    rw [e]
    have e2 : (1 - t) * (1 ^ 4 / ‖a‖ ^ 2) + t * (1 ^ 4 / ‖c‖ ^ 2) =
        1 ^ 4 / ‖d‖ ^ 2 + t * (1 - t) * ‖invPt (1 : ℝ) a - invPt 1 c‖ ^ 2 := by linarith
    rw [e2, mul_add, one_pow, mul_one_div_cancel hnd.ne']
    have := mul_pos hnd hδ'
    linarith
  · have e : d = ‖d‖ ^ 2 • invPt 1 d := by
      rw [invPt, smul_smul, one_pow, mul_one_div_cancel hnd.ne', one_smul]
    calc d = ‖d‖ ^ 2 • invPt 1 d := e
      _ = _ := by
        rw [← hdt]
        simp only [invPt, one_pow, smul_add, smul_smul]
        congr 2 <;> field_simp

/-- The 8 monotone orders of `1, 0, s, r` give the cyclic order on the line `B + ℝ a`. -/
theorem line_cyclic {B a : E2} (ha : a ≠ 0) {s r : ℝ}
    (hord : ((1:ℝ)<0 ∧ 0<s ∧ s<r) ∨ (r<s ∧ s<0 ∧ (0:ℝ)<1) ∨ (0<s ∧ s<r ∧ r<1) ∨
      (1<r ∧ r<s ∧ s<0) ∨ (s<r ∧ r<1 ∧ (1:ℝ)<0) ∨ ((0:ℝ)<1 ∧ 1<r ∧ r<s) ∨
      (r<1 ∧ (1:ℝ)<0 ∧ 0<s) ∨ (s<0 ∧ (0:ℝ)<1 ∧ 1<r)) :
    ClassicalLineCyclicOrder (B + (1 : ℝ) • a) (B + (0 : ℝ) • a) (B + s • a) (B + r • a) := by
  unfold ClassicalLineCyclicOrder
  rcases hord with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨sbtw_param ha (Or.inl ⟨h1, h2⟩), sbtw_param ha (Or.inl ⟨h2, h3⟩)⟩
  · exact Or.inl ⟨sbtw_param ha (Or.inr ⟨h2, h3⟩), sbtw_param ha (Or.inr ⟨h1, h2⟩)⟩
  · exact Or.inr (Or.inl ⟨sbtw_param ha (Or.inl ⟨h1, h2⟩), sbtw_param ha (Or.inl ⟨h2, h3⟩)⟩)
  · exact Or.inr (Or.inl ⟨sbtw_param ha (Or.inr ⟨h2, h3⟩), sbtw_param ha (Or.inr ⟨h1, h2⟩)⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨sbtw_param ha (Or.inl ⟨h1, h2⟩), sbtw_param ha (Or.inl ⟨h2, h3⟩)⟩))
  · exact Or.inr (Or.inr (Or.inl
      ⟨sbtw_param ha (Or.inr ⟨h2, h3⟩), sbtw_param ha (Or.inr ⟨h1, h2⟩)⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨sbtw_param ha (Or.inl ⟨h1, h2⟩), sbtw_param ha (Or.inl ⟨h2, h3⟩)⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨sbtw_param ha (Or.inr ⟨h2, h3⟩), sbtw_param ha (Or.inr ⟨h1, h2⟩)⟩))

/-- **I2b, direction (⇒).** Equality in Ptolemy's inequality for four distinct points of the
plane: either they are concyclic with crossing diagonals, or collinear in cyclic order
`A, B, C, D`. -/
theorem classical_I2b_mp (A B C D : E2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (heq : dist A B * dist C D + dist B C * dist D A = dist A C * dist B D) :
    (Cospherical ({A, B, C, D} : Set E2) ∧ ∃ X : E2, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
      ClassicalLineCyclicOrder A B C D := by
  have eA : A = B + (A - B) := by abel
  have eC : C = B + (C - B) := by abel
  have eD : D = B + (D - B) := by abel
  generalize hadef : A - B = a at eA
  generalize hcdef : C - B = c at eC
  generalize hddef : D - B = d at eD
  subst eA eC eD
  have ha : a ≠ 0 := by rintro rfl; simp at hAB
  have hc : c ≠ 0 := by rintro rfl; simp at hBC
  have hd : d ≠ 0 := by rintro rfl; simp at hBD
  have hac : a ≠ c := by rintro rfl; exact hAC rfl
  have had : a ≠ d := by rintro rfl; exact hAD rfl
  have hcd : c ≠ d := by rintro rfl; exact hCD rfl
  clear hadef hcdef hddef hAB hAC hAD hBC hBD hCD
  -- Ptolemy equality ⇒ betweenness of the inverted images (inversion at `B`)
  have hW : Wbtw ℝ (invPt 1 a) (invPt 1 d) (invPt 1 c) := by
    rw [← dist_add_dist_eq_iff, ptolemy_iff_dist_add_dist_invPt one_ne_zero ha hd hc]
    have e1 : dist (B + a) B = ‖a‖ := dist_self_add_left a B
    have e2 : dist B (B + c) = ‖c‖ := by rw [dist_comm]; exact dist_self_add_left c B
    have e3 : dist B (B + d) = ‖d‖ := by rw [dist_comm]; exact dist_self_add_left d B
    rw [e1, e2, e3, dist_add_left, dist_add_left, dist_add_left] at heq
    rw [dist_comm d a] at heq
    rw [dist_comm d c]
    linarith [heq, mul_comm (dist a c) ‖d‖]
  obtain ⟨α, β, t, ht0, ht1, hα, hβ, hαβ, hdab⟩ := core ha hc hd hac had hcd hW
  have hna : 0 < ‖a‖ ^ 2 := by have := norm_pos_iff.2 ha; positivity
  have hnc : 0 < ‖c‖ ^ 2 := by have := norm_pos_iff.2 hc; positivity
  have hnd : 0 < ‖d‖ ^ 2 := by have := norm_pos_iff.2 hd; positivity
  have h1t : 0 < 1 - t := by linarith
  have hαpos : 0 < α := by rw [hα]; positivity
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hnormd : ‖d‖ ^ 2 = α * ‖a‖ ^ 2 + β * ‖c‖ ^ 2 := by
    rw [hα, hβ]; field_simp; ring
  by_cases hx : a 1 * c 0 - a 0 * c 1 = 0
  · -- collinear case
    right
    set s := inner ℝ c a / ‖a‖ ^ 2
    have hcs : c = s • a := eq_smul_of_cross ha hx
    set r := α + β * s with hr
    have hdr : d = r • a := by rw [hdab, hcs, smul_smul, ← add_smul]
    have hs0 : s ≠ 0 := by intro h0; apply hc; rw [hcs, h0, zero_smul]
    have hr0 : r ≠ 0 := by intro h0; apply hd; rw [hdr, h0, zero_smul]
    have hs1 : s ≠ 1 := by intro h0; apply hac; rw [hcs, h0, one_smul]
    have hr1 : r ≠ 1 := by intro h0; apply had; rw [hdr, h0, one_smul]
    have hsr : s ≠ r := by intro h0; apply hcd; rw [hcs, hdr, h0]
    have hnc' : ‖c‖ ^ 2 = s ^ 2 * ‖a‖ ^ 2 := by
      rw [hcs, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hnd' : ‖d‖ ^ 2 = r ^ 2 * ‖a‖ ^ 2 := by
      rw [hdr, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hα' : α = r ^ 2 * (1 - t) := by rw [hα, hnd']; field_simp
    have hβ' : β * s ^ 2 = r ^ 2 * t := by rw [hβ, hnc', hnd']; field_simp
    have h1 : s = r * (s * (1 - t) + t) := by
      have h2 : r * s = r ^ 2 * (1 - t) * s + r ^ 2 * t := by
        rw [← hα', ← hβ', hr]; ring
      have h3 : r * (s - r * (s * (1 - t) + t)) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hr0
      · linarith
    have hpos : 0 < s * (s - r) * (r - 1) := by
      have e : s * (s - r) * (r - 1) = r ^ 2 * t * (1 - t) * (s - 1) ^ 2 := by
        have hs' : s - r = r * (1 - t) * (s - 1) := by linear_combination h1
        have hr' : s * (r - 1) = r * t * (s - 1) := by linear_combination -h1
        linear_combination (s - r) * hr' + r * t * (s - 1) * hs'
      rw [e]
      have : 0 < (s - 1) ^ 2 := by positivity
      have : 0 < r ^ 2 := by positivity
      positivity
    have hord := real_order 1 0 s r one_ne_zero (Ne.symm hs1) (Ne.symm hr1) (Ne.symm hs0)
      (Ne.symm hr0) hsr (by nlinarith)
    have key := line_cyclic (B := B) ha hord
    rw [one_smul, zero_smul, add_zero] at key
    rw [hcs, hdr]
    exact key
  · -- concyclic case: centre of the circle through `0, a, c` (shifted by `B`)
    left
    constructor
    · have hD : a 0 * c 1 - a 1 * c 0 ≠ 0 := by intro h0; apply hx; linarith
      set D0 := a 0 * c 1 - a 1 * c 0 with hD0
      set K : E2 := !₂[(‖a‖ ^ 2 * c 1 - ‖c‖ ^ 2 * a 1) / (2 * D0),
        (a 0 * ‖c‖ ^ 2 - c 0 * ‖a‖ ^ 2) / (2 * D0)] with hKdef
      have hK0 : K 0 = (‖a‖ ^ 2 * c 1 - ‖c‖ ^ 2 * a 1) / (2 * D0) := by simp [K]
      have hK1 : K 1 = (a 0 * ‖c‖ ^ 2 - c 0 * ‖a‖ ^ 2) / (2 * D0) := by simp [K]
      have iaK : inner ℝ a K = ‖a‖ ^ 2 / 2 := by
        rw [inner2, hK0, hK1]; field_simp; rw [hD0]; ring
      have icK : inner ℝ c K = ‖c‖ ^ 2 / 2 := by
        rw [inner2, hK0, hK1]; field_simp; rw [hD0]; ring
      have idK : inner ℝ d K = ‖d‖ ^ 2 / 2 := by
        rw [hnormd, hdab, inner_add_left, real_inner_smul_left, real_inner_smul_left, iaK, icK]
        ring
      have circ : ∀ p : E2, inner ℝ p K = ‖p‖ ^ 2 / 2 → ‖p - K‖ = ‖K‖ := by
        intro p hp
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, hp]; ring
      refine ⟨B + K, ‖K‖, ?_⟩
      intro P hP
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
      rcases hP with rfl | rfl | rfl | rfl
      · rw [dist_add_left, dist_eq_norm]; exact circ _ iaK
      · rw [dist_comm, dist_self_add_left]
      · rw [dist_add_left, dist_eq_norm]; exact circ _ icK
      · rw [dist_add_left, dist_eq_norm]; exact circ _ idK
    · refine ⟨B + (α + β)⁻¹ • d, ?_, ?_⟩
      · have hl : (α + β)⁻¹ • d = AffineMap.lineMap a c (β / (α + β)) := by
          have hne : α + β ≠ 0 := by linarith
          rw [AffineMap.lineMap_apply_module, hdab, smul_add, smul_smul, smul_smul]
          congr 2 <;> (field_simp; try ring)
        have hs : Sbtw ℝ a ((α + β)⁻¹ • d) c := by
          rw [hl, sbtw_lineMap_iff]
          exact ⟨hac, div_pos hβpos (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
        exact (sbtw_const_add_iff B).2 hs
      · have hl : (α + β)⁻¹ • d = AffineMap.lineMap (0 : E2) d (α + β)⁻¹ := by
          rw [AffineMap.lineMap_apply_module]; simp
        have hs : Sbtw ℝ 0 ((α + β)⁻¹ • d) d := by
          rw [hl, sbtw_lineMap_iff]
          exact ⟨hd.symm, inv_pos.2 (by linarith), inv_lt_one_of_one_lt₀ hαβ⟩
        have := (sbtw_const_add_iff B).2 hs
        rwa [add_zero] at this

/-! ## The full equivalence (⇐ copied from `scratch/L15_compare.lean`) -/

theorem ptolemy_eq_of_sbtw {w x y z : E2} (h₁ : Sbtw ℝ w x y) (h₂ : Sbtw ℝ x y z) :
    dist w x * dist y z + dist x y * dist z w = dist w y * dist x z := by
  have hwxz := h₁.wbtw.trans_expand_left h₂.wbtw h₂.left_ne
  have hxz := dist_add_dist_eq_iff.2 h₂.wbtw
  have hwy := dist_add_dist_eq_iff.2 h₁.wbtw
  have hwz := dist_add_dist_eq_iff.2 hwxz
  rw [dist_comm z w, ← hwz, ← hxz, ← hwy]; ring

theorem classical_I2b_mpr (A B C D : E2) :
    ((Cospherical ({A, B, C, D} : Set E2) ∧ ∃ X : E2, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
        ClassicalLineCyclicOrder A B C D) →
      dist A B * dist C D + dist B C * dist D A = dist A C * dist B D := by
  rintro (⟨hc, X, h1, h2⟩ | (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩))
  · exact mul_dist_add_mul_dist_eq_mul_dist_of_cospherical hc h1.angle₁₂₃_eq_pi
      h2.angle₁₂₃_eq_pi
  · exact ptolemy_eq_of_sbtw h1 h2
  all_goals
    have := ptolemy_eq_of_sbtw h1 h2
    simp only [dist_comm C A, dist_comm D B] at this ⊢
    linarith [this]

/-- **I2b, verbatim statement of `PaperIClassical.classical_I2b`.** -/
theorem classical_I2b (A B C D : E2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    dist A B * dist C D + dist B C * dist D A = dist A C * dist B D ↔
      (Cospherical ({A, B, C, D} : Set E2) ∧ ∃ X : E2, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
        ClassicalLineCyclicOrder A B C D :=
  ⟨classical_I2b_mp A B C D hAB hAC hAD hBC hBD hCD, classical_I2b_mpr A B C D⟩

end PtolemyOrder

#print axioms PtolemyOrder.classical_I2b_mp
#print axioms PtolemyOrder.classical_I2b
