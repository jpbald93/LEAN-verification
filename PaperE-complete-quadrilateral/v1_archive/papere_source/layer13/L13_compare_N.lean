import QuadNewton

open Complex

noncomputable section

namespace Blind

/-! ## The model (shared definitions) -/

/-- `cr(a,b) = Im(conj a * b)`. -/
def BlindCr (a b : ℂ) : ℝ := (starRingEnd ℂ a * b).im

/-- A line is a pair `(p, d)` of a point and a direction. -/
structure BlindLine where
  p : ℂ
  d : ℂ

/-- Carrier `{z : cr(d, z - p) = 0}`. -/
def BlindLine.carrier (L : BlindLine) : Set ℂ := {z | BlindCr L.d (z - L.p) = 0}

/-- `meet(L,M) = p + cr(e, q-p)/cr(e,d) * d`. -/
def BlindMeet (L M : BlindLine) : ℂ :=
  L.p + ((BlindCr M.d (M.p - L.p) / BlindCr M.d L.d : ℝ) : ℂ) * L.d

/-- General position: nonzero directions, no two parallel, no three concurrent. -/
def BlindGenPos (L₁ L₂ L₃ L₄ : BlindLine) : Prop :=
  L₁.d ≠ 0 ∧ L₂.d ≠ 0 ∧ L₃.d ≠ 0 ∧ L₄.d ≠ 0 ∧
  BlindCr L₁.d L₂.d ≠ 0 ∧ BlindCr L₁.d L₃.d ≠ 0 ∧ BlindCr L₁.d L₄.d ≠ 0 ∧
  BlindCr L₂.d L₃.d ≠ 0 ∧ BlindCr L₂.d L₄.d ≠ 0 ∧ BlindCr L₃.d L₄.d ≠ 0 ∧
  -- AMBIGUOUS: "meet(L_i,L_j) ∉ L_k for the four triples" – taken as i<j<k pair (i,j) with k the
  -- remaining indices in the triples {1,2,3},{1,2,4},{1,3,4},{2,3,4}; other choices of the pair
  -- within a triple are equivalent under non-parallelism.
  BlindMeet L₁ L₂ ∉ L₃.carrier ∧ BlindMeet L₁ L₂ ∉ L₄.carrier ∧
  BlindMeet L₁ L₃ ∉ L₄.carrier ∧ BlindMeet L₂ L₃ ∉ L₄.carrier

/-- Circumcentre, by the explicit formula. -/
def BlindCirc (a b c : ℂ) : ℂ :=
  a + (((Complex.normSq (b - a) : ℝ) : ℂ) * (c - a) - ((Complex.normSq (c - a) : ℝ) : ℂ) * (b - a)) /
    (starRingEnd ℂ (b - a) * (c - a) - (b - a) * starRingEnd ℂ (c - a))

/-- Orthocentre via Euler's relation `H = A + B + C - 2 O`. -/
def BlindOrtho (a b c : ℂ) : ℂ := a + b + c - 2 * BlindCirc a b c

/-- Foot of the perpendicular from `z` to `L`. -/
def BlindFoot (z : ℂ) (L : BlindLine) : ℂ :=
  L.p + ((((starRingEnd ℂ L.d) * (z - L.p)).re / Complex.normSq L.d : ℝ) : ℂ) * L.d

/-- Power of `z` w.r.t. the circle on `PQ` as diameter. -/
def BlindPw (z P Q : ℂ) : ℝ :=
  Complex.normSq (z - (P + Q) / 2) - (1 / 4) * Complex.normSq (P - Q)

/-- The six vertices `A_ij`. -/
def BlindA12 (L₁ L₂ _L₃ _L₄ : BlindLine) : ℂ := BlindMeet L₁ L₂
def BlindA13 (L₁ _L₂ L₃ _L₄ : BlindLine) : ℂ := BlindMeet L₁ L₃
def BlindA14 (L₁ _L₂ _L₃ L₄ : BlindLine) : ℂ := BlindMeet L₁ L₄
def BlindA23 (_L₁ L₂ L₃ _L₄ : BlindLine) : ℂ := BlindMeet L₂ L₃
def BlindA24 (_L₁ L₂ _L₃ L₄ : BlindLine) : ℂ := BlindMeet L₂ L₄
def BlindA34 (_L₁ _L₂ L₃ L₄ : BlindLine) : ℂ := BlindMeet L₃ L₄

/-- Triangles `T_k` (vertices not on `L_k`). -/
def BlindT4 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ × ℂ × ℂ :=
  (BlindA12 L₁ L₂ L₃ L₄, BlindA13 L₁ L₂ L₃ L₄, BlindA23 L₁ L₂ L₃ L₄)
def BlindT3 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ × ℂ × ℂ :=
  (BlindA12 L₁ L₂ L₃ L₄, BlindA14 L₁ L₂ L₃ L₄, BlindA24 L₁ L₂ L₃ L₄)
def BlindT2 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ × ℂ × ℂ :=
  (BlindA13 L₁ L₂ L₃ L₄, BlindA14 L₁ L₂ L₃ L₄, BlindA34 L₁ L₂ L₃ L₄)
def BlindT1 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ × ℂ × ℂ :=
  (BlindA23 L₁ L₂ L₃ L₄, BlindA24 L₁ L₂ L₃ L₄, BlindA34 L₁ L₂ L₃ L₄)

/-- Circumcentre / orthocentre of a triangle given as a triple. -/
def BlindTriCirc (T : ℂ × ℂ × ℂ) : ℂ := BlindCirc T.1 T.2.1 T.2.2
def BlindTriOrtho (T : ℂ × ℂ × ℂ) : ℂ := BlindOrtho T.1 T.2.1 T.2.2

/-- Circumcircle of a triangle: circle with centre `circ T` through its first vertex
(the other vertices are on it by the circumcentre formula).
AMBIGUOUS: radius could instead be required to equal the distance to all three vertices. -/
def BlindCircumcircle (T : ℂ × ℂ × ℂ) : Set ℂ :=
  Metric.sphere (BlindTriCirc T) (dist T.1 (BlindTriCirc T))

/-- Orthocentres `H_k` of `T_k`. -/
def BlindH1 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ := BlindTriOrtho (BlindT1 L₁ L₂ L₃ L₄)
def BlindH2 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ := BlindTriOrtho (BlindT2 L₁ L₂ L₃ L₄)
def BlindH3 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ := BlindTriOrtho (BlindT3 L₁ L₂ L₃ L₄)
def BlindH4 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ := BlindTriOrtho (BlindT4 L₁ L₂ L₃ L₄)

/-- Midpoints of the three diagonals `A12A34`, `A13A24`, `A14A23`. -/
def BlindM1 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ :=
  (BlindA12 L₁ L₂ L₃ L₄ + BlindA34 L₁ L₂ L₃ L₄) / 2
def BlindM2 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ :=
  (BlindA13 L₁ L₂ L₃ L₄ + BlindA24 L₁ L₂ L₃ L₄) / 2
def BlindM3 (L₁ L₂ L₃ L₄ : BlindLine) : ℂ :=
  (BlindA14 L₁ L₂ L₃ L₄ + BlindA23 L₁ L₂ L₃ L₄) / 2

/-- The Miquel point, by the explicit formula. -/
def BlindMiquel (L₁ L₂ L₃ L₄ : BlindLine) : ℂ :=
  BlindA12 L₁ L₂ L₃ L₄ +
    ((BlindA13 L₁ L₂ L₃ L₄ - BlindA12 L₁ L₂ L₃ L₄) * (BlindA24 L₁ L₂ L₃ L₄ - BlindA12 L₁ L₂ L₃ L₄)
      - (BlindA23 L₁ L₂ L₃ L₄ - BlindA12 L₁ L₂ L₃ L₄) * (BlindA14 L₁ L₂ L₃ L₄ - BlindA12 L₁ L₂ L₃ L₄)) /
    (BlindA13 L₁ L₂ L₃ L₄ + BlindA24 L₁ L₂ L₃ L₄ - BlindA23 L₁ L₂ L₃ L₄ - BlindA14 L₁ L₂ L₃ L₄)

/-! ## Blind statements (conclusions verbatim from PaperEBlind.lean) -/

def blind1_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    Collinear ℝ ({BlindM1 L₁ L₂ L₃ L₄, BlindM2 L₁ L₂ L₃ L₄, BlindM3 L₁ L₂ L₃ L₄} : Set ℂ)

def blind2_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    BlindM1 L₁ L₂ L₃ L₄ ≠ BlindM2 L₁ L₂ L₃ L₄

def blind3_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    Collinear ℝ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
      BlindH4 L₁ L₂ L₃ L₄} : Set ℂ)

def blind4_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    BlindH3 L₁ L₂ L₃ L₄ ≠ BlindH4 L₁ L₂ L₃ L₄ ∨ BlindH2 L₁ L₂ L₃ L₄ ≠ BlindH4 L₁ L₂ L₃ L₄

def blind5_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    ∀ H ∈ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
        BlindH4 L₁ L₂ L₃ L₄} : Set ℂ),
      BlindPw H (BlindA12 L₁ L₂ L₃ L₄) (BlindA34 L₁ L₂ L₃ L₄) =
        BlindPw H (BlindA13 L₁ L₂ L₃ L₄) (BlindA24 L₁ L₂ L₃ L₄) ∧
      BlindPw H (BlindA13 L₁ L₂ L₃ L₄) (BlindA24 L₁ L₂ L₃ L₄) =
        BlindPw H (BlindA14 L₁ L₂ L₃ L₄) (BlindA23 L₁ L₂ L₃ L₄)

def blind6_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    ∀ H ∈ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
        BlindH4 L₁ L₂ L₃ L₄} : Set ℂ),
    ∀ H' ∈ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
        BlindH4 L₁ L₂ L₃ L₄} : Set ℂ),
      ((BlindM2 L₁ L₂ L₃ L₄ - BlindM1 L₁ L₂ L₃ L₄) * starRingEnd ℂ (H' - H)).re = 0

/-! ## Translation and agreement lemmas -/

def toR (L : BlindLine) : QuadNewton.Line := ⟨L.p, L.d⟩
def toB (L : QuadNewton.Line) : BlindLine := ⟨L.p, L.d⟩

lemma toR_toB (L : QuadNewton.Line) : toR (toB L) = L := rfl

lemma cr_agree (a b : ℂ) : BlindCr a b = QuadNewton.cr a b := rfl
lemma carrier_agree (L : BlindLine) : L.carrier = (toR L).carrier := rfl
lemma meet_agree (L M : BlindLine) : BlindMeet L M = QuadNewton.meet (toR L) (toR M) := rfl
lemma circ_agree (a b c : ℂ) : BlindCirc a b c = QuadNewton.circ a b c := rfl
lemma ortho_agree (a b c : ℂ) : BlindOrtho a b c = QuadNewton.ortho a b c := rfl

/-- Not `rfl`: `normSq` vs `‖·‖ ^ 2` and `(1/4) * x` vs `x / 4`; an unfolding + Mathlib fact. -/
lemma pw_agree (z P Q : ℂ) : BlindPw z P Q = QuadNewton.pw z P Q := by
  unfold BlindPw QuadNewton.pw
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; ring

lemma genPos_agree (L₁ L₂ L₃ L₄ : BlindLine) :
    BlindGenPos L₁ L₂ L₃ L₄ ↔ QuadNewton.GenPos (toR L₁) (toR L₂) (toR L₃) (toR L₄) := by
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

/-! ## Pair 1 -/
theorem rb_1 : (type_of% @QuadNewton.newton_gauss) → blind1_stmt := by
  intro H L₁ L₂ L₃ L₄ h
  have := H ((genPos_agree _ _ _ _).mp h)
  simp only [BlindM1, BlindM2, BlindM3, BlindA12, BlindA13, BlindA14, BlindA23, BlindA24,
    BlindA34, meet_agree]
  exact this

theorem br_1 : blind1_stmt → (type_of% @QuadNewton.newton_gauss) := by
  intro H L₁ L₂ L₃ L₄ h
  exact H (toB L₁) (toB L₂) (toB L₃) (toB L₄) ((genPos_agree _ _ _ _).mpr h)

/-! ## Pair 2 -/
theorem rb_2 : (type_of% @QuadNewton.diag_midpoints_ne) → blind2_stmt := by
  intro H L₁ L₂ L₃ L₄ h
  exact H ((genPos_agree _ _ _ _).mp h)

theorem br_2 : blind2_stmt → (type_of% @QuadNewton.diag_midpoints_ne) := by
  intro H L₁ L₂ L₃ L₄ h
  exact H (toB L₁) (toB L₂) (toB L₃) (toB L₄) ((genPos_agree _ _ _ _).mpr h)

/-! ## Pair 3 -/
theorem rb_3 : (type_of% @QuadNewton.orthocentres_collinear) → blind3_stmt := by
  intro H L₁ L₂ L₃ L₄ h
  have := H ((genPos_agree _ _ _ _).mp h)
  simp only [BlindH1, BlindH2, BlindH3, BlindH4, BlindTriOrtho, BlindT1, BlindT2, BlindT3,
    BlindT4, BlindA12, BlindA13, BlindA14, BlindA23, BlindA24, BlindA34, meet_agree, ortho_agree]
  exact this

theorem br_3 : blind3_stmt → (type_of% @QuadNewton.orthocentres_collinear) := by
  intro H L₁ L₂ L₃ L₄ h
  exact H (toB L₁) (toB L₂) (toB L₃) (toB L₄) ((genPos_agree _ _ _ _).mpr h)

/-! ## Pair 4 -/
theorem rb_4 : (type_of% @QuadNewton.orthocentres_not_all_eq) → blind4_stmt := by
  intro H L₁ L₂ L₃ L₄ h
  exact H ((genPos_agree _ _ _ _).mp h)

theorem br_4 : blind4_stmt → (type_of% @QuadNewton.orthocentres_not_all_eq) := by
  intro H L₁ L₂ L₃ L₄ h
  exact H (toB L₁) (toB L₂) (toB L₃) (toB L₄) ((genPos_agree _ _ _ _).mpr h)

/-! ## Pair 5 (second conjunct: blind `pw13_24 = pw14_23`, real `pw12_34 = pw14_23`;
related by transitivity with the shared first conjunct) -/
theorem rb_5 : (type_of% @QuadNewton.bodenmiller) → blind5_stmt := by
  intro H L₁ L₂ L₃ L₄ h K hK
  obtain ⟨e1, e2⟩ := H ((genPos_agree _ _ _ _).mp h) K hK
  simp only [BlindA12, BlindA13, BlindA14, BlindA23, BlindA24, BlindA34, pw_agree, meet_agree]
  exact ⟨e1, e1.symm.trans e2⟩

theorem br_5 : blind5_stmt → (type_of% @QuadNewton.bodenmiller) := by
  intro H L₁ L₂ L₃ L₄ h K hK
  obtain ⟨e1, e2⟩ := H (toB L₁) (toB L₂) (toB L₃) (toB L₄) ((genPos_agree _ _ _ _).mpr h) K hK
  simp only [BlindA12, BlindA13, BlindA14, BlindA23, BlindA24, BlindA34, pw_agree, meet_agree,
    toR_toB] at e1 e2
  exact ⟨e1, e1.trans e2⟩

/-! ## Pair 6 -/
theorem rb_6 : (type_of% @QuadNewton.orthocentre_line_perp) → blind6_stmt := by
  intro H L₁ L₂ L₃ L₄ h
  exact H ((genPos_agree _ _ _ _).mp h)

theorem br_6 : blind6_stmt → (type_of% @QuadNewton.orthocentre_line_perp) := by
  intro H L₁ L₂ L₃ L₄ h
  exact H (toB L₁) (toB L₂) (toB L₃) (toB L₄) ((genPos_agree _ _ _ _).mpr h)

end Blind
