import QuadMiquel

/-! L13 comparer: blind_7..blind_10 vs QuadMiquel.miquel / steiner_circle / simson /
steiner_parallel_line. Blind definitions copied verbatim from scratch/PaperEBlind.lean
(namespace `Blind`, sorry'd theorems replaced by `blindK_stmt : Prop`). -/

open Complex

noncomputable section

namespace Blind

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

/-- The Miquel point, by the explicit formula. -/
def BlindMiquel (L₁ L₂ L₃ L₄ : BlindLine) : ℂ :=
  BlindA12 L₁ L₂ L₃ L₄ +
    ((BlindA13 L₁ L₂ L₃ L₄ - BlindA12 L₁ L₂ L₃ L₄) * (BlindA24 L₁ L₂ L₃ L₄ - BlindA12 L₁ L₂ L₃ L₄)
      - (BlindA23 L₁ L₂ L₃ L₄ - BlindA12 L₁ L₂ L₃ L₄) * (BlindA14 L₁ L₂ L₃ L₄ - BlindA12 L₁ L₂ L₃ L₄)) /
    (BlindA13 L₁ L₂ L₃ L₄ + BlindA24 L₁ L₂ L₃ L₄ - BlindA23 L₁ L₂ L₃ L₄ - BlindA14 L₁ L₂ L₃ L₄)

/-! ## Blind statements as Props (verbatim conclusions) -/

-- thm:miquel
def blind7_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    BlindMiquel L₁ L₂ L₃ L₄ ∈ BlindCircumcircle (BlindT1 L₁ L₂ L₃ L₄) ∧
    BlindMiquel L₁ L₂ L₃ L₄ ∈ BlindCircumcircle (BlindT2 L₁ L₂ L₃ L₄) ∧
    BlindMiquel L₁ L₂ L₃ L₄ ∈ BlindCircumcircle (BlindT3 L₁ L₂ L₃ L₄) ∧
    BlindMiquel L₁ L₂ L₃ L₄ ∈ BlindCircumcircle (BlindT4 L₁ L₂ L₃ L₄)

-- thm:steiner
def blind8_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    EuclideanGeometry.Cospherical
      ({BlindTriCirc (BlindT1 L₁ L₂ L₃ L₄), BlindTriCirc (BlindT2 L₁ L₂ L₃ L₄),
        BlindTriCirc (BlindT3 L₁ L₂ L₃ L₄), BlindTriCirc (BlindT4 L₁ L₂ L₃ L₄),
        BlindMiquel L₁ L₂ L₃ L₄} : Set ℂ)

-- thm:simson
def blind9_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    Collinear ℝ ({BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₁, BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₂,
      BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₃, BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₄} : Set ℂ)

-- thm:par
def blind10_stmt : Prop := ∀ (L₁ L₂ L₃ L₄ : BlindLine), BlindGenPos L₁ L₂ L₃ L₄ →
    (line[ℝ, BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₁, BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₂]).Parallel
      (affineSpan ℝ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
        BlindH4 L₁ L₂ L₃ L₄} : Set ℂ))

/-! ## Translation and definitional agreement lemmas (all `rfl`) -/

open QuadMiquel

def toL (L : BlindLine) : QuadMiquel.Line := ⟨L.p, L.d⟩
def ofL (L : QuadMiquel.Line) : BlindLine := ⟨L.p, L.d⟩

theorem toL_ofL (L : QuadMiquel.Line) : toL (ofL L) = L := rfl

theorem cr_agree (a b : ℂ) : BlindCr a b = QuadMiquel.cr a b := rfl
theorem carrier_agree (L : BlindLine) : L.carrier = (toL L).carrier := rfl
theorem meet_agree (L M : BlindLine) : BlindMeet L M = QuadMiquel.meet (toL L) (toL M) := rfl
theorem circ_agree (a b c : ℂ) : BlindCirc a b c = QuadMiquel.circ a b c := rfl
theorem ortho_agree (a b c : ℂ) : BlindOrtho a b c = QuadMiquel.ortho a b c := rfl
theorem foot_agree (z : ℂ) (L : BlindLine) : BlindFoot z L = QuadMiquel.foot z (toL L) := rfl
theorem miquel_agree (L₁ L₂ L₃ L₄ : BlindLine) :
    BlindMiquel L₁ L₂ L₃ L₄ = miquelPt (toL L₁) (toL L₂) (toL L₃) (toL L₄) := rfl
/-- Same radius convention as the real `miquel`: centre `circ T`, through the FIRST vertex. -/
theorem circumcircle_agree (a b c : ℂ) :
    BlindCircumcircle (a, b, c) = Metric.sphere (QuadMiquel.circ a b c) (dist a (QuadMiquel.circ a b c)) :=
  rfl

/-- `BlindGenPos` (a conjunction) ↔ `GenPos` (a structure), field by field. -/
theorem genPos_agree (L₁ L₂ L₃ L₄ : BlindLine) :
    BlindGenPos L₁ L₂ L₃ L₄ ↔ GenPos (toL L₁) (toL L₂) (toL L₃) (toL L₄) := by
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

/-! ## Pair 7: blind_7 ↔ QuadMiquel.miquel -/

theorem rb_7 : (type_of% @QuadMiquel.miquel) → blind7_stmt := by
  intro H L₁ L₂ L₃ L₄ h
  exact H ((genPos_agree L₁ L₂ L₃ L₄).1 h)

theorem br_7 : blind7_stmt → (type_of% @QuadMiquel.miquel) := by
  intro H L₁ L₂ L₃ L₄ h
  exact H (ofL L₁) (ofL L₂) (ofL L₃) (ofL L₄) ((genPos_agree _ _ _ _).2 h)

/-! ## Pair 8: blind_8 ↔ QuadMiquel.steiner_circle -/

theorem rb_8 : (type_of% @QuadMiquel.steiner_circle) → blind8_stmt := by
  intro H L₁ L₂ L₃ L₄ h
  exact H ((genPos_agree L₁ L₂ L₃ L₄).1 h)

theorem br_8 : blind8_stmt → (type_of% @QuadMiquel.steiner_circle) := by
  intro H L₁ L₂ L₃ L₄ h
  exact H (ofL L₁) (ofL L₂) (ofL L₃) (ofL L₄) ((genPos_agree _ _ _ _).2 h)

/-! ## Pair 9: blind_9 ↔ QuadMiquel.simson -/

theorem rb_9 : (type_of% @QuadMiquel.simson) → blind9_stmt := by
  intro H L₁ L₂ L₃ L₄ h
  rw [miquel_agree, foot_agree, foot_agree, foot_agree, foot_agree]
  exact H ((genPos_agree L₁ L₂ L₃ L₄).1 h)

theorem br_9 : blind9_stmt → (type_of% @QuadMiquel.simson) := by
  intro H L₁ L₂ L₃ L₄ h
  have := H (ofL L₁) (ofL L₂) (ofL L₃) (ofL L₄) ((genPos_agree _ _ _ _).2 h)
  rw [miquel_agree, foot_agree, foot_agree, foot_agree, foot_agree] at this
  simp only [toL_ofL] at this
  exact this

/-! ## Pair 10: blind_10 ↔ QuadMiquel.steiner_parallel_line -/

theorem rb_10 : (type_of% @QuadMiquel.steiner_parallel_line) → blind10_stmt := by
  intro H L₁ L₂ L₃ L₄ h
  simp only [BlindH1, BlindH2, BlindH3, BlindH4, BlindTriOrtho, BlindT1, BlindT2, BlindT3, BlindT4,
    BlindA12, BlindA13, BlindA14, BlindA23, BlindA24, BlindA34, ortho_agree, meet_agree,
    miquel_agree, foot_agree]
  exact H ((genPos_agree L₁ L₂ L₃ L₄).1 h)

theorem br_10 : blind10_stmt → (type_of% @QuadMiquel.steiner_parallel_line) := by
  intro H L₁ L₂ L₃ L₄ h
  have := H (ofL L₁) (ofL L₂) (ofL L₃) (ofL L₄) ((genPos_agree _ _ _ _).2 h)
  simp only [BlindH1, BlindH2, BlindH3, BlindH4, BlindTriOrtho, BlindT1, BlindT2, BlindT3, BlindT4,
    BlindA12, BlindA13, BlindA14, BlindA23, BlindA24, BlindA34, ortho_agree, meet_agree,
    miquel_agree, foot_agree, toL_ofL] at this
  exact this

end Blind
