import Mathlib

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

/-! ## The diagonals and the orthocentres -/
section Diagonals

-- thm:newton (part 1). If L₁,…,L₄ are in general position, the midpoints of the three diagonals
-- are collinear.
theorem blind_1 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    Collinear ℝ ({BlindM1 L₁ L₂ L₃ L₄, BlindM2 L₁ L₂ L₃ L₄, BlindM3 L₁ L₂ L₃ L₄} : Set ℂ) := by
  sorry

-- thm:newton (part 2). … and the midpoints of A₁₂A₃₄ and A₁₃A₂₄ are distinct.
theorem blind_2 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    BlindM1 L₁ L₂ L₃ L₄ ≠ BlindM2 L₁ L₂ L₃ L₄ := by
  sorry

-- thm:ortho (part 1). If L₁,…,L₄ are in general position, the orthocentres H₁,…,H₄ of T₁,…,T₄
-- are collinear.
theorem blind_3 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    Collinear ℝ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
      BlindH4 L₁ L₂ L₃ L₄} : Set ℂ) := by
  sorry

-- thm:ortho (part 2). … and they are not all equal: H₃ ≠ H₄ or H₂ ≠ H₄.
theorem blind_4 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    BlindH3 L₁ L₂ L₃ L₄ ≠ BlindH4 L₁ L₂ L₃ L₄ ∨ BlindH2 L₁ L₂ L₃ L₄ ≠ BlindH4 L₁ L₂ L₃ L₄ := by
  sorry

-- thm:boden. If L₁,…,L₄ are in general position, each orthocentre H_k has the same power with
-- respect to the three circles having the diagonals as diameters.
theorem blind_5 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    ∀ H ∈ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
        BlindH4 L₁ L₂ L₃ L₄} : Set ℂ),
      BlindPw H (BlindA12 L₁ L₂ L₃ L₄) (BlindA34 L₁ L₂ L₃ L₄) =
        BlindPw H (BlindA13 L₁ L₂ L₃ L₄) (BlindA24 L₁ L₂ L₃ L₄) ∧
      BlindPw H (BlindA13 L₁ L₂ L₃ L₄) (BlindA24 L₁ L₂ L₃ L₄) =
        BlindPw H (BlindA14 L₁ L₂ L₃ L₄) (BlindA23 L₁ L₂ L₃ L₄) := by
  sorry

-- thm:perp. If L₁,…,L₄ are in general position, then for any two orthocentres H, H′,
-- Re((m₂ - m₁) · conj(H′ - H)) = 0, where m₁, m₂ are the midpoints of A₁₂A₃₄ and A₁₃A₂₄.
theorem blind_6 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    ∀ H ∈ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
        BlindH4 L₁ L₂ L₃ L₄} : Set ℂ),
    ∀ H' ∈ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
        BlindH4 L₁ L₂ L₃ L₄} : Set ℂ),
      ((BlindM2 L₁ L₂ L₃ L₄ - BlindM1 L₁ L₂ L₃ L₄) * starRingEnd ℂ (H' - H)).re = 0 := by
  sorry

end Diagonals

/-! ## The circles -/
section Circles

-- thm:miquel. If L₁,…,L₄ are in general position, M lies on the circumcircle of each of
-- T₁,…,T₄.
theorem blind_7 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    BlindMiquel L₁ L₂ L₃ L₄ ∈ BlindCircumcircle (BlindT1 L₁ L₂ L₃ L₄) ∧
    BlindMiquel L₁ L₂ L₃ L₄ ∈ BlindCircumcircle (BlindT2 L₁ L₂ L₃ L₄) ∧
    BlindMiquel L₁ L₂ L₃ L₄ ∈ BlindCircumcircle (BlindT3 L₁ L₂ L₃ L₄) ∧
    BlindMiquel L₁ L₂ L₃ L₄ ∈ BlindCircumcircle (BlindT4 L₁ L₂ L₃ L₄) := by
  sorry

-- thm:steiner. If L₁,…,L₄ are in general position, the four circumcentres circ(T₁),…,circ(T₄)
-- and M are cospherical (lie on one circle).
theorem blind_8 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    EuclideanGeometry.Cospherical
      ({BlindTriCirc (BlindT1 L₁ L₂ L₃ L₄), BlindTriCirc (BlindT2 L₁ L₂ L₃ L₄),
        BlindTriCirc (BlindT3 L₁ L₂ L₃ L₄), BlindTriCirc (BlindT4 L₁ L₂ L₃ L₄),
        BlindMiquel L₁ L₂ L₃ L₄} : Set ℂ) := by
  sorry

-- thm:simson. If L₁,…,L₄ are in general position, the feet of the perpendiculars from M to
-- L₁,…,L₄ are collinear.
theorem blind_9 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    Collinear ℝ ({BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₁, BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₂,
      BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₃, BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₄} : Set ℂ) := by
  sorry

-- thm:par. If L₁,…,L₄ are in general position, with F_k the foot of the perpendicular from M to
-- L_k, the line through F₁ and F₂ is parallel to the affine span of the four orthocentres.
theorem blind_10 (L₁ L₂ L₃ L₄ : BlindLine) (h : BlindGenPos L₁ L₂ L₃ L₄) :
    (line[ℝ, BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₁, BlindFoot (BlindMiquel L₁ L₂ L₃ L₄) L₂]).Parallel
      (affineSpan ℝ ({BlindH1 L₁ L₂ L₃ L₄, BlindH2 L₁ L₂ L₃ L₄, BlindH3 L₁ L₂ L₃ L₄,
        BlindH4 L₁ L₂ L₃ L₄} : Set ℂ)) := by
  sorry

end Circles

end Blind
