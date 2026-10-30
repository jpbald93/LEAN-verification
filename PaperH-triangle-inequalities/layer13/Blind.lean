import Mathlib

/-!
Blind formalisation (Layer 13) of the theorem statements of the paper `paperh_blind.txt`.
Conventions (Section "Setting"): `A = t.points 0`, `B = t.points 1`, `C = t.points 2`,
`a = |BC|`, `b = |CA|`, `c = |AB|`, `O` circumcentre, `I` incentre, `G` centroid,
`H` orthocentre, `R` circumradius, `r` inradius.
-/

open EuclideanGeometry Real

noncomputable section

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Semiperimeter `s = (a+b+c)/2`. -/
def BlindSemiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
    dist (t.points 0) (t.points 1)) / 2

/-- Area `Δ = ½ |AB| |AC| sin ∠BAC`. -/
def BlindArea (t : Affine.Triangle ℝ P) : ℝ :=
  1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
    Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))

/-- Heron's polynomial `Γ(a,b,c) = ¼(2a²b²+2b²c²+2c²a²-a⁴-b⁴-c⁴)` (auxiliary definition). -/
def BlindHeronGamma (a b c : ℝ) : ℝ :=
  1 / 4 * (2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4)

/-- "Equilateral" is `|AB| = |BC| ∧ |BC| = |CA|`. -/
def BlindEquilateral (t : Affine.Triangle ℝ P) : Prop :=
  dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
    dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)

/-- `X` is in the closed triangle: `X = w₀A + w₁B + w₂C` with all `wᵢ ≥ 0`, `∑ wᵢ = 1`. -/
def BlindInClosedTriangle (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- `X` is strictly inside the triangle: as above with all `wᵢ > 0`. -/
def BlindStrictlyInside (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- Distance from `X` to the line `YZ`: `|X π_{YZ}(X)|`, `π_{YZ}` the orthogonal projection. -/
def BlindDistToLine (X Y Z : P) : ℝ :=
  dist X (EuclideanGeometry.orthogonalProjection line[ℝ, Y, Z] X : P)

/-! ### Oriented plane setting (Section "Fermat and Napoleon") -/

section Oriented

variable [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Orientation sign `σ ∈ {1,-1}` of `t`: `σ = 1` iff `ω(B-A, C-A) > 0`. -/
def BlindOrientationSign (t : Affine.Triangle ℝ P) : ℝ :=
  if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then 1 else -1

/-- Outer apex on `XY`: the image of `Y` under the rotation about `X` by `-σπ/3`. -/
def BlindOuterApex (t : Affine.Triangle ℝ P) (X Y : P) : P :=
  o.rotation ((-(BlindOrientationSign o t * π / 3) : ℝ) : Real.Angle) (Y -ᵥ X) +ᵥ X

/-- `A'`: outer apex on `BC`. -/
def BlindApexA (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 1) (t.points 2)
/-- `B'`: outer apex on `CA`. -/
def BlindApexB (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 2) (t.points 0)
/-- `C'`: outer apex on `AB`. -/
def BlindApexC (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 0) (t.points 1)

/-- `N_A`: centroid of `B C A'`. -/
def BlindNapoleonA (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 1, t.points 2, BlindApexA o t]
/-- `N_B`: centroid of `C A B'`. -/
def BlindNapoleonB (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 2, t.points 0, BlindApexB o t]
/-- `N_C`: centroid of `A B C'`. -/
def BlindNapoleonC (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 0, t.points 1, BlindApexC o t]

end Oriented

/-! ### The Euler family -/

-- thm:euler — For every triangle, |IO|^2 = R^2 - 2Rr.
theorem blind_1 (t : Affine.Triangle ℝ P) :
    dist t.incenter t.circumcenter ^ 2 =
      t.circumradius ^ 2 - 2 * t.circumradius * t.inradius := by sorry

-- thm:eulerineq — For every triangle, 2r ≤ R; (part 1: inequality)
theorem blind_2 (t : Affine.Triangle ℝ P) : 2 * t.inradius ≤ t.circumradius := by sorry

-- thm:eulerineq — For every triangle, 2r ≤ R; and 2r = R iff equilateral (part 2: equality case)
theorem blind_3 (t : Affine.Triangle ℝ P) :
    2 * t.inradius = t.circumradius ↔ BlindEquilateral t := by sorry

-- thm:eulerex — (body redacted; reconstructed from the proof) |I_i O|^2 = R^2 + 2 R r_i,
-- where I_i, r_i are the excentre/exradius of the excircle opposite vertex i. (vertex 0 = A)
theorem blind_4 (t : Affine.Triangle ℝ P) :
    dist (t.excenter {0}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {0} := by sorry

-- thm:eulerex — (vertex 1 = B)
theorem blind_5 (t : Affine.Triangle ℝ P) :
    dist (t.excenter {1}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {1} := by sorry

-- thm:eulerex — (vertex 2 = C)
theorem blind_6 (t : Affine.Triangle ℝ P) :
    dist (t.excenter {2}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {2} := by sorry

-- thm:ogh — For every triangle, |OG|^2 = R^2 - (a^2+b^2+c^2)/9, ... (part OG)
theorem blind_7 (t : Affine.Triangle ℝ P) :
    dist t.circumcenter (Finset.univ.centroid ℝ t.points) ^ 2 =
      t.circumradius ^ 2 - 1 / 9 * (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) := by sorry

-- thm:ogh — For every triangle, ... |OH|^2 = 9R^2 - (a^2+b^2+c^2) ... (part OH)
theorem blind_8 (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.orthocenter ^ 2 =
      9 * t.circumradius ^ 2 - (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) := by sorry

-- thm:ogh — For every triangle, ... |IG|^2 = (s^2 + 5r^2 - 16Rr)/9. (part IG)
theorem blind_9 (t : Affine.Triangle ℝ P) :
    dist t.incenter (Finset.univ.centroid ℝ t.points) ^ 2 =
      1 / 9 * (BlindSemiperimeter t ^ 2 + 5 * t.inradius ^ 2 -
        16 * t.circumradius * t.inradius) := by sorry

/-! ### Inequalities in R, r, s -/

-- thm:quartic — For every triangle, s^4 - 2(2R^2+10Rr-r^2)s^2 + r(4R+r)^3 ≤ 0.
theorem blind_10 (t : Affine.Triangle ℝ P) :
    BlindSemiperimeter t ^ 4 -
      2 * (2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2) *
        BlindSemiperimeter t ^ 2 +
      t.inradius * (4 * t.circumradius + t.inradius) ^ 3 ≤ 0 := by sorry

-- thm:gerretsen — For every triangle, 16Rr - 5r^2 ≤ s^2 ≤ 4R^2+4Rr+3r^2. (lower bound)
theorem blind_11 (t : Affine.Triangle ℝ P) :
    16 * t.circumradius * t.inradius - 5 * t.inradius ^ 2 ≤ BlindSemiperimeter t ^ 2 := by sorry

-- thm:gerretsen — For every triangle, 16Rr - 5r^2 ≤ s^2 ≤ 4R^2+4Rr+3r^2. (upper bound)
theorem blind_12 (t : Affine.Triangle ℝ P) :
    BlindSemiperimeter t ^ 2 ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2 := by sorry

-- thm:gerretsen — Moreover (R-r)(R-2r) ≥ 0.
theorem blind_13 (t : Affine.Triangle ℝ P) :
    0 ≤ (t.circumradius - t.inradius) * (t.circumradius - 2 * t.inradius) := by sorry

-- thm:kooi — For every triangle, s^2 ≤ R(4R+r)^2/(2(2R-r)) ... (Kooi's inequality)
theorem blind_14 (t : Affine.Triangle ℝ P) :
    BlindSemiperimeter t ^ 2 ≤
      t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius)) := by sorry

-- thm:kooi — ... and R(4R+r)^2/(2(2R-r)) ≤ 4R^2+4Rr+3r^2. (comparison with Gerretsen)
theorem blind_15 (t : Affine.Triangle ℝ P) :
    t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius)) ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2 := by sorry

/-! ### Area inequalities and extremal problems -/

-- thm:weitz — For every triangle, 4√3 Δ ≤ a^2+b^2+c^2, ... (inequality)
theorem blind_16 (t : Affine.Triangle ℝ P) :
    4 * √3 * BlindArea t ≤ dist (t.points 1) (t.points 2) ^ 2 +
      dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 := by sorry

-- thm:weitz — ... with equality if and only if the triangle is equilateral.
theorem blind_17 (t : Affine.Triangle ℝ P) :
    4 * √3 * BlindArea t = dist (t.points 1) (t.points 2) ^ 2 +
      dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 ↔
      BlindEquilateral t := by sorry

-- thm:hf — For every triangle, 4√3Δ + (a-b)^2+(b-c)^2+(c-a)^2 ≤ a^2+b^2+c^2, ... (inequality)
theorem blind_18 (t : Affine.Triangle ℝ P) :
    4 * √3 * BlindArea t +
        (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
        (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 +
        (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 ≤
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2 := by sorry

-- thm:hf — ... with equality if and only if the triangle is equilateral.
theorem blind_19 (t : Affine.Triangle ℝ P) :
    4 * √3 * BlindArea t +
        (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
        (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 +
        (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 =
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2 ↔ BlindEquilateral t := by sorry

-- thm:iso — For every triangle, 12√3 Δ ≤ (a+b+c)^2, ... (inequality)
theorem blind_20 (t : Affine.Triangle ℝ P) :
    12 * √3 * BlindArea t ≤ (dist (t.points 1) (t.points 2) +
      dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) ^ 2 := by sorry

-- thm:iso — ... with equality if and only if the triangle is equilateral.
theorem blind_21 (t : Affine.Triangle ℝ P) :
    12 * √3 * BlindArea t = (dist (t.points 1) (t.points 2) +
      dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) ^ 2 ↔
      BlindEquilateral t := by sorry

-- thm:leibniz — For every triangle and every point X of the space,
-- |XA|^2+|XB|^2+|XC|^2 = 3|XG|^2 + (a^2+b^2+c^2)/3; (relation)
theorem blind_22 (t : Affine.Triangle ℝ P) (X : P) :
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 =
      3 * dist X (Finset.univ.centroid ℝ t.points) ^ 2 +
        1 / 3 * (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2) := by sorry

-- thm:leibniz — ... hence |XA|^2+|XB|^2+|XC|^2 ≥ (a^2+b^2+c^2)/3, (minimum)
theorem blind_23 (t : Affine.Triangle ℝ P) (X : P) :
    1 / 3 * (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2) ≤
      dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 := by sorry

-- thm:leibniz — ... with equality if and only if X = G.
theorem blind_24 (t : Affine.Triangle ℝ P) (X : P) :
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 =
        1 / 3 * (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2) ↔
      X = Finset.univ.centroid ℝ t.points := by sorry

/-! ### Two triangles: Neuberg–Pedoe -/

section Pedoe

variable {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [MetricSpace P']
  [NormedAddTorsor V' P']

-- thm:pedoe — Let t and t' be triangles, possibly in different real inner product spaces, with
-- sides a,b,c and a',b',c' and areas Δ, Δ'. Then a'^2(b^2+c^2-a^2)+... ≥ 16ΔΔ', (inequality)
theorem blind_25 (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    16 * BlindArea t * BlindArea t' ≤
      dist (t'.points 1) (t'.points 2) ^ 2 *
          (dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 -
            dist (t.points 1) (t.points 2) ^ 2) +
        dist (t'.points 2) (t'.points 0) ^ 2 *
          (dist (t.points 0) (t.points 1) ^ 2 + dist (t.points 1) (t.points 2) ^ 2 -
            dist (t.points 2) (t.points 0) ^ 2) +
        dist (t'.points 0) (t'.points 1) ^ 2 *
          (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 -
            dist (t.points 0) (t.points 1) ^ 2) := by sorry

-- thm:pedoe — ... with equality if and only if there is k > 0 with a' = ka, b' = kb, c' = kc.
theorem blind_26 (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    dist (t'.points 1) (t'.points 2) ^ 2 *
          (dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 -
            dist (t.points 1) (t.points 2) ^ 2) +
        dist (t'.points 2) (t'.points 0) ^ 2 *
          (dist (t.points 0) (t.points 1) ^ 2 + dist (t.points 1) (t.points 2) ^ 2 -
            dist (t.points 2) (t.points 0) ^ 2) +
        dist (t'.points 0) (t'.points 1) ^ 2 *
          (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 -
            dist (t.points 0) (t.points 1) ^ 2) = 16 * BlindArea t * BlindArea t' ↔
      ∃ k : ℝ, 0 < k ∧
        dist (t'.points 1) (t'.points 2) = k * dist (t.points 1) (t.points 2) ∧
        dist (t'.points 2) (t'.points 0) = k * dist (t.points 2) (t.points 0) ∧
        dist (t'.points 0) (t'.points 1) = k * dist (t.points 0) (t.points 1) := by sorry

end Pedoe

/-! ### Ptolemy -/

-- thm:ptolemy — For any four points A,B,C,D of P, |AC||BD| ≤ |AB||CD| + |BC||AD|.
theorem blind_27 (A B C D : P) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D := by sorry

-- thm:ptolemyeq — Let A,B,C,D be four pairwise distinct points of P (six hypotheses).
-- Then |AC||BD| = |AB||CD| + |BC||AD| iff one of the following holds: (items redacted;
-- reconstructed from abstract/proof) (a) A,B,C,D cospherical and the diagonals AC, BD cross;
-- (b) A,B,C,D collinear in one of eight orders.
-- AMBIGUOUS: item (a) might additionally state non-collinearity, and "crossing" might be stated
-- with weak betweenness (Wbtw); item (b)'s "eight orders" are rendered as the eight linear
-- sequences that are cyclic rotations of ABCD or DCBA, each as a chain of strict betweenness.
theorem blind_28 (A B C D : P) (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) :
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D ↔
      (Cospherical ({A, B, C, D} : Set P) ∧ ∃ X : P, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
      (Collinear ℝ ({A, B, C, D} : Set P) ∧
        ((Sbtw ℝ A B C ∧ Sbtw ℝ B C D) ∨ (Sbtw ℝ B C D ∧ Sbtw ℝ C D A) ∨
          (Sbtw ℝ C D A ∧ Sbtw ℝ D A B) ∨ (Sbtw ℝ D A B ∧ Sbtw ℝ A B C) ∨
          (Sbtw ℝ D C B ∧ Sbtw ℝ C B A) ∨ (Sbtw ℝ A D C ∧ Sbtw ℝ D C B) ∨
          (Sbtw ℝ B A D ∧ Sbtw ℝ A D C) ∨ (Sbtw ℝ C B A ∧ Sbtw ℝ B A D))) := by sorry

/-! ### Erdős–Mordell and Barrow -/

-- thm:key — For every triangle and every X in the closed triangle, b d_C(X) + c d_B(X) ≤ a|XA|, ...
theorem blind_29 (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X) :
    dist (t.points 2) (t.points 0) * BlindDistToLine X (t.points 0) (t.points 1) +
        dist (t.points 0) (t.points 1) * BlindDistToLine X (t.points 2) (t.points 0) ≤
      dist (t.points 1) (t.points 2) * dist X (t.points 0) := by sorry

-- thm:key — ... c d_A(X) + a d_C(X) ≤ b|XB|, ...
theorem blind_30 (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X) :
    dist (t.points 0) (t.points 1) * BlindDistToLine X (t.points 1) (t.points 2) +
        dist (t.points 1) (t.points 2) * BlindDistToLine X (t.points 0) (t.points 1) ≤
      dist (t.points 2) (t.points 0) * dist X (t.points 1) := by sorry

-- thm:key — ... a d_B(X) + b d_A(X) ≤ c|XC|.
theorem blind_31 (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X) :
    dist (t.points 1) (t.points 2) * BlindDistToLine X (t.points 2) (t.points 0) +
        dist (t.points 2) (t.points 0) * BlindDistToLine X (t.points 1) (t.points 2) ≤
      dist (t.points 0) (t.points 1) * dist X (t.points 2) := by sorry

-- thm:em — For every triangle and every X in the closed triangle,
-- 2(d_A(X)+d_B(X)+d_C(X)) ≤ |XA|+|XB|+|XC|, (inequality)
theorem blind_32 (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X) :
    2 * (BlindDistToLine X (t.points 1) (t.points 2) +
        BlindDistToLine X (t.points 2) (t.points 0) +
        BlindDistToLine X (t.points 0) (t.points 1)) ≤
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by sorry

-- thm:em — (equality case; text partly redacted) equality iff the triangle is equilateral and
-- X is the centroid.
theorem blind_33 (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X) :
    2 * (BlindDistToLine X (t.points 1) (t.points 2) +
        BlindDistToLine X (t.points 2) (t.points 0) +
        BlindDistToLine X (t.points 0) (t.points 1)) =
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) ↔
      BlindEquilateral t ∧ X = Finset.univ.centroid ℝ t.points := by sorry

-- thm:barrow — Let X be strictly inside the triangle (all three weights positive), and let U, V', W
-- be points with U weakly between B and C, V' weakly between C and A, W weakly between A and B
-- (and, redacted, on the internal bisectors of ∠BXC, ∠CXA, ∠AXB). Then
-- 2(|XU|+|XV'|+|XW|) ≤ |XA|+|XB|+|XC|.
-- AMBIGUOUS: the redacted bisector hypotheses are rendered as equal angles ∠BXU = ∠UXC etc.
theorem blind_34 (t : Affine.Triangle ℝ P) (X U V' W : P) (hX : BlindStrictlyInside t X)
    (hU : Wbtw ℝ (t.points 1) U (t.points 2)) (hV : Wbtw ℝ (t.points 2) V' (t.points 0))
    (hW : Wbtw ℝ (t.points 0) W (t.points 1))
    (hUa : ∠ (t.points 1) X U = ∠ U X (t.points 2))
    (hVa : ∠ (t.points 2) X V' = ∠ V' X (t.points 0))
    (hWa : ∠ (t.points 0) X W = ∠ W X (t.points 1)) :
    2 * (dist X U + dist X V' + dist X W) ≤
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by sorry

/-! ### Fermat–Torricelli -/

-- thm:fermatmin — Let A,B,C,F be points of P with ∠AFB = ∠BFC = ∠CFA = 2π/3. Then for every
-- X ∈ P, |FA|+|FB|+|FC| ≤ |XA|+|XB|+|XC|.
theorem blind_35 (A B C F : P) (h1 : ∠ A F B = 2 * π / 3) (h2 : ∠ B F C = 2 * π / 3)
    (h3 : ∠ C F A = 2 * π / 3) (X : P) :
    dist F A + dist F B + dist F C ≤ dist X A + dist X B + dist X C := by sorry

-- thm:fermat — Let t be a triangle whose three angles ∠BAC, ∠CBA, ∠ACB are all less than 2π/3.
-- Then there is F ∈ P with ∠AFB = ∠BFC = ∠CFA = 2π/3, and for every X, |FA|+|FB|+|FC| ≤ ...
theorem blind_36 (t : Affine.Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) :
    ∃ F : P, ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧ ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
      ∀ X : P, dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2) ≤
        dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by sorry

/-! ### Fermat–Napoleon lines and Napoleon (oriented plane, dim V = 2) -/

section Napoleon

variable [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

-- thm:fn (o) — for each vertex i, the vertex t_i and the apex on the opposite side lie strictly on
-- opposite sides of the line through the other two vertices. (vertex A)
-- AMBIGUOUS: the end of item (o) is redacted; "opposite sides of the opposite side line" is our
-- reading of "lie strictly on ...".
theorem blind_37 (t : Affine.Triangle ℝ P) :
    (line[ℝ, t.points 1, t.points 2]).SOppSide (t.points 0) (BlindApexA o t) := by sorry

-- thm:fn (o) — (vertex B)
theorem blind_38 (t : Affine.Triangle ℝ P) :
    (line[ℝ, t.points 2, t.points 0]).SOppSide (t.points 1) (BlindApexB o t) := by sorry

-- thm:fn (o) — (vertex C)
theorem blind_39 (t : Affine.Triangle ℝ P) :
    (line[ℝ, t.points 0, t.points 1]).SOppSide (t.points 2) (BlindApexC o t) := by sorry

-- thm:fn (i) — (redacted; from abstract) the segments AA', BB', CC' have equal lengths. |AA'|=|BB'|
theorem blind_40 (t : Affine.Triangle ℝ P) :
    dist (t.points 0) (BlindApexA o t) = dist (t.points 1) (BlindApexB o t) := by sorry

-- thm:fn (i) — |BB'| = |CC'|
theorem blind_41 (t : Affine.Triangle ℝ P) :
    dist (t.points 1) (BlindApexB o t) = dist (t.points 2) (BlindApexC o t) := by sorry

-- thm:fn (ii) — (redacted; from abstract/proof) the lines AA', BB', CC' are concurrent.
theorem blind_42 (t : Affine.Triangle ℝ P) :
    ∃ F : P, F ∈ line[ℝ, t.points 0, BlindApexA o t] ∧ F ∈ line[ℝ, t.points 1, BlindApexB o t] ∧
      F ∈ line[ℝ, t.points 2, BlindApexC o t] := by sorry

-- thm:fn (iii) — (redacted; from remarks/proof) if every angle is < 2π/3, any F on the lines AA'
-- and BB' satisfies ∠AFB = ∠BFC = ∠CFA = 2π/3 (it is the Fermat point). (angles)
theorem blind_43 (t : Affine.Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) (F : P)
    (hFA : F ∈ line[ℝ, t.points 0, BlindApexA o t]) (hFB : F ∈ line[ℝ, t.points 1, BlindApexB o t]) :
    ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧ ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
      ∠ (t.points 2) F (t.points 0) = 2 * π / 3 := by sorry

-- thm:fn (iii) — ... and |AA'| = |FA|+|FB|+|FC|. (length)
theorem blind_44 (t : Affine.Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) (F : P)
    (hFA : F ∈ line[ℝ, t.points 0, BlindApexA o t]) (hFB : F ∈ line[ℝ, t.points 1, BlindApexB o t]) :
    dist (t.points 0) (BlindApexA o t) =
      dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2) := by sorry

-- thm:fn (iv) — (redacted; from abstract/proof) the lines meet pairwise at angle π/3: the vectors
-- A'-A, B'-B make the angle 2π/3 (so the unoriented lines AA', BB' meet at π/3).
-- AMBIGUOUS: (iv) might be stated directly as a line angle π/3 (min(θ, π-θ) = π/3).
theorem blind_45 (t : Affine.Triangle ℝ P) :
    InnerProductGeometry.angle (BlindApexA o t -ᵥ t.points 0) (BlindApexB o t -ᵥ t.points 1) =
      2 * π / 3 := by sorry

-- thm:fn (iv) — (pair B, C)
theorem blind_46 (t : Affine.Triangle ℝ P) :
    InnerProductGeometry.angle (BlindApexB o t -ᵥ t.points 1) (BlindApexC o t -ᵥ t.points 2) =
      2 * π / 3 := by sorry

-- thm:fn (iv) — (pair C, A)
theorem blind_47 (t : Affine.Triangle ℝ P) :
    InnerProductGeometry.angle (BlindApexC o t -ᵥ t.points 2) (BlindApexA o t -ᵥ t.points 0) =
      2 * π / 3 := by sorry

-- thm:napoleon — In the setting above, |N_AN_B| = |N_BN_C| = |N_CN_A|, ... (|N_AN_B| = |N_BN_C|)
theorem blind_48 (t : Affine.Triangle ℝ P) :
    dist (BlindNapoleonA o t) (BlindNapoleonB o t) =
      dist (BlindNapoleonB o t) (BlindNapoleonC o t) := by sorry

-- thm:napoleon — ... (|N_BN_C| = |N_CN_A|)
theorem blind_49 (t : Affine.Triangle ℝ P) :
    dist (BlindNapoleonB o t) (BlindNapoleonC o t) =
      dist (BlindNapoleonC o t) (BlindNapoleonA o t) := by sorry

-- thm:napoleon — ... and the centroid of N_A, N_B, N_C is the centroid G of t.
theorem blind_50 (t : Affine.Triangle ℝ P) :
    Finset.univ.centroid ℝ ![BlindNapoleonA o t, BlindNapoleonB o t, BlindNapoleonC o t] =
      Finset.univ.centroid ℝ t.points := by sorry

end Napoleon

end
