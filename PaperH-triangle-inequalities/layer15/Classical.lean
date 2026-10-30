import Mathlib

/-!
# Paper H — classical statements (blind formalisation)

Conventions: for `t : Affine.Triangle ℝ P`, `A = t.points 0`, `B = t.points 1`,
`C = t.points 2`; `a = BC`, `b = CA`, `c = AB`.  Non-degeneracy is built into
`Affine.Triangle` (affinely independent vertices).
-/

open EuclideanGeometry Real

noncomputable section

namespace PaperHClassical

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## Definitions not (directly) in Mathlib -/

/-- Side `a = BC`. -/
def ClassicalSideA (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 1) (t.points 2)
/-- Side `b = CA`. -/
def ClassicalSideB (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 2) (t.points 0)
/-- Side `c = AB`. -/
def ClassicalSideC (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 0) (t.points 1)

/-- Semiperimeter `s = (a+b+c)/2`. -/
def ClassicalSemiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (ClassicalSideA t + ClassicalSideB t + ClassicalSideC t) / 2

/-- Area of the triangle with vertices `A B C`: `Δ = ½·AB·AC·sin A`. -/
def ClassicalAreaPts (A B C : P) : ℝ :=
  1 / 2 * dist A B * dist A C * Real.sin (∠ B A C)

/-- Area `Δ` of a triangle. -/
def ClassicalArea (t : Affine.Triangle ℝ P) : ℝ :=
  ClassicalAreaPts (t.points 0) (t.points 1) (t.points 2)

/-- Centroid `G`. -/
def ClassicalCentroid (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ t.points

/-- Equilateral: `a = b = c`. -/
def ClassicalEquilateral (t : Affine.Triangle ℝ P) : Prop :=
  ClassicalSideA t = ClassicalSideB t ∧ ClassicalSideB t = ClassicalSideC t

/-- Sum of squared sides `a² + b² + c²`. -/
def ClassicalSumSq (t : Affine.Triangle ℝ P) : ℝ :=
  ClassicalSideA t ^ 2 + ClassicalSideB t ^ 2 + ClassicalSideC t ^ 2

/-- `X` lies inside or on the triangle (closed convex hull of the vertices):
all barycentric coordinates nonnegative. -/
def ClassicalInsideOrOn (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- `X` lies strictly inside the triangle: all barycentric coordinates positive
(works in any ambient dimension, i.e. relative interior). -/
def ClassicalStrictlyInside (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- Distance from `X` to the line through `Y` and `Z`. -/
def ClassicalDistToLine (X Y Z : P) : ℝ :=
  Metric.infDist X (affineSpan ℝ {Y, Z} : Set P)

/-- Fermat point: a point seeing each side under `120°`. -/
def ClassicalIsFermatPoint (t : Affine.Triangle ℝ P) (F : P) : Prop :=
  ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
  ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
  ∠ (t.points 0) F (t.points 1) = 2 * π / 3

/-- All angles of the triangle are less than `120°`. -/
def ClassicalAnglesLt120 (t : Affine.Triangle ℝ P) : Prop :=
  ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3 ∧
  ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3 ∧
  ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3

/-- `X'` is the apex of the equilateral triangle erected outward on side `YZ`
of a triangle whose third vertex is `X`: `X'Y = X'Z = YZ`, and `X'` lies on the
opposite side of line `YZ` from `X`. -/
def ClassicalOutwardEquilateralApex (X Y Z X' : P) : Prop :=
  dist X' Y = dist Y Z ∧ dist X' Z = dist Y Z ∧
  (affineSpan ℝ {Y, Z}).SOppSide X X'

/-- Sum of distances `XA + XB + XC`. -/
def ClassicalDistSum (t : Affine.Triangle ℝ P) (X : P) : ℝ :=
  dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)

/-- Sum of squared distances `XA² + XB² + XC²`. -/
def ClassicalDistSqSum (t : Affine.Triangle ℝ P) (X : P) : ℝ :=
  dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2

/-- Four distinct points lie "in this order" `A, B, C, D` on a circle or line:
either they are concyclic and the diagonals `AC`, `BD` meet (convex position in
the order `ABCD`), or they are collinear and the pair `{A, C}` separates
`{B, D}` (exactly one of `B, D` lies strictly between `A` and `C`). -/
def ClassicalInOrderOnCircleOrLine (A B C D : P) : Prop :=
  (Concyclic ({A, B, C, D} : Set P) ∧
      ∃ X : P, Wbtw ℝ A X C ∧ Wbtw ℝ B X D) ∨
  (Collinear ℝ ({A, B, C, D} : Set P) ∧ (Sbtw ℝ A B C ↔ ¬ Sbtw ℝ A D C))

/-! ## E1–E12 -/

/-- E1 (Euler). OI² = R² − 2Rr. -/
theorem classical_E1 (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.incenter ^ 2 =
      t.circumradius ^ 2 - 2 * t.circumradius * t.inradius := by sorry

/-- E2 (Euler's inequality). R ≥ 2r. -/
theorem classical_E2a (t : Affine.Triangle ℝ P) :
    2 * t.inradius ≤ t.circumradius := by sorry

/-- E2 (Euler's inequality). … with equality iff the triangle is equilateral. -/
theorem classical_E2b (t : Affine.Triangle ℝ P) :
    t.circumradius = 2 * t.inradius ↔ ClassicalEquilateral t := by sorry

/-- E3 (Feuerbach–Euler for excircles). OI_A² = R² + 2R r_A (and similarly for B, C).
`t.excenter {i}` / `t.exradius {i}` are the excentre / exradius opposite vertex `i`. -/
theorem classical_E3 (t : Affine.Triangle ℝ P) (i : Fin 3) :
    dist t.circumcenter (t.excenter {i}) ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {i} := by sorry

/-- E4. OG² = R² − (a²+b²+c²)/9. -/
theorem classical_E4a (t : Affine.Triangle ℝ P) :
    dist t.circumcenter (ClassicalCentroid t) ^ 2 =
      t.circumradius ^ 2 - ClassicalSumSq t / 9 := by sorry

/-- E4. OH² = 9R² − (a²+b²+c²). -/
theorem classical_E4b (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.orthocenter ^ 2 =
      9 * t.circumradius ^ 2 - ClassicalSumSq t := by sorry

/-- E4. IG² = (s² + 5r² − 16Rr)/9. -/
theorem classical_E4c (t : Affine.Triangle ℝ P) :
    dist t.incenter (ClassicalCentroid t) ^ 2 =
      (ClassicalSemiperimeter t ^ 2 + 5 * t.inradius ^ 2
        - 16 * t.circumradius * t.inradius) / 9 := by sorry

/-- E5 (Fundamental inequality / Blundon's quartic).
s⁴ − 2(2R² + 10Rr − r²)s² + r(4R+r)³ ≤ 0. -/
theorem classical_E5 (t : Affine.Triangle ℝ P) :
    ClassicalSemiperimeter t ^ 4
      - 2 * (2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2)
        * ClassicalSemiperimeter t ^ 2
      + t.inradius * (4 * t.circumradius + t.inradius) ^ 3 ≤ 0 := by sorry

/-- E6 (Gerretsen). 16Rr − 5r² ≤ s². -/
theorem classical_E6a (t : Affine.Triangle ℝ P) :
    16 * t.circumradius * t.inradius - 5 * t.inradius ^ 2 ≤
      ClassicalSemiperimeter t ^ 2 := by sorry

/-- E6 (Gerretsen). s² ≤ 4R² + 4Rr + 3r². -/
theorem classical_E6b (t : Affine.Triangle ℝ P) :
    ClassicalSemiperimeter t ^ 2 ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2 := by sorry

/-- E7 (Kooi). s² ≤ R(4R+r)² / (2(2R−r)).
(`2R − r > 0` follows from E2, so the division is meaningful; no extra hypothesis.) -/
theorem classical_E7 (t : Affine.Triangle ℝ P) :
    ClassicalSemiperimeter t ^ 2 ≤
      t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius)) := by sorry

/-- E8 (Weitzenböck). a²+b²+c² ≥ 4√3 Δ. -/
theorem classical_E8a (t : Affine.Triangle ℝ P) :
    4 * √3 * ClassicalArea t ≤ ClassicalSumSq t := by sorry

/-- E8 (Weitzenböck). … equality iff equilateral. -/
theorem classical_E8b (t : Affine.Triangle ℝ P) :
    ClassicalSumSq t = 4 * √3 * ClassicalArea t ↔ ClassicalEquilateral t := by sorry

/-- E9 (Hadwiger–Finsler). a²+b²+c² ≥ 4√3 Δ + (a−b)² + (b−c)² + (c−a)². -/
theorem classical_E9a (t : Affine.Triangle ℝ P) :
    4 * √3 * ClassicalArea t + (ClassicalSideA t - ClassicalSideB t) ^ 2
      + (ClassicalSideB t - ClassicalSideC t) ^ 2 + (ClassicalSideC t - ClassicalSideA t) ^ 2
      ≤ ClassicalSumSq t := by sorry

/-- E9 (Hadwiger–Finsler). … equality iff equilateral. -/
theorem classical_E9b (t : Affine.Triangle ℝ P) :
    ClassicalSumSq t = 4 * √3 * ClassicalArea t + (ClassicalSideA t - ClassicalSideB t) ^ 2
      + (ClassicalSideB t - ClassicalSideC t) ^ 2 + (ClassicalSideC t - ClassicalSideA t) ^ 2
      ↔ ClassicalEquilateral t := by sorry

/-- E10 (Isoperimetric inequality for triangles). (a+b+c)² ≥ 12√3 Δ. -/
theorem classical_E10a (t : Affine.Triangle ℝ P) :
    12 * √3 * ClassicalArea t ≤
      (ClassicalSideA t + ClassicalSideB t + ClassicalSideC t) ^ 2 := by sorry

/-- E10 (Isoperimetric inequality for triangles). … equality iff equilateral. -/
theorem classical_E10b (t : Affine.Triangle ℝ P) :
    (ClassicalSideA t + ClassicalSideB t + ClassicalSideC t) ^ 2 = 12 * √3 * ClassicalArea t
      ↔ ClassicalEquilateral t := by sorry

/-- E11 (Leibniz). For every point X: XA² + XB² + XC² = 3XG² + (a²+b²+c²)/3. -/
theorem classical_E11a (t : Affine.Triangle ℝ P) (X : P) :
    ClassicalDistSqSum t X =
      3 * dist X (ClassicalCentroid t) ^ 2 + ClassicalSumSq t / 3 := by sorry

/-- E11 (Leibniz). … so the sum is minimised exactly at X = G. -/
theorem classical_E11b (t : Affine.Triangle ℝ P) :
    (∀ X : P, ClassicalDistSqSum t (ClassicalCentroid t) ≤ ClassicalDistSqSum t X) ∧
    (∀ X : P, ClassicalDistSqSum t X = ClassicalDistSqSum t (ClassicalCentroid t) →
      X = ClassicalCentroid t) := by sorry

/-- E12 (Neuberg–Pedoe).
a′²(b²+c²−a²) + b′²(c²+a²−b²) + c′²(a²+b²−c²) ≥ 16ΔΔ′.
-- AMBIGUOUS: the two triangles need not live in the same space; we allow
-- arbitrary (possibly different) Euclidean affine spaces `P` and `P'`. -/
theorem classical_E12a {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    [MetricSpace P'] [NormedAddTorsor V' P']
    (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    16 * ClassicalArea t * ClassicalArea t' ≤
      ClassicalSideA t' ^ 2 * (ClassicalSideB t ^ 2 + ClassicalSideC t ^ 2 - ClassicalSideA t ^ 2)
      + ClassicalSideB t' ^ 2 * (ClassicalSideC t ^ 2 + ClassicalSideA t ^ 2 - ClassicalSideB t ^ 2)
      + ClassicalSideC t' ^ 2 * (ClassicalSideA t ^ 2 + ClassicalSideB t ^ 2 - ClassicalSideC t ^ 2)
      := by sorry

/-- E12 (Neuberg–Pedoe). … equality iff the triangles are similar (a′:b′:c′ = a:b:c). -/
theorem classical_E12b {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    [MetricSpace P'] [NormedAddTorsor V' P']
    (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    (ClassicalSideA t' ^ 2 * (ClassicalSideB t ^ 2 + ClassicalSideC t ^ 2 - ClassicalSideA t ^ 2)
      + ClassicalSideB t' ^ 2 * (ClassicalSideC t ^ 2 + ClassicalSideA t ^ 2 - ClassicalSideB t ^ 2)
      + ClassicalSideC t' ^ 2 * (ClassicalSideA t ^ 2 + ClassicalSideB t ^ 2 - ClassicalSideC t ^ 2)
      = 16 * ClassicalArea t * ClassicalArea t') ↔
    ∃ k : ℝ, 0 < k ∧ ClassicalSideA t' = k * ClassicalSideA t ∧
      ClassicalSideB t' = k * ClassicalSideB t ∧ ClassicalSideC t' = k * ClassicalSideC t := by
  sorry

/-! ## P1–P2 -/

/-- P1 (Ptolemy's inequality). For any four points A,B,C,D: AC·BD ≤ AB·CD + BC·AD. -/
theorem classical_P1 (A B C D : P) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D := by sorry

/-- P2 (Ptolemy's theorem and converse). For four distinct points, equality holds iff
A,B,C,D lie in this order on a circle or a line.
-- AMBIGUOUS: "in this order" is read cyclically (the pair {A,C} separates {B,D}).
-- For collinear points the literal reading `Sbtw A B C ∧ Sbtw B C D` would make the
-- "only if" direction false (e.g. order B,C,D,A on a line also gives equality). -/
theorem classical_P2 (A B C D : P) (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D ↔
      ClassicalInOrderOnCircleOrLine A B C D := by sorry

/-! ## M1–M2 -/

/-- M1 (Erdős–Mordell). For X inside or on ABC with distances p, q, r to the side lines
BC, CA, AB: XA + XB + XC ≥ 2(p + q + r). -/
theorem classical_M1a (t : Affine.Triangle ℝ P) (X : P) (hX : ClassicalInsideOrOn t X) :
    2 * (ClassicalDistToLine X (t.points 1) (t.points 2)
        + ClassicalDistToLine X (t.points 2) (t.points 0)
        + ClassicalDistToLine X (t.points 0) (t.points 1)) ≤ ClassicalDistSum t X := by sorry

/-- M1 (Erdős–Mordell). … equality iff the triangle is equilateral and X is its centre. -/
theorem classical_M1b (t : Affine.Triangle ℝ P) (X : P) (hX : ClassicalInsideOrOn t X) :
    ClassicalDistSum t X = 2 * (ClassicalDistToLine X (t.points 1) (t.points 2)
        + ClassicalDistToLine X (t.points 2) (t.points 0)
        + ClassicalDistToLine X (t.points 0) (t.points 1)) ↔
      ClassicalEquilateral t ∧ X = ClassicalCentroid t := by sorry

/-- M2 (Barrow). For X inside ABC, if the internal bisectors of angles BXC, CXA, AXB
meet BC, CA, AB at U, V, W, then XA + XB + XC ≥ 2(XU + XV + XW).
"Internal bisector of ∠BXC meets BC at U" is encoded as: U on segment BC and
∠BXU = ∠UXC. -/
theorem classical_M2 (t : Affine.Triangle ℝ P) (X U V W : P)
    (hX : ClassicalStrictlyInside t X)
    (hU : Wbtw ℝ (t.points 1) U (t.points 2) ∧ ∠ (t.points 1) X U = ∠ U X (t.points 2))
    (hV : Wbtw ℝ (t.points 2) V (t.points 0) ∧ ∠ (t.points 2) X V = ∠ V X (t.points 0))
    (hW : Wbtw ℝ (t.points 0) W (t.points 1) ∧ ∠ (t.points 0) X W = ∠ W X (t.points 1)) :
    2 * (dist X U + dist X V + dist X W) ≤ ClassicalDistSum t X := by sorry

/-! ## F1–F3 -/

/-- F1 (Fermat–Torricelli). If every angle of ABC is less than 120°, there is a point F
seeing each side under 120°, and F minimises XA + XB + XC over all points X. -/
theorem classical_F1a (t : Affine.Triangle ℝ P) (h : ClassicalAnglesLt120 t) :
    ∃ F : P, ClassicalIsFermatPoint t F ∧
      ∀ X : P, ClassicalDistSum t F ≤ ClassicalDistSum t X := by sorry

/-- F1 (Fermat–Torricelli), strengthened reading: any point F seeing each side under 120°
minimises XA + XB + XC.
-- AMBIGUOUS: the textbook phrase "there is a point F … and F minimises" can be read as
-- existence-plus-minimality (F1a) or as "the 120° point is the minimiser" (this form). -/
theorem classical_F1b (t : Affine.Triangle ℝ P) (h : ClassicalAnglesLt120 t) (F : P)
    (hF : ClassicalIsFermatPoint t F) :
    ∀ X : P, ClassicalDistSum t F ≤ ClassicalDistSum t X := by sorry

section Plane

variable [Fact (Module.finrank ℝ V = 2)]

/-- F2 (Fermat–Napoleon). In the plane, erect equilateral triangles BCA′, CAB′, ABC′
outward on the sides. Then AA′ = BB′ = CC′. -/
theorem classical_F2a (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C') :
    dist (t.points 0) A' = dist (t.points 1) B' ∧
      dist (t.points 1) B' = dist (t.points 2) C' := by sorry

/-- F2 (Fermat–Napoleon). … the lines AA′, BB′, CC′ are concurrent. -/
theorem classical_F2b (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C') :
    ∃ Q : P, Q ∈ affineSpan ℝ {t.points 0, A'} ∧ Q ∈ affineSpan ℝ {t.points 1, B'} ∧
      Q ∈ affineSpan ℝ {t.points 2, C'} := by sorry

/-- F2 (Fermat–Napoleon). … if all angles are < 120° they meet at the Fermat point F and
AA′ = FA + FB + FC. -/
theorem classical_F2c (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C')
    (h : ClassicalAnglesLt120 t) (F : P) (hF : ClassicalIsFermatPoint t F) :
    F ∈ affineSpan ℝ {t.points 0, A'} ∧ F ∈ affineSpan ℝ {t.points 1, B'} ∧
      F ∈ affineSpan ℝ {t.points 2, C'} ∧ dist (t.points 0) A' = ClassicalDistSum t F := by
  sorry

/-- F2 (Fermat–Napoleon). … and the lines meet at 60° angles.
-- AMBIGUOUS: the angle between two (unoriented) lines is taken as the angle between
-- direction vectors up to supplement, i.e. the vector angle is 60° or 120°. -/
theorem classical_F2d (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C') :
    (InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) ∧
    (InnerProductGeometry.angle (B' -ᵥ t.points 1) (C' -ᵥ t.points 2) = π / 3 ∨
      InnerProductGeometry.angle (B' -ᵥ t.points 1) (C' -ᵥ t.points 2) = 2 * π / 3) ∧
    (InnerProductGeometry.angle (C' -ᵥ t.points 2) (A' -ᵥ t.points 0) = π / 3 ∨
      InnerProductGeometry.angle (C' -ᵥ t.points 2) (A' -ᵥ t.points 0) = 2 * π / 3) := by
  sorry

/-- F3 (Napoleon). The centres of these three equilateral triangles form an equilateral
triangle whose centre is the centroid of ABC.  The centre of the equilateral triangle
`BCA′` is its centroid. -/
theorem classical_F3 (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C') :
    let Oa := Finset.univ.centroid ℝ ![t.points 1, t.points 2, A']
    let Ob := Finset.univ.centroid ℝ ![t.points 2, t.points 0, B']
    let Oc := Finset.univ.centroid ℝ ![t.points 0, t.points 1, C']
    dist Oa Ob = dist Ob Oc ∧ dist Ob Oc = dist Oc Oa ∧
      Finset.univ.centroid ℝ ![Oa, Ob, Oc] = ClassicalCentroid t := by sorry

end Plane

end PaperHClassical
