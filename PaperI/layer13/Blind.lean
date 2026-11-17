import Mathlib

noncomputable section
open scoped RealInnerProductSpace
open Set Metric MeasureTheory EuclideanGeometry

open scoped RealInnerProductSpace
open Set Metric



open scoped BigOperators

def BlindPlane (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] : Prop :=
  Module.finrank ℝ V = 2

def BlindSideAB {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B : P) : ℝ :=
  dist A B

def BlindSideBC {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (B C : P) : ℝ :=
  dist B C

def BlindSideCD {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (C D : P) : ℝ :=
  dist C D

def BlindSideDA {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (D A : P) : ℝ :=
  dist D A

def BlindDiagonalAC {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A C : P) : ℝ :=
  dist A C

def BlindDiagonalBD {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (B D : P) : ℝ :=
  dist B D

def BlindSemiperimeter {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C D : P) : ℝ :=
  (1 / 2 : ℝ) * (dist A B + dist B C + dist C D + dist D A)

-- AMBIGUOUS: The omitted condition on X could instead be stated using
-- interiors of convex hulls.
def BlindConvexQuad {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C D : P) : Prop :=
  BlindPlane V ∧
    ¬ Collinear ℝ ({A, B, C} : Set P) ∧
    ∃ (X : P) (t u : ℝ),
      t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1 ∧
      X = t • (C -ᵥ A) +ᵥ A ∧
      X = u • (D -ᵥ B) +ᵥ B

def BlindCross {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e : OrthonormalBasis (Fin 2) ℝ V) (v w : V) : ℝ :=
  inner ℝ v (e 0) * inner ℝ w (e 1) -
    inner ℝ v (e 1) * inner ℝ w (e 0)

def BlindDiagonalFrame {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D X : P) (e : OrthonormalBasis (Fin 2) ℝ V)
    (t u : ℝ) (p q : V) : Prop :=
  BlindPlane V ∧
    t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1 ∧
    BlindCross e p q > 0 ∧
    A = (-t) • p +ᵥ X ∧
    C = (1 - t) • p +ᵥ X ∧
    B = (-u) • q +ᵥ X ∧
    D = (1 - u) • q +ᵥ X

def BlindCrossTriangleArea {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (e : OrthonormalBasis (Fin 2) ℝ V) (A B C : P) : ℝ :=
  (1 / 2 : ℝ) * |BlindCross e (B -ᵥ A) (C -ᵥ A)|

def BlindTriangleAreaBAC {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C : P) : ℝ :=
  (1 / 2 : ℝ) * dist A B * dist A C *
    Real.sin (EuclideanGeometry.angle B A C)

def BlindTriangleAreaCAD {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A C D : P) : ℝ :=
  (1 / 2 : ℝ) * dist A C * dist A D *
    Real.sin (EuclideanGeometry.angle C A D)

def BlindQuadArea {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) : ℝ :=
  BlindTriangleAreaBAC A B C + BlindTriangleAreaCAD A C D

def BlindSideLine {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (X Y : P) : Set P :=
  (affineSpan ℝ ({X, Y} : Set P) : Set P)

def BlindLineDistance {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (X Y Z : P) : ℝ :=
  Metric.infDist Z (BlindSideLine X Y)

def BlindSignedDistance {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (e : OrthonormalBasis (Fin 2) ℝ V) (X Y Z : P) : ℝ :=
  BlindCross e (Y -ᵥ X) (Z -ᵥ X) / dist X Y

def BlindSameSide {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (X Y Z W : P) : Prop :=
  ∃ e : OrthonormalBasis (Fin 2) ℝ V,
    BlindCross e (Y -ᵥ X) (Z -ᵥ X) *
      BlindCross e (Y -ᵥ X) (W -ᵥ X) > 0

def BlindIncircle {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D I : P) (r : ℝ) : Prop :=
  BlindPlane V ∧ r > 0 ∧
    BlindLineDistance A B I = r ∧
    BlindLineDistance B C I = r ∧
    BlindLineDistance C D I = r ∧
    BlindLineDistance D A I = r ∧
    BlindSameSide A B I C ∧
    BlindSameSide B C I D ∧
    BlindSameSide C D I A ∧
    BlindSameSide D A I B

def BlindTangentialQuad {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) : Prop :=
  ∃ (I : P) (r : ℝ), BlindIncircle A B C D I r

def BlindSignedIncircleEquations {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (e : OrthonormalBasis (Fin 2) ℝ V) (A B C D I : P) (r : ℝ) : Prop :=
  BlindCross e (B -ᵥ A) (I -ᵥ A) = r * dist A B ∧
    BlindCross e (C -ᵥ B) (I -ᵥ B) = r * dist B C ∧
    BlindCross e (D -ᵥ C) (I -ᵥ C) = r * dist C D ∧
    BlindCross e (A -ᵥ D) (I -ᵥ D) = r * dist D A

def BlindCircle : Type := ℂ × ℝ

def BlindCirclePoints (c : BlindCircle) : Set ℂ :=
  {z | dist z c.1 = c.2}

def BlindDisk (c : BlindCircle) : Set ℂ :=
  {z | dist z c.1 ≤ c.2}

def BlindCircleInterior (c : BlindCircle) : Set ℂ :=
  {z | dist z c.1 < c.2}

def BlindPower (z : ℂ) (c : BlindCircle) : ℝ :=
  dist z c.1 ^ 2 - c.2 ^ 2

def BlindExternallyTangent (c d : BlindCircle) : Prop :=
  c.2 > 0 ∧ d.2 > 0 ∧ dist c.1 d.1 = c.2 + d.2

def BlindInternallyTangent (inner outer : BlindCircle) : Prop :=
  inner.2 > 0 ∧ outer.2 > 0 ∧
    dist inner.1 outer.1 + inner.2 = outer.2

def BlindDiameterCircle (a b : ℝ) : BlindCircle :=
  ((((a + b) / 2 : ℝ) : ℂ), (b - a) / 2)

def BlindArbelosOuterCircle (a c : ℝ) : BlindCircle :=
  BlindDiameterCircle a c

def BlindArbelosLeftCircle (a b : ℝ) : BlindCircle :=
  BlindDiameterCircle a b

def BlindArbelosRightCircle (b c : ℝ) : BlindCircle :=
  BlindDiameterCircle b c

-- AMBIGUOUS: The arbelos may instead mean only its three semicircular arcs.
def BlindArbelos (a b c : ℝ) : Set ℂ :=
  {z | a < b ∧ b < c ∧ 0 ≤ z.im ∧
    z ∈ BlindDisk (BlindArbelosOuterCircle a c) ∧
    z ∉ BlindCircleInterior (BlindArbelosLeftCircle a b) ∧
    z ∉ BlindCircleInterior (BlindArbelosRightCircle b c)}

-- AMBIGUOUS: The twin circles may be specified by their explicit centers and
-- common radius rather than by these tangencies.
def BlindArchimedesTwinCircle (a b c : ℝ) (left : Bool)
    (circle : BlindCircle) : Prop :=
  a < b ∧ b < c ∧ circle.1.im > 0 ∧
    BlindInternallyTangent circle (BlindArbelosOuterCircle a c) ∧
    BlindExternallyTangent circle
      (if left then BlindArbelosLeftCircle a b
       else BlindArbelosRightCircle b c) ∧
    |circle.1.re - b| = circle.2

def BlindArchimedesTwins (a b c : ℝ) (left right : BlindCircle) : Prop :=
  BlindArchimedesTwinCircle a b c true left ∧
    BlindArchimedesTwinCircle a b c false right

-- AMBIGUOUS: A Pappus chain may be indexed from the other inner semicircle.
def BlindPappusChain (a b c : ℝ) (chain : ℕ → BlindCircle) : Prop :=
  a < b ∧ b < c ∧
    (∀ n, (chain n).1.im > 0 ∧
      BlindInternallyTangent (chain n) (BlindArbelosOuterCircle a c) ∧
      BlindExternallyTangent (chain n) (BlindArbelosLeftCircle a b)) ∧
    BlindExternallyTangent (chain 0) (BlindArbelosRightCircle b c) ∧
    ∀ n, BlindExternallyTangent (chain n) (chain (n + 1))

-- AMBIGUOUS: A Steiner chain may also be defined for two non-nested circles.
def BlindSteinerChain (inner outer : BlindCircle) (n : ℕ)
    (chain : ℕ → BlindCircle) : Prop :=
  0 < n ∧ inner.2 > 0 ∧ outer.2 > 0 ∧
    dist inner.1 outer.1 + inner.2 < outer.2 ∧
    (∀ i, chain (i + n) = chain i) ∧
    (∀ i, i < n →
      BlindInternallyTangent (chain i) outer ∧
      BlindExternallyTangent (chain i) inner ∧
      BlindExternallyTangent (chain i) (chain ((i + 1) % n)))

-- AMBIGUOUS: “Simple” can instead mean that the chain has no self-intersections.
def BlindSimpleSteinerChain (inner outer : BlindCircle) (n : ℕ)
    (chain : ℕ → BlindCircle) : Prop :=
  BlindSteinerChain inner outer n chain ∧
    ∀ i j, i < n → j < n → i ≠ j → chain i ≠ chain j

def BlindDisjointSteinerChain (inner outer : BlindCircle) (n : ℕ)
    (chain : ℕ → BlindCircle) : Prop :=
  BlindSteinerChain inner outer n chain ∧
    ∀ i j, i < n → j < n → i ≠ j →
      Disjoint (BlindCircleInterior (chain i)) (BlindCircleInterior (chain j))

def BlindRadicalAxis (c d : BlindCircle) : Set ℂ :=
  {z | BlindPower z c = BlindPower z d}

def BlindRadicalCentre (c d e : BlindCircle) (z : ℂ) : Prop :=
  BlindPower z c = BlindPower z d ∧ BlindPower z d = BlindPower z e

-- AMBIGUOUS: A coaxal pencil may include oriented circles, lines, or
-- degenerate circles as generalized circles.
def BlindCoaxalPencil (c d : BlindCircle) : Set BlindCircle :=
  {e | ∃ t : ℝ, ∀ z : ℂ,
    BlindPower z e = t * BlindPower z c + (1 - t) * BlindPower z d}

def BlindOrthogonalCircles (c d : BlindCircle) : Prop :=
  c.2 > 0 ∧ d.2 > 0 ∧
    dist c.1 d.1 ^ 2 = c.2 ^ 2 + d.2 ^ 2

-- AMBIGUOUS: Inversion can instead be a partial map undefined at its center.
def BlindInversion (center : ℂ) (radius : ℝ) (z : ℂ) : ℂ :=
  center + ((radius ^ 2 / ‖z - center‖ ^ 2 : ℝ) : ℂ) * (z - center)

-- AMBIGUOUS: A Peaucellier cell may include an additional driving linkage
-- and nondegeneracy conditions.
def BlindPeaucellierCell (O A B C D : ℂ) : Prop :=
  dist O A = dist O C ∧
    dist A B = dist B C ∧
    dist B C = dist C D ∧
    dist C D = dist D A

-- AMBIGUOUS: Curvature may mean the unsigned reciprocal of the radius.
def BlindCurvature (signedRadius : ℝ) : ℝ :=
  1 / signedRadius

def BlindDescartesCurvatures (k : Fin 4 → ℝ) : Prop :=
  (∑ i : Fin 4, k i) ^ 2 = 2 * ∑ i : Fin 4, (k i) ^ 2

def BlindApollonianMove (k : Fin 4 → ℝ) (i : Fin 4) : Fin 4 → ℝ :=
  fun j =>
    if j = i then 2 * ∑ h ∈ Finset.univ.erase i, k h - k i else k j


-- ===== section: quad =====


open scoped BigOperators

def BlindVanAubelSign {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (e : OrthonormalBasis (Fin 2) ℝ V) (A B C D : P) : ℝ :=
  if BlindCross e (C -ᵥ A) (D -ᵥ B) > 0 then 1 else -1

def BlindVanAubelRotation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (e : OrthonormalBasis (Fin 2) ℝ V)
    (σ : ℝ) (v : V) : V :=
  (Real.cos (-σ * Real.pi / 2) * inner ℝ v (e 0) -
      Real.sin (-σ * Real.pi / 2) * inner ℝ v (e 1)) • e 0 +
    (Real.sin (-σ * Real.pi / 2) * inner ℝ v (e 0) +
      Real.cos (-σ * Real.pi / 2) * inner ℝ v (e 1)) • e 1

def BlindVanAubelCenter {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (e : OrthonormalBasis (Fin 2) ℝ V) (A B C D X Y : P) : P :=
  ((1 / 2 : ℝ) •
    BlindVanAubelRotation e (BlindVanAubelSign e A B C D) (Y -ᵥ X)) +ᵥ
      midpoint ℝ X Y

-- thm:bretschneider
-- For every convex quadrilateral ABCD, Bretschneider's formula holds.
theorem blind_1 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D) :
    BlindQuadArea A B C D ^ 2 =
      (BlindSemiperimeter A B C D - BlindSideAB A B) *
      (BlindSemiperimeter A B C D - BlindSideBC B C) *
      (BlindSemiperimeter A B C D - BlindSideCD C D) *
      (BlindSemiperimeter A B C D - BlindSideDA D A) -
      BlindSideAB A B * BlindSideBC B C * BlindSideCD C D * BlindSideDA D A *
        Real.cos ((EuclideanGeometry.angle A B C +
          EuclideanGeometry.angle C D A) / 2) ^ 2 := by
  sorry

-- thm:brahmagupta
-- For every convex quadrilateral ABCD with A, B, C, D concyclic, Brahmagupta's formula holds.
theorem blind_2 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D)
    (hcyclic : Cospherical ({A, B, C, D} : Set P)) :
    BlindQuadArea A B C D =
      Real.sqrt
        ((BlindSemiperimeter A B C D - BlindSideAB A B) *
         (BlindSemiperimeter A B C D - BlindSideBC B C) *
         (BlindSemiperimeter A B C D - BlindSideCD C D) *
         (BlindSemiperimeter A B C D - BlindSideDA D A)) := by
  sorry

-- thm:pitot
-- Let ABCD be convex.
theorem blind_3 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D)
    (htangent : BlindTangentialQuad A B C D) :
    BlindSideAB A B + BlindSideCD C D = BlindSideBC B C + BlindSideDA D A := by
  sorry

-- thm:pitot (converse)
-- Conversely, if a + c = b + d, then ABCD is tangential.
theorem blind_4 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D)
    (hsides : BlindSideAB A B + BlindSideCD C D =
      BlindSideBC B C + BlindSideDA D A) :
    BlindTangentialQuad A B C D := by
  sorry

-- thm:euler4
-- For any four points, a² + b² + c² + d² = |AC|² + |BD|² + 4|MN|², where M and N are the midpoints of AC and BD.
theorem blind_5 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) :
    BlindSideAB A B ^ 2 + BlindSideBC B C ^ 2 +
      BlindSideCD C D ^ 2 + BlindSideDA D A ^ 2 =
      BlindDiagonalAC A C ^ 2 + BlindDiagonalBD B D ^ 2 +
        4 * dist (midpoint ℝ A C) (midpoint ℝ B D) ^ 2 := by
  sorry

-- thm:ptolemy2
-- For every convex quadrilateral ABCD with A, B, C, D concyclic, Ptolemy's second theorem holds.
theorem blind_6 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (hplane : BlindPlane V) (hconvex : BlindConvexQuad A B C D)
    (hcyclic : Cospherical ({A, B, C, D} : Set P)) :
    dist A C / dist B D =
      (dist A B * dist A D + dist C B * dist C D) /
        (dist B A * dist B C + dist D A * dist D C) := by
  sorry

-- thm:vanaubel (equal lengths)
-- Let o be an orientation of the plane and A, B, C, D any four points.
theorem blind_7 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (e : OrthonormalBasis (Fin 2) ℝ V)
    (hplane : BlindPlane V) :
    dist (BlindVanAubelCenter e A B C D A B)
        (BlindVanAubelCenter e A B C D C D) =
      dist (BlindVanAubelCenter e A B C D B C)
        (BlindVanAubelCenter e A B C D D A) := by
  sorry

-- thm:vanaubel (perpendicularity)
-- Let o be an orientation of the plane and A, B, C, D any four points.
theorem blind_8 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (e : OrthonormalBasis (Fin 2) ℝ V)
    (hplane : BlindPlane V) :
    inner ℝ
      (BlindVanAubelCenter e A B C D C D -ᵥ BlindVanAubelCenter e A B C D A B)
      (BlindVanAubelCenter e A B C D D A -ᵥ BlindVanAubelCenter e A B C D B C) =
        0 := by
  sorry

-- thm:newton
-- If ABCD is convex and (I, r) is an incircle, then the midpoints of AC and BD and the centre I are collinear.
theorem blind_9 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D I : P) (r : ℝ) (hplane : BlindPlane V)
    (hconvex : BlindConvexQuad A B C D) (hincircle : BlindIncircle A B C D I r) :
    Collinear ℝ ({midpoint ℝ A C, midpoint ℝ B D, I} : Set P) := by
  sorry

-- thm:fuss
-- Let ABCD be convex, let A, B, C, D lie at distance R from a point O, and let (I, r) be an incircle of ABCD.
theorem blind_10 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D O I : P) (R r : ℝ) (hplane : BlindPlane V)
    (hconvex : BlindConvexQuad A B C D)
    (hA : dist A O = R) (hB : dist B O = R)
    (hC : dist C O = R) (hD : dist D O = R)
    (hincircle : BlindIncircle A B C D I r) :
    1 / (R - dist O I) ^ 2 + 1 / (R + dist O I) ^ 2 = 1 / r ^ 2 := by
  sorry

-- thm:fuss (positivity)
-- In Theorem thm:fuss nothing is assumed about d or R; the proof shows that R² - d² > 0.
theorem blind_11 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D O I : P) (R r : ℝ) (hplane : BlindPlane V)
    (hconvex : BlindConvexQuad A B C D)
    (hA : dist A O = R) (hB : dist B O = R)
    (hC : dist C O = R) (hD : dist D O = R)
    (hincircle : BlindIncircle A B C D I r) :
    R ^ 2 - dist O I ^ 2 > 0 := by
  sorry

-- thm:fuss (counterexample)
-- For a convex tangential quadrilateral with O the circumcentre of ABC the relation fails in general.
theorem blind_12 :
    ∃ (A B C D O I : ℂ) (R r : ℝ),
      BlindConvexQuad A B C D ∧
      dist A O = R ∧ dist B O = R ∧ dist C O = R ∧
      BlindIncircle A B C D I r ∧
      1 / (R - dist O I) ^ 2 + 1 / (R + dist O I) ^ 2 ≠ 1 / r ^ 2 := by
  sorry

-- thm:fuss (earlier variant)
-- Our earlier proof instead assumed four distinct points on the circumcircle whose side lines are tangent to the incircle, with d ≠ R, and did not need convexity.
-- AMBIGUOUS: The points may also be required to occur in the stated order on the circumcircle.
theorem blind_13 {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (A B C D O I : P) (R r : ℝ) (hplane : BlindPlane V)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hA : dist A O = R) (hB : dist B O = R)
    (hC : dist C O = R) (hD : dist D O = R)
    (hr : r > 0)
    (htAB : BlindLineDistance A B I = r)
    (htBC : BlindLineDistance B C I = r)
    (htCD : BlindLineDistance C D I = r)
    (htDA : BlindLineDistance D A I = r)
    (hd : dist O I ≠ R) :
    1 / (R - dist O I) ^ 2 + 1 / (R + dist O I) ^ 2 = 1 / r ^ 2 := by
  sorry


-- ===== section: arbelos =====


open scoped BigOperators

def BlindPappusDenominator (a b t : ℝ) : ℝ :=
  a * (a + b) + t ^ 2 * b ^ 2

def BlindPhi (a b t : ℝ) : BlindCircle :=
  (Complex.mk
      (a * (a + b) * (2 * a + b) / BlindPappusDenominator a b t)
      (2 * a * b * (a + b) * t / BlindPappusDenominator a b t),
    a * b * (a + b) / BlindPappusDenominator a b t)

def BlindPappusCircle (a b : ℝ) (n : ℕ) : BlindCircle :=
  BlindPhi a b n

-- AMBIGUOUS: The passage does not explicitly define the inversion or its radius.
def BlindPappusInversion (a b : ℝ) : ℂ → ℂ :=
  BlindInversion 0 (2 * Real.sqrt (a * (a + b)))

def BlindInvertedCircle (center : ℂ) (radius : ℝ) (c : BlindCircle) :
    BlindCircle :=
  (center + ((radius ^ 2 / BlindPower center c : ℝ) : ℂ) * (c.1 - center),
    radius ^ 2 * c.2 / BlindPower center c)

-- thm:twin
-- Let a,b>0 and let s be a circle tangent to ℓ, internally tangent to Γ and externally tangent to Γ₁, with centre to the left of ℓ.
theorem blind_14
    (a b : ℝ) (s : BlindCircle)
    (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s.2)
    (hline : |s.1.re - 2 * a| = s.2)
    (hleft : s.1.re < 2 * a)
    (houter : BlindInternallyTangent s (BlindDiameterCircle 0 (2 * (a + b))))
    (hinner : BlindExternallyTangent s (BlindDiameterCircle 0 (2 * a))) :
    s.2 = a * b / (a + b) := by
  sorry

-- thm:twin
-- The same holds with Γ₂ for a circle to the right of ℓ.
theorem blind_15
    (a b : ℝ) (s : BlindCircle)
    (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s.2)
    (hline : |s.1.re - 2 * a| = s.2)
    (hright : 2 * a < s.1.re)
    (houter : BlindInternallyTangent s (BlindDiameterCircle 0 (2 * (a + b))))
    (hinner :
      BlindExternallyTangent s (BlindDiameterCircle (2 * a) (2 * (a + b)))) :
    s.2 = a * b / (a + b) := by
  sorry

-- thm:twin
-- Both circles exist, with centres in the upper half plane.
theorem blind_16
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ left right : BlindCircle,
      BlindArchimedesTwins 0 (2 * a) (2 * (a + b)) left right ∧
      left.1.re < 2 * a ∧ 2 * a < right.1.re := by
  sorry

-- thm:area
-- Let a,b>0 and let D be a point of Γ on ℓ.
theorem blind_17
    (a b : ℝ) (D : ℂ) (ha : 0 < a) (hb : 0 < b)
    (hD : D ∈ BlindCirclePoints (BlindDiameterCircle 0 (2 * (a + b))))
    (hline : D.re = 2 * a) :
    volume (BlindArbelos 0 (2 * a) (2 * (a + b))) =
      volume (Metric.ball ((((2 * a : ℝ) : ℂ) + D) / 2)
        (dist ((2 * a : ℝ) : ℂ) D / 2)) := by
  sorry

-- thm:pappus
-- Let a,b>0 and n∈ℕ.
theorem blind_18
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    BlindPappusCircle a b 0 =
      BlindDiameterCircle (2 * a) (2 * (a + b)) := by
  sorry

-- thm:pappus
-- Let a,b>0 and n∈ℕ.
theorem blind_19
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    BlindInternallyTangent (BlindPappusCircle a b n)
      (BlindDiameterCircle 0 (2 * (a + b))) := by
  sorry

-- thm:pappus
-- Let a,b>0 and n∈ℕ.
theorem blind_20
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    BlindExternallyTangent (BlindPappusCircle a b n)
      (BlindDiameterCircle 0 (2 * a)) := by
  sorry

-- thm:pappus
-- Let a,b>0 and n∈ℕ.
theorem blind_21
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    BlindExternallyTangent (BlindPappusCircle a b n)
      (BlindPappusCircle a b (n + 1)) := by
  sorry

-- thm:pappus
-- Let a,b>0 and n∈ℕ.
theorem blind_22
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (BlindPappusCircle a b n).1.im =
      (n : ℝ) * (2 * (BlindPappusCircle a b n).2) := by
  sorry

-- thm:pappus
-- Every circle of positive radius internally tangent to Γ and externally tangent to Γ₁ is φₜ with t equal to its height divided by its diameter.
theorem blind_23
    (a b : ℝ) (s : BlindCircle) (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s.2)
    (houter : BlindInternallyTangent s (BlindDiameterCircle 0 (2 * (a + b))))
    (hinner : BlindExternallyTangent s (BlindDiameterCircle 0 (2 * a))) :
    s = BlindPhi a b (s.1.im / (2 * s.2)) := by
  sorry

-- thm:pappus
-- If (c'ₙ)ₙ∈ℕ is a sequence of circles of positive radius with c'₀=Γ₂, each internally tangent to Γ and externally tangent to Γ₁, consecutive circles externally tangent, c'ₙ₊₂≠c'ₙ for all n, and c'₁ centred in the upper half plane, then c'ₙ=cₙ for all n.
theorem blind_24
    (a b : ℝ) (chain : ℕ → BlindCircle) (ha : 0 < a) (hb : 0 < b)
    (hpos : ∀ n, 0 < (chain n).2)
    (hzero : chain 0 = BlindDiameterCircle (2 * a) (2 * (a + b)))
    (houter : ∀ n, BlindInternallyTangent (chain n)
      (BlindDiameterCircle 0 (2 * (a + b))))
    (hinner : ∀ n, BlindExternallyTangent (chain n)
      (BlindDiameterCircle 0 (2 * a)))
    (hnext : ∀ n, BlindExternallyTangent (chain n) (chain (n + 1)))
    (hdistinct : ∀ n, chain (n + 2) ≠ chain n)
    (hupper : 0 < (chain 1).1.im) :
    ∀ n, chain n = BlindPappusCircle a b n := by
  sorry

-- thm:pappus
-- In the indexing that starts from the incircle, cₙ₊₁, the height is (n+1) times the diameter.
theorem blind_25
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (BlindPappusCircle a b (n + 1)).1.im =
      ((n : ℝ) + 1) * (2 * (BlindPappusCircle a b (n + 1)).2) := by
  sorry

-- thm:pappus
-- The height formula itself is an identity of the family and holds for all real a,b.
theorem blind_26 (a b t : ℝ) :
    (BlindPhi a b t).1.im = t * (2 * (BlindPhi a b t).2) := by
  sorry

-- thm:pappusinv
-- Then ι maps Γ∖{A} onto the line Re z=2a, Γ₁∖{A} onto the line Re z=2(a+b), and cₙ onto the circle of radius b centred at (2a+b)+2nb i.
theorem blind_27
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    BlindPappusInversion a b ''
        (BlindCirclePoints (BlindDiameterCircle 0 (2 * (a + b))) \ {0}) =
      {z : ℂ | z.re = 2 * a} := by
  sorry

-- thm:pappusinv
-- Then ι maps Γ∖{A} onto the line Re z=2a, Γ₁∖{A} onto the line Re z=2(a+b), and cₙ onto the circle of radius b centred at (2a+b)+2nb i.
theorem blind_28
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    BlindPappusInversion a b ''
        (BlindCirclePoints (BlindDiameterCircle 0 (2 * a)) \ {0}) =
      {z : ℂ | z.re = 2 * (a + b)} := by
  sorry

-- thm:pappusinv
-- Then ι maps Γ∖{A} onto the line Re z=2a, Γ₁∖{A} onto the line Re z=2(a+b), and cₙ onto the circle of radius b centred at (2a+b)+2nb i.
theorem blind_29
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    BlindPappusInversion a b '' BlindCirclePoints (BlindPappusCircle a b n) =
      BlindCirclePoints (Complex.mk (2 * a + b) (2 * (n : ℝ) * b), b) := by
  sorry

-- thm:bankoff
-- Let a,b>0.
theorem blind_30
    (a b : ℝ) (s : BlindCircle) (ha : 0 < a) (hb : 0 < b)
    (houter : BlindInternallyTangent s (BlindDiameterCircle 0 (2 * (a + b))))
    (hleft : BlindExternallyTangent s (BlindDiameterCircle 0 (2 * a)))
    (hright : BlindExternallyTangent s
      (BlindDiameterCircle (2 * a) (2 * (a + b))))
    (hupper : 0 < s.1.im) :
    s = BlindPappusCircle a b 1 := by
  sorry

-- thm:steiner
-- Let S₁,S₂ be circles with S₁ of positive radius and strictly inside S₂, i.e. |O₁O₂|<ρ₂−ρ₁.
theorem blind_31
    (S₁ S₂ s₀ : BlindCircle) (n : ℕ) (c : ℕ → BlindCircle)
    (hpos : 0 < S₁.2) (hnested : dist S₁.1 S₂.1 < S₂.2 - S₁.2)
    (hchain : BlindSteinerChain S₁ S₂ n c)
    (hspos : 0 < s₀.2)
    (hsext : BlindExternallyTangent s₀ S₁)
    (hsint : BlindInternallyTangent s₀ S₂) :
    ∃ d : ℕ → BlindCircle, BlindSteinerChain S₁ S₂ n d ∧ d 0 = s₀ := by
  sorry

-- thm:steiner
-- If the given chain is simple, d can be chosen simple; if it is simple with disjoint discs, d can be chosen simple with disjoint discs.
theorem blind_32
    (S₁ S₂ s₀ : BlindCircle) (n : ℕ) (c : ℕ → BlindCircle)
    (hpos : 0 < S₁.2) (hnested : dist S₁.1 S₂.1 < S₂.2 - S₁.2)
    (hn : 3 ≤ n) (hchain : BlindSimpleSteinerChain S₁ S₂ n c)
    (hspos : 0 < s₀.2)
    (hsext : BlindExternallyTangent s₀ S₁)
    (hsint : BlindInternallyTangent s₀ S₂) :
    ∃ d : ℕ → BlindCircle, BlindSimpleSteinerChain S₁ S₂ n d ∧ d 0 = s₀ := by
  sorry

-- thm:steiner
-- If the given chain is simple, d can be chosen simple; if it is simple with disjoint discs, d can be chosen simple with disjoint discs.
theorem blind_33
    (S₁ S₂ s₀ : BlindCircle) (n : ℕ) (c : ℕ → BlindCircle)
    (hpos : 0 < S₁.2) (hnested : dist S₁.1 S₂.1 < S₂.2 - S₁.2)
    (hn : 3 ≤ n)
    (hsimple : BlindSimpleSteinerChain S₁ S₂ n c)
    (hdisjoint : BlindDisjointSteinerChain S₁ S₂ n c)
    (hspos : 0 < s₀.2)
    (hsext : BlindExternallyTangent s₀ S₁)
    (hsint : BlindInternallyTangent s₀ S₂) :
    ∃ d : ℕ → BlindCircle,
      BlindSimpleSteinerChain S₁ S₂ n d ∧
      BlindDisjointSteinerChain S₁ S₂ n d ∧ d 0 = s₀ := by
  sorry

-- thm:steiner
-- The library proves separately the concentric case (where the positivity of the radius of s₀ is not needed), the reduction lemma that for non-concentric nested circles some inversion with centre outside both circles makes them concentric, and that inversion with positive powers preserves external and internal tangency.
-- AMBIGUOUS: Tangency without a positive radius may instead be interpreted using a nonnegative-radius convention.
theorem blind_34
    (S₁ S₂ s₀ : BlindCircle) (n : ℕ) (c : ℕ → BlindCircle)
    (hpos : 0 < S₁.2) (hnested : dist S₁.1 S₂.1 < S₂.2 - S₁.2)
    (hconcentric : S₁.1 = S₂.1)
    (hchain : BlindSteinerChain S₁ S₂ n c)
    (hsext : dist s₀.1 S₁.1 = s₀.2 + S₁.2)
    (hsint : dist s₀.1 S₂.1 + s₀.2 = S₂.2) :
    ∃ d : ℕ → BlindCircle, BlindSteinerChain S₁ S₂ n d ∧ d 0 = s₀ := by
  sorry

-- thm:steiner
-- The library proves separately the concentric case (where the positivity of the radius of s₀ is not needed), the reduction lemma that for non-concentric nested circles some inversion with centre outside both circles makes them concentric, and that inversion with positive powers preserves external and internal tangency.
theorem blind_35
    (S₁ S₂ : BlindCircle)
    (hpos : 0 < S₁.2) (hnested : dist S₁.1 S₂.1 < S₂.2 - S₁.2)
    (hne : S₁.1 ≠ S₂.1) :
    ∃ center : ℂ, ∃ radius : ℝ,
      0 < radius ∧
      0 < BlindPower center S₁ ∧ 0 < BlindPower center S₂ ∧
      (BlindInvertedCircle center radius S₁).1 =
        (BlindInvertedCircle center radius S₂).1 := by
  sorry

-- thm:steiner
-- The library proves separately the concentric case (where the positivity of the radius of s₀ is not needed), the reduction lemma that for non-concentric nested circles some inversion with centre outside both circles makes them concentric, and that inversion with positive powers preserves external and internal tangency.
theorem blind_36
    (center : ℂ) (radius : ℝ) (c d : BlindCircle)
    (hradius : 0 < radius)
    (hc : 0 < BlindPower center c) (hd : 0 < BlindPower center d)
    (htan : BlindExternallyTangent c d) :
    BlindExternallyTangent (BlindInvertedCircle center radius c)
      (BlindInvertedCircle center radius d) := by
  sorry

-- thm:steiner
-- The library proves separately the concentric case (where the positivity of the radius of s₀ is not needed), the reduction lemma that for non-concentric nested circles some inversion with centre outside both circles makes them concentric, and that inversion with positive powers preserves external and internal tangency.
theorem blind_37
    (center : ℂ) (radius : ℝ) (c d : BlindCircle)
    (hradius : 0 < radius)
    (hc : 0 < BlindPower center c) (hd : 0 < BlindPower center d)
    (htan : BlindInternallyTangent c d) :
    BlindInternallyTangent (BlindInvertedCircle center radius c)
      (BlindInvertedCircle center radius d) := by
  sorry

-- proof:pappus
-- The identity that drives everything is |cₜ−cᵤ|²−(ρₜ+ρᵤ)²=4ρₜρᵤ((t−u)²−1).
theorem blind_38
    (a b t u : ℝ) (ha : 0 < a) (hb : 0 < b) :
    dist (BlindPhi a b t).1 (BlindPhi a b u).1 ^ 2 -
        ((BlindPhi a b t).2 + (BlindPhi a b u).2) ^ 2 =
      4 * (BlindPhi a b t).2 * (BlindPhi a b u).2 * ((t - u) ^ 2 - 1) := by
  sorry

-- proof:pappus
-- The identity that drives everything is |cₜ−cᵤ|²−(ρₜ+ρᵤ)²=4ρₜρᵤ((t−u)²−1).
theorem blind_39
    (a b t u : ℝ) (ha : 0 < a) (hb : 0 < b) :
    BlindExternallyTangent (BlindPhi a b t) (BlindPhi a b u) ↔
      |t - u| = 1 := by
  sorry


-- ===== section: circles =====


open scoped BigOperators

def BlindVectorPower {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (X O : V) (R : ℝ) : ℝ :=
  ‖X - O‖ ^ 2 - R ^ 2

def BlindVectorRadicalAxis {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (O₁ O₂ : V) (R₁ R₂ : ℝ) : Set V :=
  {X | BlindVectorPower X O₁ R₁ = BlindVectorPower X O₂ R₂}

def BlindPencilPower {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (O₁ O₂ : V) (R₁ R₂ t : ℝ) (X : V) : ℝ :=
  (1 - t) * BlindVectorPower X O₁ R₁ + t * BlindVectorPower X O₂ R₂

def BlindPerpendicularFoot {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (P X Y D : V) : Prop :=
  (∃ t : ℝ, D = X + t • (Y - X)) ∧
    inner ℝ (P - D) (Y - X) = 0

-- thm:radical
-- In any V, the radical axis of (O₁,R₁) and (O₂,R₂) is the stated level set.
theorem blind_40
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ : V) (R₁ R₂ : ℝ) :
    BlindVectorRadicalAxis O₁ O₂ R₁ R₂ =
      {X | inner ℝ X (O₁ - O₂) =
        (1 / 2 : ℝ) * (‖O₁‖ ^ 2 - ‖O₂‖ ^ 2 - R₁ ^ 2 + R₂ ^ 2)} := by
  sorry

-- thm:radical
-- If O₁ ≠ O₂, the radical axis is an affine subspace with the stated direction.
theorem blind_41
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ : V) (R₁ R₂ : ℝ) (h : O₁ ≠ O₂) :
    BlindVectorRadicalAxis O₁ O₂ R₁ R₂ =
      {X | ∃ w ∈ (Submodule.span ℝ ({O₁ - O₂} : Set V))ᗮ,
        X = ((1 / 2 : ℝ) *
          (‖O₁‖ ^ 2 - ‖O₂‖ ^ 2 - R₁ ^ 2 + R₂ ^ 2) /
          ‖O₁ - O₂‖ ^ 2) • (O₁ - O₂) + w} := by
  sorry

-- thm:radical
-- If O₁ ≠ O₂, the radical axis is a line when dim V = 2.
theorem blind_42
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ : V) (h : O₁ ≠ O₂) (hV : Module.finrank ℝ V = 2) :
    Module.finrank ℝ (Submodule.span ℝ ({O₁ - O₂} : Set V))ᗮ = 1 := by
  sorry

-- thm:radical
-- If dim V = 2 and O₁,O₂,O₃ are not collinear, there is exactly one point on the three pairwise radical axes.
theorem blind_43
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ O₃ : V) (R₁ R₂ R₃ : ℝ)
    (hV : Module.finrank ℝ V = 2)
    (hO : ¬ Collinear ℝ ({O₁, O₂, O₃} : Set V)) :
    ∃! X : V,
      X ∈ BlindVectorRadicalAxis O₁ O₂ R₁ R₂ ∧
      X ∈ BlindVectorRadicalAxis O₂ O₃ R₂ R₃ ∧
      X ∈ BlindVectorRadicalAxis O₃ O₁ R₃ R₁ := by
  sorry

-- thm:coaxal
-- In any V, the member t of the pencil has the stated centre and squared radius.
theorem blind_44
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ X : V) (R₁ R₂ t : ℝ) :
    BlindPencilPower O₁ O₂ R₁ R₂ t X =
      ‖X - ((1 - t) • O₁ + t • O₂)‖ ^ 2 -
        ((1 - t) * R₁ ^ 2 + t * R₂ ^ 2 -
          t * (1 - t) * ‖O₁ - O₂‖ ^ 2) := by
  sorry

-- thm:coaxal
-- Any two members with distinct parameters have the radical axis of the generators.
theorem blind_45
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ : V) (R₁ R₂ t₁ t₂ : ℝ) (h : t₁ ≠ t₂) :
    {X | BlindPencilPower O₁ O₂ R₁ R₂ t₁ X =
        BlindPencilPower O₁ O₂ R₁ R₂ t₂ X} =
      BlindVectorRadicalAxis O₁ O₂ R₁ R₂ := by
  sorry

-- thm:coaxal
-- A common point of the generators lies on every member.
theorem blind_46
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ X : V) (R₁ R₂ t : ℝ)
    (h₁ : dist X O₁ = R₁) (h₂ : dist X O₂ = R₂) :
    BlindPencilPower O₁ O₂ R₁ R₂ t X = 0 := by
  sorry

-- thm:coaxal
-- If dim V = 2 and R₁,R₂ > 0, the circles are orthogonal if and only if the stated power equality holds.
theorem blind_47
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ : V) (R₁ R₂ : ℝ)
    (hV : Module.finrank ℝ V = 2) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) :
    (∃ X : V, dist X O₁ = R₁ ∧ dist X O₂ = R₂ ∧
      inner ℝ (X - O₁) (X - O₂) = 0) ↔
      BlindVectorPower O₁ O₂ R₂ = R₁ ^ 2 := by
  sorry

-- thm:johnson
-- In any V, let three circles of the same radius R have centres O₁,O₂,O₃ and pass through a common point H.
theorem blind_48
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ O₃ H : V) (R : ℝ)
    (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R) :
    let A := O₂ + O₃ - H
    let B := O₃ + O₁ - H
    let C := O₁ + O₂ - H
    let J := O₁ + O₂ + O₃ - (2 : ℝ) • H
    dist A J = R ∧ dist B J = R ∧ dist C J = R := by
  sorry

-- thm:johnson
-- In any V, let three circles of the same radius R have centres O₁,O₂,O₃ and pass through a common point H.
theorem blind_49
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ O₃ H : V) (R : ℝ)
    (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R) :
    let A := O₂ + O₃ - H
    let B := O₃ + O₁ - H
    let C := O₁ + O₂ - H
    dist A O₂ = R ∧ dist A O₃ = R ∧
    dist B O₃ = R ∧ dist B O₁ = R ∧
    dist C O₁ = R ∧ dist C O₂ = R := by
  sorry

-- thm:johnson
-- In the plane, when the circles are distinct and not tangent, these are their second pairwise intersections.
theorem blind_50
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ H : V) (R : ℝ)
    (hV : Module.finrank ℝ V = 2)
    (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R)
    (hne : O₁ ≠ O₂) (htan : dist O₁ O₂ ≠ 2 * R) :
    {X : V | dist X O₁ = R ∧ dist X O₂ = R} =
      ({H, O₁ + O₂ - H} : Set V) ∧
    O₁ + O₂ - H ≠ H := by
  sorry

-- thm:johnson
-- Moreover H is the orthocentre of ABC.
theorem blind_51
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ O₃ H : V) (R : ℝ)
    (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R) :
    let A := O₂ + O₃ - H
    let B := O₃ + O₁ - H
    let C := O₁ + O₂ - H
    inner ℝ (H - A) (C - B) = 0 ∧
    inner ℝ (H - B) (A - C) = 0 ∧
    inner ℝ (H - C) (B - A) = 0 := by
  sorry

-- thm:simson
-- Let |AO|=|BO|=|CO|=R with A,B,C pairwise distinct.
theorem blind_52
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (β : OrthonormalBasis (Fin 2) ℝ V)
    (A B C O P D E F : V) (R : ℝ)
    (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hD : BlindPerpendicularFoot P B C D)
    (hE : BlindPerpendicularFoot P C A E)
    (hF : BlindPerpendicularFoot P A B F) :
    4 * R ^ 2 * BlindCross β (E - D) (F - D) =
      -BlindCross β (B - A) (C - A) * BlindVectorPower P O R := by
  sorry

-- thm:simson
-- If dim V = 2 and A,B,C are not collinear, then D,E,F are collinear if and only if |PO|=R.
theorem blind_53
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C O P D E F : V) (R : ℝ)
    (hV : Module.finrank ℝ V = 2)
    (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set V))
    (hD : BlindPerpendicularFoot P B C D)
    (hE : BlindPerpendicularFoot P C A E)
    (hF : BlindPerpendicularFoot P A B F) :
    Collinear ℝ ({D, E, F} : Set V) ↔ dist P O = R := by
  sorry

-- thm:simson
-- The foot D of the perpendicular from P to the chord XY of the circle |z|=R satisfies the stated identity.
theorem blind_54
    (P X Y D : ℂ) (R : ℝ)
    (hX : ‖X‖ = R) (hY : ‖Y‖ = R) (hXY : X ≠ Y)
    (hD : BlindPerpendicularFoot P X Y D) :
    (2 : ℂ) * (R : ℂ) ^ 2 * D =
      (R : ℂ) ^ 2 * (P + X + Y) - star P * X * Y := by
  sorry

-- thm:steinerline
-- Let dim V=2, |AO|=|BO|=|CO|=|PO|=R with A,B,C pairwise distinct.
theorem blind_55
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C O P D E F : V) (R : ℝ)
    (hV : Module.finrank ℝ V = 2)
    (hA : dist A O = R) (hB : dist B O = R)
    (hC : dist C O = R) (hP : dist P O = R)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hD : BlindPerpendicularFoot P B C D)
    (hE : BlindPerpendicularFoot P C A E)
    (hF : BlindPerpendicularFoot P A B F) :
    Collinear ℝ
      ({A + B + C - (2 : ℝ) • O,
        (2 : ℝ) • D - P, (2 : ℝ) • E - P,
        (2 : ℝ) • F - P} : Set V) := by
  sorry


-- ===== section: inversion =====


open scoped BigOperators

def BlindVectorInversion {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (R : ℝ) (P : V) : V :=
  (R ^ 2 / ‖P‖ ^ 2) • P

def BlindSignedTangency {X : Type*} [MetricSpace X]
    (c d : X) (r s : ℝ) : Prop :=
  dist c d ^ 2 = (r + s) ^ 2

-- thm:ptolemyinv
-- In any V, let P,Q,S≠0 and R≠0.
theorem blind_56
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P Q S : V) (R : ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hS : S ≠ 0) (hR : R ≠ 0) :
    dist (BlindVectorInversion R P) (BlindVectorInversion R Q) +
        dist (BlindVectorInversion R Q) (BlindVectorInversion R S) =
      dist (BlindVectorInversion R P) (BlindVectorInversion R S) ↔
    dist P Q * ‖S‖ + dist Q S * ‖P‖ = dist P S * ‖Q‖ := by
  sorry

-- thm:ptolemyinv
-- In any V, let P,Q,S≠0 and R≠0.
theorem blind_57
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P Q S : V) (R : ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hS : S ≠ 0) (hR : R ≠ 0) :
    dist P S * ‖Q‖ ≤ dist P Q * ‖S‖ + dist Q S * ‖P‖ := by
  sorry

-- thm:ptolemyinv
-- Three points are collinear if and only if one of the three triangle inequalities between them is an equality.
theorem blind_58
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P Q S : V) :
    Collinear ℝ ({P, Q, S} : Set V) ↔
      dist P Q + dist Q S = dist P S ∨
      dist Q S + dist S P = dist Q P ∨
      dist S P + dist P Q = dist S Q := by
  sorry

-- thm:ptolemyinv
-- In ℂ, if 0,P,Q,S lie on one circle (|P-K|=|Q-K|=|S-K|=|K|) with P,Q,S≠0, then P',Q',S' are collinear and one of the three Ptolemy identities holds.
theorem blind_59
    (P Q S K : ℂ) (R : ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hS : S ≠ 0) (hR : R ≠ 0)
    (hPK : ‖P - K‖ = ‖K‖) (hQK : ‖Q - K‖ = ‖K‖)
    (hSK : ‖S - K‖ = ‖K‖) :
    Collinear ℝ
      ({BlindInversion 0 R P, BlindInversion 0 R Q,
        BlindInversion 0 R S} : Set ℂ) := by
  sorry

-- thm:ptolemyinv
-- In ℂ, if 0,P,Q,S lie on one circle (|P-K|=|Q-K|=|S-K|=|K|) with P,Q,S≠0, then P',Q',S' are collinear and one of the three Ptolemy identities holds.
theorem blind_60
    (P Q S K : ℂ) (R : ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hS : S ≠ 0) (hR : R ≠ 0)
    (hPK : ‖P - K‖ = ‖K‖) (hQK : ‖Q - K‖ = ‖K‖)
    (hSK : ‖S - K‖ = ‖K‖) :
    dist P Q * ‖S‖ + dist Q S * ‖P‖ = dist P S * ‖Q‖ ∨
    dist Q S * ‖P‖ + dist S P * ‖Q‖ = dist Q P * ‖S‖ ∨
    dist S P * ‖Q‖ + dist P Q * ‖S‖ = dist S Q * ‖P‖ := by
  sorry

-- thm:peaucellier
-- Under these hypotheses, 0, P, Q are collinear; if moreover P≠Q, then P+Q=A+B and ⟨P,Q⟩=b²-a².
theorem blind_61
    (A B P Q : ℂ) (a b : ℝ)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a) (hAB : A ≠ B) :
    Collinear ℝ ({(0 : ℂ), P, Q} : Set ℂ) := by
  sorry

-- thm:peaucellier
-- Under these hypotheses, 0, P, Q are collinear; if moreover P≠Q, then P+Q=A+B and ⟨P,Q⟩=b²-a².
theorem blind_62
    (A B P Q : ℂ) (a b : ℝ)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a)
    (hAB : A ≠ B) (hPQ : P ≠ Q) :
    P + Q = A + B := by
  sorry

-- thm:peaucellier
-- Under these hypotheses, 0, P, Q are collinear; if moreover P≠Q, then P+Q=A+B and ⟨P,Q⟩=b²-a².
theorem blind_63
    (A B P Q : ℂ) (a b : ℝ)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a)
    (hAB : A ≠ B) (hPQ : P ≠ Q) :
    inner ℝ P Q = b ^ 2 - a ^ 2 := by
  sorry

-- thm:peaucellier
-- If b²-a²=R² (the classical cell), then Q=inv_R(P) and |P||Q|=R²; if moreover P lies on a circle through the pivot, |P-C|=|C|, then Q lies on the line ⟨Q,C⟩=R²/2.
theorem blind_64
    (A B P Q : ℂ) (a b R : ℝ)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a)
    (hAB : A ≠ B) (hPQ : P ≠ Q) (hR : R ≠ 0)
    (hclassical : b ^ 2 - a ^ 2 = R ^ 2) :
    Q = BlindInversion 0 R P := by
  sorry

-- thm:peaucellier
-- If b²-a²=R² (the classical cell), then Q=inv_R(P) and |P||Q|=R²; if moreover P lies on a circle through the pivot, |P-C|=|C|, then Q lies on the line ⟨Q,C⟩=R²/2.
theorem blind_65
    (A B P Q : ℂ) (a b R : ℝ)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a)
    (hAB : A ≠ B) (hPQ : P ≠ Q) (hR : R ≠ 0)
    (hclassical : b ^ 2 - a ^ 2 = R ^ 2) :
    ‖P‖ * ‖Q‖ = R ^ 2 := by
  sorry

-- thm:peaucellier
-- If b²-a²=R² (the classical cell), then Q=inv_R(P) and |P||Q|=R²; if moreover P lies on a circle through the pivot, |P-C|=|C|, then Q lies on the line ⟨Q,C⟩=R²/2.
theorem blind_66
    (A B P Q C : ℂ) (a b R : ℝ)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a)
    (hAB : A ≠ B) (hPQ : P ≠ Q) (hR : R ≠ 0)
    (hclassical : b ^ 2 - a ^ 2 = R ^ 2)
    (hcircle : ‖P - C‖ = ‖C‖) :
    inner ℝ Q C = R ^ 2 / 2 := by
  sorry

-- thm:peaucellier
-- If a²-b²=R², then Q=-inv_R(P), |P||Q|=R², and under |P-C|=|C| the point Q lies on the line ⟨Q,C⟩=-R²/2.
theorem blind_67
    (A B P Q : ℂ) (a b R : ℝ)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a)
    (hAB : A ≠ B) (hPQ : P ≠ Q) (hR : R ≠ 0)
    (hnegative : a ^ 2 - b ^ 2 = R ^ 2) :
    Q = -BlindInversion 0 R P := by
  sorry

-- thm:peaucellier
-- If a²-b²=R², then Q=-inv_R(P), |P||Q|=R², and under |P-C|=|C| the point Q lies on the line ⟨Q,C⟩=-R²/2.
theorem blind_68
    (A B P Q : ℂ) (a b R : ℝ)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a)
    (hAB : A ≠ B) (hPQ : P ≠ Q) (hR : R ≠ 0)
    (hnegative : a ^ 2 - b ^ 2 = R ^ 2) :
    ‖P‖ * ‖Q‖ = R ^ 2 := by
  sorry

-- thm:peaucellier
-- If a²-b²=R², then Q=-inv_R(P), |P||Q|=R², and under |P-C|=|C| the point Q lies on the line ⟨Q,C⟩=-R²/2.
theorem blind_69
    (A B P Q C : ℂ) (a b R : ℝ)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b)
    (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a)
    (hAB : A ≠ B) (hPQ : P ≠ Q) (hR : R ≠ 0)
    (hnegative : a ^ 2 - b ^ 2 = R ^ 2)
    (hcircle : ‖P - C‖ = ‖C‖) :
    inner ℝ Q C = -R ^ 2 / 2 := by
  sorry

-- thm:descartes
-- Let c₁,…,c₄∈ℂ and r₁,…,r₄≠0 with |cᵢcⱼ|²=(rᵢ+rⱼ)² for all i<j.
theorem blind_70
    (c : Fin 4 → ℂ) (r : Fin 4 → ℝ)
    (hr : ∀ i, r i ≠ 0)
    (htangent : ∀ i j, i < j → BlindSignedTangency (c i) (c j) (r i) (r j)) :
    BlindDescartesCurvatures (fun i => BlindCurvature (r i)) := by
  sorry

-- thm:soddy
-- Let c₁,…,c₅∈ℝ³ and r₁,…,r₅≠0 with |cᵢcⱼ|²=(rᵢ+rⱼ)² for all i<j.
theorem blind_71
    (c : Fin 5 → EuclideanSpace ℝ (Fin 3)) (r : Fin 5 → ℝ)
    (hr : ∀ i, r i ≠ 0)
    (htangent : ∀ i j, i < j → BlindSignedTangency (c i) (c j) (r i) (r j)) :
    (∑ i : Fin 5, BlindCurvature (r i)) ^ 2 =
      3 * ∑ i : Fin 5, (BlindCurvature (r i)) ^ 2 := by
  sorry

-- thm:apollonian
-- For reals k₁,…,k₄, the Descartes relation holds if and only if k₁k₂+k₂k₃+k₃k₁≥0 and k₄=k₁+k₂+k₃±2√(k₁k₂+k₂k₃+k₃k₁).
theorem blind_72
    (k₁ k₂ k₃ k₄ : ℝ) :
    BlindDescartesCurvatures ![k₁, k₂, k₃, k₄] ↔
      k₁ * k₂ + k₂ * k₃ + k₃ * k₁ ≥ 0 ∧
        (k₄ = k₁ + k₂ + k₃ + 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ∨
         k₄ = k₁ + k₂ + k₃ - 2 * Real.sqrt (k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) := by
  sorry

-- thm:apollonian
-- Two distinct solutions k⁺ and k⁻ satisfy k⁺+k⁻=2(k₁+k₂+k₃) and k⁺k⁻=2(k₁²+k₂²+k₃²)-(k₁+k₂+k₃)².
theorem blind_73
    (k₁ k₂ k₃ kplus kminus : ℝ)
    (hplus : BlindDescartesCurvatures ![k₁, k₂, k₃, kplus])
    (hminus : BlindDescartesCurvatures ![k₁, k₂, k₃, kminus])
    (hdistinct : kplus ≠ kminus) :
    kplus + kminus = 2 * (k₁ + k₂ + k₃) := by
  sorry

-- thm:apollonian
-- Two distinct solutions k⁺ and k⁻ satisfy k⁺+k⁻=2(k₁+k₂+k₃) and k⁺k⁻=2(k₁²+k₂²+k₃²)-(k₁+k₂+k₃)².
theorem blind_74
    (k₁ k₂ k₃ kplus kminus : ℝ)
    (hplus : BlindDescartesCurvatures ![k₁, k₂, k₃, kplus])
    (hminus : BlindDescartesCurvatures ![k₁, k₂, k₃, kminus])
    (hdistinct : kplus ≠ kminus) :
    kplus * kminus =
      2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) - (k₁ + k₂ + k₃) ^ 2 := by
  sorry

-- thm:apollonian
-- If (k₁,k₂,k₃,k₄) satisfies the relation, so does (k₁,k₂,k₃,2(k₁+k₂+k₃)-k₄).
theorem blind_75
    (k₁ k₂ k₃ k₄ : ℝ)
    (h : BlindDescartesCurvatures ![k₁, k₂, k₃, k₄]) :
    BlindDescartesCurvatures ![k₁, k₂, k₃, 2 * (k₁ + k₂ + k₃) - k₄] := by
  sorry

-- thm:apollonian
-- Consequently every quadruple reached from an integral Descartes quadruple by such moves (in any coordinate, any number of times) is again an integral Descartes quadruple.
theorem blind_76
    (k : Fin 4 → ℝ) (moves : List (Fin 4))
    (hdescartes : BlindDescartesCurvatures k)
    (hintegral : ∀ i, ∃ z : ℤ, k i = (z : ℝ)) :
    BlindDescartesCurvatures
      (moves.foldl (fun current i => BlindApollonianMove current i) k) := by
  sorry

-- thm:apollonian
-- Consequently every quadruple reached from an integral Descartes quadruple by such moves (in any coordinate, any number of times) is again an integral Descartes quadruple.
theorem blind_77
    (k : Fin 4 → ℝ) (moves : List (Fin 4))
    (hdescartes : BlindDescartesCurvatures k)
    (hintegral : ∀ i, ∃ z : ℤ, k i = (z : ℝ)) :
    ∀ i, ∃ z : ℤ,
      (moves.foldl (fun current j => BlindApollonianMove current j) k) i = (z : ℝ) := by
  sorry

-- thm:apollonian
-- An unnamed result in the library checks that the move on the first curvature takes (-1,2,2,3) to (15,2,2,3).
theorem blind_78 :
    BlindApollonianMove ![(-1 : ℝ), 2, 2, 3] 0 = ![(15 : ℝ), 2, 2, 3] := by
  sorry

-- ===== section: bankoff addendum =====


def BlindIsCircle (c : BlindCircle) : Prop :=
  0 < c.2

def BlindUpperHalfPlane (p : ℂ) : Prop :=
  0 < p.im

def BlindExtTangentAtPoint (c d : BlindCircle) (p : ℂ) : Prop :=
  BlindIsCircle c ∧ BlindIsCircle d ∧
    dist c.1 d.1 = c.2 + d.2 ∧
    0 ≤ p.im ∧ BlindCirclePoints c p ∧ BlindCirclePoints d p

def BlindOuterCircle (a b : ℝ) : BlindCircle :=
  (((a + b : ℝ) : ℂ), a + b)

def BlindFirstCircle (a : ℝ) : BlindCircle :=
  ((a : ℂ), a)

def BlindSecondCircle (a b : ℝ) : BlindCircle :=
  (((2 * a + b : ℝ) : ℂ), b)

def BlindCommonPoint (a : ℝ) : ℂ :=
  ((2 * a : ℝ) : ℂ)

def BlindBankoffCircle (a b : ℝ) : BlindCircle :=
  (((2 * a : ℝ) : ℂ) + ((a * b / (a + b) : ℝ) : ℂ) * Complex.I,
    a * b / (a + b))

-- thm:bankoff
-- Let a, b > 0. A circle internally tangent to Gamma, externally tangent
-- to Gamma_1 and Gamma_2, with centre in the upper half plane, is c_1.
theorem blind_79
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (c₁ k : BlindCircle) (T₁ T₂ : ℂ)
    (hupper : BlindUpperHalfPlane c₁.1)
    (hinner : BlindInternallyTangent c₁ (BlindOuterCircle a b))
    (ht₁ : BlindExtTangentAtPoint c₁ (BlindFirstCircle a) T₁)
    (ht₂ : BlindExtTangentAtPoint c₁ (BlindSecondCircle a b) T₂)
    (hk : BlindIsCircle k)
    (hC : BlindCirclePoints k (BlindCommonPoint a))
    (hT₁ : BlindCirclePoints k T₁)
    (hT₂ : BlindCirclePoints k T₂) :
    k.2 = a * b / (a + b) := by
  sorry

-- thm:bankoff
-- Let a, b > 0. A circle internally tangent to Gamma, externally tangent
-- to Gamma_1 and Gamma_2, with centre in the upper half plane, is c_1.
theorem blind_80
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (c₁ : BlindCircle) (T₁ T₂ : ℂ)
    (hupper : BlindUpperHalfPlane c₁.1)
    (hinner : BlindInternallyTangent c₁ (BlindOuterCircle a b))
    (ht₁ : BlindExtTangentAtPoint c₁ (BlindFirstCircle a) T₁)
    (ht₂ : BlindExtTangentAtPoint c₁ (BlindSecondCircle a b) T₂) :
    BlindIsCircle (BlindBankoffCircle a b) ∧
      BlindCirclePoints (BlindBankoffCircle a b) (BlindCommonPoint a) ∧
      BlindCirclePoints (BlindBankoffCircle a b) T₁ ∧
      BlindCirclePoints (BlindBankoffCircle a b) T₂ := by
  sorry
