import Mathlib

/-!
# Blind formalisation of "paper G": the Nagel-line family and the symmedian / Brocard points

Written from the redacted prose alone.  Setting (Section "Setting and definitions"):
`V` a real inner product space, `P` a metric space that is a normed torsor over `V`,
`t : Affine.Triangle ℝ P` with `A = t.points 0`, `B = t.points 1`, `C = t.points 2`.
-/

open EuclideanGeometry Affine
open scoped RealInnerProductSpace

noncomputable section

namespace PaperGBlind

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## Common definitions -/

/-- `a = |BC|`. -/
def BlindSideA (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 1) (t.points 2)

/-- `b = |CA|`. -/
def BlindSideB (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 2) (t.points 0)

/-- `c = |AB|`. -/
def BlindSideC (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 0) (t.points 1)

/-- The semiperimeter `s = (a + b + c) / 2`. -/
def BlindSemiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (1 / 2 : ℝ) * (BlindSideA t + BlindSideB t + BlindSideC t)

/-- The centroid `G`. -/
def BlindCentroid (t : Affine.Triangle ℝ P) : P := Finset.univ.centroid ℝ t.points

/-! ## The Nagel line family -/
section NagelLine

/-- The Nagel point `N = ((s-a)A + (s-b)B + (s-c)C)/s`. -/
def BlindNagelPoint (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.affineCombination ℝ t.points
    ![(BlindSemiperimeter t - BlindSideA t) / BlindSemiperimeter t,
      (BlindSemiperimeter t - BlindSideB t) / BlindSemiperimeter t,
      (BlindSemiperimeter t - BlindSideC t) / BlindSemiperimeter t]

/-- The Gergonne point: weights proportional to `1/(s-a), 1/(s-b), 1/(s-c)`, normalised to sum 1. -/
def BlindGergonnePoint (t : Affine.Triangle ℝ P) : P :=
  let s := BlindSemiperimeter t
  let D := 1 / (s - BlindSideA t) + 1 / (s - BlindSideB t) + 1 / (s - BlindSideC t)
  Finset.univ.affineCombination ℝ t.points
    ![(1 / (s - BlindSideA t)) / D, (1 / (s - BlindSideB t)) / D, (1 / (s - BlindSideC t)) / D]

-- AMBIGUOUS: the prose's definition of the Spieker centre is redacted; Theorem thm:spieker
-- identifies it with the incentre of the medial triangle, which is the reading taken here.
-- The other reading: the point with barycentric weights `(b+c) : (c+a) : (a+b)`.
/-- The Spieker centre: the incentre of the medial triangle. -/
def BlindSpiekerCentre (t : Affine.Triangle ℝ P) : P := t.medial.incenter

/-- The de Longchamps point `L = H + 2(O - H)`. -/
def BlindDeLongchampsPoint (t : Affine.Triangle ℝ P) : P :=
  (2 : ℝ) • (t.circumcenter -ᵥ t.orthocenter) +ᵥ t.orthocenter

/-- The anticomplementary triangle: the image of `t` under the homothety with centre `G` and
ratio `-2`. -/
def BlindAnticomplementary (t : Affine.Triangle ℝ P) : Affine.Triangle ℝ P :=
  t.map (AffineMap.homothety (BlindCentroid t) (-2 : ℝ))
    (AffineMap.homothety_injective _ (by norm_num))

-- thm:gergonne: "For every triangle and every vertex i, the Gergonne point lies on the line
-- through vertex i and [the incircle contact point on the opposite side]."
theorem blind_1 (t : Affine.Triangle ℝ P) (i : Fin 3) :
    BlindGergonnePoint t ∈ line[ℝ, t.points i, t.touchpoint ∅ i] := by sorry

-- thm:gergonne (consequence): "Consequently the three cevians to the incircle contact points
-- have a common point."
theorem blind_2 (t : Affine.Triangle ℝ P) :
    ∃ X : P, ∀ i : Fin 3, X ∈ line[ℝ, t.points i, t.touchpoint ∅ i] := by sorry

-- thm:nagel: "For every triangle and every vertex i, the Nagel point lies on the line through
-- vertex i and [the contact point `touchpoint {i} i` of the excircle opposite i]."
theorem blind_3 (t : Affine.Triangle ℝ P) (i : Fin 3) :
    BlindNagelPoint t ∈ line[ℝ, t.points i, t.touchpoint {i} i] := by sorry

-- thm:nagel (consequence): "Consequently the three cevians to the excircle contact points have a
-- common point."
theorem blind_4 (t : Affine.Triangle ℝ P) :
    ∃ X : P, ∀ i : Fin 3, X ∈ line[ℝ, t.points i, t.touchpoint {i} i] := by sorry

-- thm:nagel (betweenness): "Moreover each such contact point lies strictly between the two other
-- vertices."
theorem blind_5 (t : Affine.Triangle ℝ P) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    Sbtw ℝ (t.points j) (t.touchpoint {i} i) (t.points k) := by sorry

-- thm:nagelline: "[redacted main statement] In particular I, G, N are collinear."
-- AMBIGUOUS: the main statement is redacted; reconstructed as the classical
-- `N - G = -2 (I - G)` (G divides IN in ratio 1 : 2). Other reading: some other metric/affine
-- relation among I, G, N (e.g. `|GN| = 2|GI|`).
theorem blind_6 (t : Affine.Triangle ℝ P) :
    BlindNagelPoint t -ᵥ BlindCentroid t = (-2 : ℝ) • (t.incenter -ᵥ BlindCentroid t) := by
  sorry

-- thm:nagelline (collinearity): "In particular I, G, N are collinear."
theorem blind_7 (t : Affine.Triangle ℝ P) :
    Collinear ℝ {t.incenter, BlindCentroid t, BlindNagelPoint t} := by sorry

-- thm:spieker: "For every triangle, the incentre of the medial triangle is the midpoint of I and N."
theorem blind_8 (t : Affine.Triangle ℝ P) :
    t.medial.incenter = midpoint ℝ t.incenter (BlindNagelPoint t) := by sorry

-- thm:spieker (collinearity): "In particular the Spieker centre, I and N are collinear."
theorem blind_9 (t : Affine.Triangle ℝ P) :
    Collinear ℝ {BlindSpiekerCentre t, t.incenter, BlindNagelPoint t} := by sorry

-- thm:delong (i): "For every triangle, with L the de Longchamps point: (i) O is the midpoint of H
-- and L"
theorem blind_10 (t : Affine.Triangle ℝ P) :
    t.circumcenter = midpoint ℝ t.orthocenter (BlindDeLongchampsPoint t) := by sorry

-- thm:delong (ii): "L, O, H are collinear"
theorem blind_11 (t : Affine.Triangle ℝ P) :
    Collinear ℝ {BlindDeLongchampsPoint t, t.circumcenter, t.orthocenter} := by sorry

-- thm:delong (iii): "G, O, L are collinear"
theorem blind_12 (t : Affine.Triangle ℝ P) :
    Collinear ℝ {BlindCentroid t, t.circumcenter, BlindDeLongchampsPoint t} := by sorry

-- thm:delong (iv): "L is the orthocentre of the anticomplementary triangle."
theorem blind_13 (t : Affine.Triangle ℝ P) :
    BlindDeLongchampsPoint t = (BlindAnticomplementary t).orthocenter := by sorry

-- thm:medialnagel: "[statement redacted: Nagel point of the medial triangle]"
-- AMBIGUOUS: the statement is redacted; reconstructed as the classical "the Nagel point of the
-- medial triangle is the incentre I of t". Other reading: it equals the Spieker-type point given
-- by some other formula, or the medial Nagel point is the midpoint of G-type points.
theorem blind_14 (t : Affine.Triangle ℝ P) :
    BlindNagelPoint t.medial = t.incenter := by sorry

-- thm:isotomic: "For every triangle and each side, the midpoint of the incircle contact point and
-- the contact point of the opposite excircle on that side is the midpoint of the side"
theorem blind_15 (t : Affine.Triangle ℝ P) :
    midpoint ℝ (t.touchpoint ∅ 0) (t.touchpoint {0} 0) = midpoint ℝ (t.points 1) (t.points 2) ∧
    midpoint ℝ (t.touchpoint ∅ 1) (t.touchpoint {1} 1) = midpoint ℝ (t.points 2) (t.points 0) ∧
    midpoint ℝ (t.touchpoint ∅ 2) (t.touchpoint {2} 2) = midpoint ℝ (t.points 0) (t.points 1) := by
  sorry

-- thm:anti: "For every triangle, the Nagel point is the incentre of the anticomplementary triangle."
theorem blind_16 (t : Affine.Triangle ℝ P) :
    BlindNagelPoint t = (BlindAnticomplementary t).incenter := by sorry

-- thm:radical: "For every triangle and all i,j ∈ {0,1,2}, the power of the Spieker centre S_p with
-- respect to the excircle opposite vertex i equals its power with respect to the excircle opposite
-- vertex j"
theorem blind_17 (t : Affine.Triangle ℝ P) (i j : Fin 3) :
    (t.exsphere {i}).power (BlindSpiekerCentre t) =
      (t.exsphere {j}).power (BlindSpiekerCentre t) := by sorry

-- thm:radical (common value): "The common value is ¼(s² + (s-a)(s-b)(s-c)/s) = (s² + r²)/4,
-- with r the inradius."
theorem blind_18 (t : Affine.Triangle ℝ P) (i : Fin 3) :
    (t.exsphere {i}).power (BlindSpiekerCentre t) =
        (1 / 4 : ℝ) * (BlindSemiperimeter t ^ 2 +
          (BlindSemiperimeter t - BlindSideA t) * (BlindSemiperimeter t - BlindSideB t) *
            (BlindSemiperimeter t - BlindSideC t) / BlindSemiperimeter t) ∧
      (1 / 4 : ℝ) * (BlindSemiperimeter t ^ 2 +
          (BlindSemiperimeter t - BlindSideA t) * (BlindSemiperimeter t - BlindSideB t) *
            (BlindSemiperimeter t - BlindSideC t) / BlindSemiperimeter t) =
        (BlindSemiperimeter t ^ 2 + t.inradius ^ 2) / 4 := by sorry

end NagelLine

/-! ## The symmedian point and the Brocard points -/
section Brocard

/-- The symmedian point `K = (a²A + b²B + c²C)/(a² + b² + c²)`. -/
def BlindSymmedianPoint (t : Affine.Triangle ℝ P) : P :=
  let a := BlindSideA t
  let b := BlindSideB t
  let c := BlindSideC t
  Finset.univ.affineCombination ℝ t.points
    ![a ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2), b ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2),
      c ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2)]

/-- The first Brocard point `Ω`: weights `1/b², 1/c², 1/a²` on `A, B, C`, normalised by
`1/a² + 1/b² + 1/c²`. -/
def BlindFirstBrocard (t : Affine.Triangle ℝ P) : P :=
  let a := BlindSideA t
  let b := BlindSideB t
  let c := BlindSideC t
  let D := 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2
  Finset.univ.affineCombination ℝ t.points ![(1 / b ^ 2) / D, (1 / c ^ 2) / D, (1 / a ^ 2) / D]

/-- The second Brocard point `Ω'`: weights `1/c², 1/a², 1/b²`, same normalisation. -/
def BlindSecondBrocard (t : Affine.Triangle ℝ P) : P :=
  let a := BlindSideA t
  let b := BlindSideB t
  let c := BlindSideC t
  let D := 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2
  Finset.univ.affineCombination ℝ t.points ![(1 / c ^ 2) / D, (1 / a ^ 2) / D, (1 / b ^ 2) / D]

/-- The area `Δ = ½ |AB| |AC| sin ∠BAC`. -/
def BlindArea (t : Affine.Triangle ℝ P) : ℝ :=
  (1 / 2 : ℝ) * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
    Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))

/-- The six Lemoine points, with `S = a² + b² + c²`. -/
def BlindLemoinePoint (t : Affine.Triangle ℝ P) : Fin 6 → P :=
  let a := BlindSideA t
  let b := BlindSideB t
  let c := BlindSideC t
  let S := a ^ 2 + b ^ 2 + c ^ 2
  let A := t.points 0
  let B := t.points 1
  let C := t.points 2
  ![(a ^ 2 / S) • (A -ᵥ C) +ᵥ C,
    ((b ^ 2 + c ^ 2) / S) • (B -ᵥ A) +ᵥ A,
    ((c ^ 2 + a ^ 2) / S) • (C -ᵥ B) +ᵥ B,
    (b ^ 2 / S) • (B -ᵥ A) +ᵥ A,
    (c ^ 2 / S) • (C -ᵥ B) +ᵥ B,
    ((a ^ 2 + b ^ 2) / S) • (A -ᵥ C) +ᵥ C]

-- AMBIGUOUS: the definition of the pedal feet is redacted; read as the orthogonal projections
-- of X onto the side lines BC, CA, AB. Other reading: projections onto the (closed) sides or
-- Mathlib's simplex face projections (which coincide with these).
/-- Foot of the perpendicular from `X` to the side line `BC`. -/
def BlindPedalFootA (t : Affine.Triangle ℝ P) (X : P) : P :=
  ↑(EuclideanGeometry.orthogonalProjection line[ℝ, t.points 1, t.points 2] X)

/-- Foot of the perpendicular from `X` to the side line `CA`. -/
def BlindPedalFootB (t : Affine.Triangle ℝ P) (X : P) : P :=
  ↑(EuclideanGeometry.orthogonalProjection line[ℝ, t.points 2, t.points 0] X)

/-- Foot of the perpendicular from `X` to the side line `AB`. -/
def BlindPedalFootC (t : Affine.Triangle ℝ P) (X : P) : P :=
  ↑(EuclideanGeometry.orthogonalProjection line[ℝ, t.points 0, t.points 1] X)

/-- The centroid `⅓(F_a + F_b + F_c)` of the pedal triangle of `X`. -/
def BlindPedalCentroid (t : Affine.Triangle ℝ P) (X : P) : P :=
  Finset.univ.centroid ℝ ![BlindPedalFootA t X, BlindPedalFootB t X, BlindPedalFootC t X]

-- thm:symmedian (angles): "For every triangle, with K the symmedian point and M_a, M_b, M_c the
-- midpoints of BC, CA, AB: [six angle equalities]"
theorem blind_19 (t : Affine.Triangle ℝ P) :
    let A := t.points 0
    let B := t.points 1
    let C := t.points 2
    let K := BlindSymmedianPoint t
    let Ma := midpoint ℝ B C
    let Mb := midpoint ℝ C A
    let Mc := midpoint ℝ A B
    ∠ B A K = ∠ Ma A C ∧ ∠ C A K = ∠ Ma A B ∧
    ∠ C B K = ∠ Mb B A ∧ ∠ A B K = ∠ Mb B C ∧
    ∠ A C K = ∠ Mc C B ∧ ∠ B C K = ∠ Mc C A := by sorry

-- thm:symmedian (interiority): "Moreover K is an affine combination of A, B, C with positive
-- weights, that is, it lies in the interior of the triangle."
theorem blind_20 (t : Affine.Triangle ℝ P) :
    ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      BlindSymmedianPoint t = Finset.univ.affineCombination ℝ t.points w := by sorry

-- thm:pedal (i): "For every triangle, K is the centroid of its pedal triangle"
theorem blind_21 (t : Affine.Triangle ℝ P) :
    BlindPedalCentroid t (BlindSymmedianPoint t) = BlindSymmedianPoint t := by sorry

-- thm:pedal (ii): "If moreover dim V = 2, then every point X of the plane that is the centroid of
-- its own pedal triangle is K."
theorem blind_22 (hV : Module.finrank ℝ V = 2) (t : Affine.Triangle ℝ P) (X : P)
    (hX : BlindPedalCentroid t X = X) : X = BlindSymmedianPoint t := by sorry

-- thm:brocard: "For every triangle, the first Brocard point satisfies ∠ΩAB = ∠ΩBC = ∠ΩCA, and the
-- second satisfies ∠Ω'BA = ∠Ω'CB = ∠Ω'AC."
theorem blind_23 (t : Affine.Triangle ℝ P) :
    ∠ (BlindFirstBrocard t) (t.points 0) (t.points 1) =
        ∠ (BlindFirstBrocard t) (t.points 1) (t.points 2) ∧
      ∠ (BlindFirstBrocard t) (t.points 1) (t.points 2) =
        ∠ (BlindFirstBrocard t) (t.points 2) (t.points 0) := by sorry

-- thm:brocard (second point)
theorem blind_24 (t : Affine.Triangle ℝ P) :
    ∠ (BlindSecondBrocard t) (t.points 1) (t.points 0) =
        ∠ (BlindSecondBrocard t) (t.points 2) (t.points 1) ∧
      ∠ (BlindSecondBrocard t) (t.points 2) (t.points 1) =
        ∠ (BlindSecondBrocard t) (t.points 0) (t.points 2) := by sorry

-- thm:cot (cotangent identities): "For every triangle, with ω = ∠ΩAB and the vertex angles ∠BAC,
-- ∠ABC, ∠ACB: cot ω = cot∠BAC + cot∠ABC + cot∠ACB = (a²+b²+c²)/(4Δ), 0 < ω ≤ π/6."
theorem blind_25 (t : Affine.Triangle ℝ P) :
    let A := t.points 0
    let B := t.points 1
    let C := t.points 2
    let ω := ∠ (BlindFirstBrocard t) A B
    Real.cot ω = Real.cot (∠ B A C) + Real.cot (∠ A B C) + Real.cot (∠ A C B) ∧
      Real.cot (∠ B A C) + Real.cot (∠ A B C) + Real.cot (∠ A C B) =
        (BlindSideA t ^ 2 + BlindSideB t ^ 2 + BlindSideC t ^ 2) / (4 * BlindArea t) := by sorry

-- thm:cot (bounds): "0 < ω ≤ π/6"
theorem blind_26 (t : Affine.Triangle ℝ P) :
    0 < ∠ (BlindFirstBrocard t) (t.points 0) (t.points 1) ∧
      ∠ (BlindFirstBrocard t) (t.points 0) (t.points 1) ≤ Real.pi / 6 := by sorry

-- thm:isogonal (angles): "For every triangle, ∠ΩAB = ∠Ω'AC, ∠ΩBC = ∠Ω'BA and ∠ΩCA = ∠Ω'CB;
-- and |OΩ| = |OΩ'|."
theorem blind_27 (t : Affine.Triangle ℝ P) :
    let A := t.points 0
    let B := t.points 1
    let C := t.points 2
    ∠ (BlindFirstBrocard t) A B = ∠ (BlindSecondBrocard t) A C ∧
      ∠ (BlindFirstBrocard t) B C = ∠ (BlindSecondBrocard t) B A ∧
      ∠ (BlindFirstBrocard t) C A = ∠ (BlindSecondBrocard t) C B := by sorry

-- thm:isogonal (equidistance): "|OΩ| = |OΩ'|"
theorem blind_28 (t : Affine.Triangle ℝ P) :
    dist t.circumcenter (BlindFirstBrocard t) = dist t.circumcenter (BlindSecondBrocard t) := by
  sorry

-- thm:brocardcircle (distances): "For every triangle, each of O, K, Ω, Ω' is at distance ½|OK|
-- from the [midpoint of OK]."
-- AMBIGUOUS: the centre is redacted; read as the midpoint of OK (the circle with diameter OK, as in
-- the abstract).
theorem blind_29 (t : Affine.Triangle ℝ P) :
    let O := t.circumcenter
    let K := BlindSymmedianPoint t
    let M := midpoint ℝ O K
    dist O M = (1 / 2 : ℝ) * dist O K ∧ dist K M = (1 / 2 : ℝ) * dist O K ∧
      dist (BlindFirstBrocard t) M = (1 / 2 : ℝ) * dist O K ∧
      dist (BlindSecondBrocard t) M = (1 / 2 : ℝ) * dist O K := by sorry

-- thm:brocardcircle (inner products): "Moreover ⟨O-Ω, K-Ω⟩ = 0 and ⟨O-Ω', K-Ω'⟩ = 0"
theorem blind_30 (t : Affine.Triangle ℝ P) :
    ⟪t.circumcenter -ᵥ BlindFirstBrocard t, BlindSymmedianPoint t -ᵥ BlindFirstBrocard t⟫ = 0 ∧
      ⟪t.circumcenter -ᵥ BlindSecondBrocard t,
        BlindSymmedianPoint t -ᵥ BlindSecondBrocard t⟫ = 0 := by sorry

-- thm:brocardcircle (right angles): "and ∠OΩK = ∠OΩ'K = π/2."
theorem blind_31 (t : Affine.Triangle ℝ P) :
    ∠ t.circumcenter (BlindFirstBrocard t) (BlindSymmedianPoint t) = Real.pi / 2 ∧
      ∠ t.circumcenter (BlindSecondBrocard t) (BlindSymmedianPoint t) = Real.pi / 2 := by sorry

-- thm:degenerate (iff): "For every triangle, Ω = O or Ω = K or Ω' = O or Ω' = K or K = O holds if
-- and only if the triangle is equilateral"
theorem blind_32 (t : Affine.Triangle ℝ P) :
    (BlindFirstBrocard t = t.circumcenter ∨ BlindFirstBrocard t = BlindSymmedianPoint t ∨
        BlindSecondBrocard t = t.circumcenter ∨ BlindSecondBrocard t = BlindSymmedianPoint t ∨
        BlindSymmedianPoint t = t.circumcenter) ↔ t.Equilateral := by sorry

-- thm:degenerate (coincidence): "and if the triangle is equilateral then Ω = Ω' = K = O."
theorem blind_33 (t : Affine.Triangle ℝ P) (h : t.Equilateral) :
    BlindFirstBrocard t = BlindSecondBrocard t ∧ BlindSecondBrocard t = BlindSymmedianPoint t ∧
      BlindSymmedianPoint t = t.circumcenter := by sorry

-- thm:lemoine (equal distances): "For every triangle, the six Lemoine points are all at the same
-- distance from the midpoint of OK"
theorem blind_34 (t : Affine.Triangle ℝ P) (i j : Fin 6) :
    dist (BlindLemoinePoint t i) (midpoint ℝ t.circumcenter (BlindSymmedianPoint t)) =
      dist (BlindLemoinePoint t j) (midpoint ℝ t.circumcenter (BlindSymmedianPoint t)) := by sorry

-- thm:lemoine (cospherical): "in particular they are cospherical."
theorem blind_35 (t : Affine.Triangle ℝ P) :
    Cospherical (Set.range (BlindLemoinePoint t)) := by sorry

-- thm:droz: "Let dim V = 2, let d₁, d₂ ∈ V with ⟨d₁, d₂⟩ = 0, and suppose that neither d₁ nor d₂
-- lies in the direction of any of the three side lines."
theorem blind_36 (hV : Module.finrank ℝ V = 2) (t : Affine.Triangle ℝ P) (d₁ d₂ : V)
    (hd : ⟪d₁, d₂⟫ = 0)
    (h₁BC : d₁ ∉ (line[ℝ, t.points 1, t.points 2]).direction)
    (h₁CA : d₁ ∉ (line[ℝ, t.points 2, t.points 0]).direction)
    (h₁AB : d₁ ∉ (line[ℝ, t.points 0, t.points 1]).direction)
    (h₂BC : d₂ ∉ (line[ℝ, t.points 1, t.points 2]).direction)
    (h₂CA : d₂ ∉ (line[ℝ, t.points 2, t.points 0]).direction)
    (h₂AB : d₂ ∉ (line[ℝ, t.points 0, t.points 1]).direction)
    (X Y : Fin 3 → P)
    (hX1 : X 0 ∈ line[ℝ, t.points 1, t.points 2])
    (hX2 : X 1 ∈ line[ℝ, t.points 2, t.points 0])
    (hX3 : X 2 ∈ line[ℝ, t.points 0, t.points 1])
    (hY1 : Y 0 ∈ line[ℝ, t.points 1, t.points 2])
    (hY2 : Y 1 ∈ line[ℝ, t.points 2, t.points 0])
    (hY3 : Y 2 ∈ line[ℝ, t.points 0, t.points 1])
    (hXH : ∀ k, X k ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁))
    (hYH : ∀ k, Y k ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂)) :
    Collinear ℝ {midpoint ℝ (X 0) (Y 0), midpoint ℝ (X 1) (Y 1), midpoint ℝ (X 2) (Y 2)} := by
  sorry

end Brocard

end PaperGBlind
