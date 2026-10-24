import Mathlib

/-!
# Classical complete-quadrilateral and complete-quadrangle statements

Blind formalization from writer_brief.txt only. All theorem proofs are deliberately
admitted. The two construction lemmas are also explicitly admitted: they establish
triangle nondegeneracy from the stated incidence hypotheses, rather than silently
adding nondegeneracy as a new assumption. No theorem here asserts proof completion.

Points are complex numbers with their usual real Euclidean structure. Lines and
triangles, circle centres/radii, parallelism, midpoint and distance are Mathlib's.
A geometric circle is described by its centre and nonnegative radius, not by a
parametrization. No formula is used to select a Miquel or Poncelet point.
-/

noncomputable section
namespace ClassicalSource

abbrev Point := ℂ
abbrev ALine := AffineSubspace ℝ Point

def IsLine (L : ALine) : Prop :=
  ∃ p q : Point, p ≠ q ∧ L = line[ℝ, p, q]

/-- Endpoint presentations are not themselves geometric-line identities. -/
structure PresentedLine where
  p : Point
  q : Point
  distinct : p ≠ q

def PresentedLine.carrier (L : PresentedLine) : ALine := line[ℝ, L.p, L.q]

/-- Mathlib's real Euclidean scalar product on the complex plane. -/
def dot (u v : Point) : ℝ := inner ℝ u v

/-- Mathlib perpendicular projection onto the supporting line. -/
def footThrough (p q z : Point) : Point :=
  letI : Nonempty (line[ℝ, p, q]) := ⟨⟨p, by apply subset_affineSpan; simp⟩⟩
  ↑(EuclideanGeometry.orthogonalProjection (line[ℝ, p, q]) z)

def PresentedLine.foot (L : PresentedLine) (z : Point) : Point :=
  footThrough L.p L.q z

/-- Mathlib reflection in the supporting affine line. -/
def PresentedLine.reflect (L : PresentedLine) (z : Point) : Point :=
  letI : Nonempty L.carrier := ⟨⟨L.p, by change L.p ∈ line[ℝ, L.p, L.q]; apply subset_affineSpan; simp⟩⟩
  EuclideanGeometry.reflection L.carrier z

def PerpendicularLines (L K : ALine) : Prop :=
  ∃ p q r s : Point, p ≠ q ∧ r ≠ s ∧
    L = line[ℝ, p, q] ∧ K = line[ℝ, r, s] ∧ dot (q - p) (s - r) = 0

/-- Total choice; used geometrically only when existence and uniqueness follow
from the nonparallel-line hypotheses. This does not read any external data. -/
def intersection (L K : ALine) : Point :=
  Classical.epsilon (fun z : Point => z ∈ L ∧ z ∈ K)

def omit4 (i : Fin 4) (j : Fin 3) : Fin 4 := i.succAbove j

def omit3 (i : Fin 3) (j : Fin 2) : Fin 3 := i.succAbove j

def OnCircumcircle (t : Affine.Triangle ℝ Point) (z : Point) : Prop :=
  dist z (Affine.Simplex.circumsphere t).center =
    (Affine.Simplex.circumsphere t).radius

def OnNinePointCircle (t : Affine.Triangle ℝ Point) (z : Point) : Prop :=
  dist z (Affine.Simplex.ninePointCircle t).center =
    (Affine.Simplex.ninePointCircle t).radius

def triangleSide (t : Affine.Triangle ℝ Point) (i : Fin 3) : ALine :=
  line[ℝ, t.points (omit3 i 0), t.points (omit3 i 1)]

/-- A genuine focus-directrix parabola; the focus is not on the directrix. -/
structure Parabola where
  focus : Point
  directrix : PresentedLine
  focus_off_directrix : focus ∉ directrix.carrier

def Parabola.locus (P : Parabola) : Set Point :=
  {z | dist z P.focus = Metric.infDist z (P.directrix.carrier : Set Point)}

def Parabola.axis (P : Parabola) : ALine :=
  line[ℝ, P.focus, P.directrix.foot P.focus]

def Parabola.vertex (P : Parabola) : Point :=
  midpoint ℝ P.focus (P.directrix.foot P.focus)

-- AMBIGUOUS: "tangent" could instead mean differential tangency. We use a
-- line with exactly one real intersection, excluding lines parallel to the
-- axis: those also have one intersection but are not tangents. For a genuine
-- real focus-directrix parabola this is the usual tangent-line notion.
def Tangent (P : Parabola) (L : ALine) : Prop :=
  IsLine L ∧ ¬ AffineSubspace.Parallel L P.axis ∧
    ∃! z : Point, z ∈ L ∧ z ∈ P.locus

section CompleteQuadrilateral

/-- Four genuine lines, no parallel pair and no concurrent triple. -/
structure Quadrilateral where
  lines : Fin 4 → PresentedLine
  no_parallel : ∀ i j, i ≠ j →
    ¬ AffineSubspace.Parallel (lines i).carrier (lines j).carrier
  no_three : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ¬ ∃ z : Point, z ∈ (lines i).carrier ∧ z ∈ (lines j).carrier ∧
      z ∈ (lines k).carrier

def Quadrilateral.meet (Q : Quadrilateral) (i j : Fin 4) : Point :=
  intersection (Q.lines i).carrier (Q.lines j).carrier

def Quadrilateral.triangleVertices (Q : Quadrilateral) (i : Fin 4) : Fin 3 → Point :=
  ![Q.meet (omit4 i 1) (omit4 i 2),
    Q.meet (omit4 i 2) (omit4 i 0),
    Q.meet (omit4 i 0) (omit4 i 1)]

/-- Construction obligation, not an additional general-position hypothesis. -/
theorem quadrilateral_triangle_independent (Q : Quadrilateral) (i : Fin 4) :
    AffineIndependent ℝ (Q.triangleVertices i) := by sorry

def Quadrilateral.triangle (Q : Quadrilateral) (i : Fin 4) : Affine.Triangle ℝ Point :=
  ⟨Q.triangleVertices i, quadrilateral_triangle_independent Q i⟩

def IsMiquelPoint (Q : Quadrilateral) (M : Point) : Prop :=
  ∀ i : Fin 4, OnCircumcircle (Q.triangle i) M

def IsOrthocentreLine (Q : Quadrilateral) (L : ALine) : Prop :=
  IsLine L ∧ ∀ i : Fin 4, Affine.Triangle.orthocenter (Q.triangle i) ∈ L

def Quadrilateral.diagonalMidpoints (Q : Quadrilateral) : Fin 3 → Point :=
  ![midpoint ℝ (Q.meet 0 1) (Q.meet 2 3),
    midpoint ℝ (Q.meet 0 2) (Q.meet 1 3),
    midpoint ℝ (Q.meet 0 3) (Q.meet 1 2)]

def IsNewtonGaussLine (Q : Quadrilateral) (L : ALine) : Prop :=
  IsLine L ∧ ∀ i : Fin 3, Q.diagonalMidpoints i ∈ L

def Inscribed (Q : Quadrilateral) (P : Parabola) : Prop :=
  ∀ i : Fin 4, Tangent P (Q.lines i).carrier

/-- Equality here is geometric focus/directrix equality, not endpoint equality. -/
def IsInscribedFocusDirectrix (Q : Quadrilateral) (fd : Point × ALine) : Prop :=
  ∃ P : Parabola, Inscribed Q P ∧ fd = (P.focus, P.directrix.carrier)

/-- C1, background: the Miquel point is characterized by circle incidence. -/
theorem classical_C1 (Q : Quadrilateral) : ∃! M : Point, IsMiquelPoint Q M := by sorry

/-- C2: the four orthocentres lie on a genuine line. -/
theorem classical_C2 (Q : Quadrilateral) :
    ∃ L : ALine, IsOrthocentreLine Q L ∧
      Collinear ℝ (Set.range (fun i : Fin 4 => Affine.Triangle.orthocenter (Q.triangle i))) := by sorry

/-- C3: every reflected Miquel point lies on the orthocentre line. -/
theorem classical_C3 (Q : Quadrilateral) (M : Point) (hM : IsMiquelPoint Q M)
    (L : ALine) (hL : IsOrthocentreLine Q L) :
    (∀ i : Fin 4, (Q.lines i).reflect M ∈ L) ∧
      Collinear ℝ (Set.range (fun i : Fin 4 => (Q.lines i).reflect M)) := by sorry

/-- C4 existence, including the focus and directrix identifications. -/
theorem classical_C4_a (Q : Quadrilateral) :
    ∃ P : Parabola, Inscribed Q P ∧ IsMiquelPoint Q P.focus ∧
      IsOrthocentreLine Q P.directrix.carrier := by sorry

-- AMBIGUOUS: uniqueness of a parabola is geometric, not equality of chosen
-- endpoint presentations of its directrix. We assert unique focus/directrix data.
theorem classical_C4_b (Q : Quadrilateral) :
    ∃! fd : Point × ALine, IsInscribedFocusDirectrix Q fd := by sorry

/-- C4's nonincidence is asserted independently of the Parabola structure. -/
theorem classical_C4_c (Q : Quadrilateral) (M : Point) (hM : IsMiquelPoint Q M)
    (L : ALine) (hL : IsOrthocentreLine Q L) : M ∉ L := by sorry

/-- C5: intrinsic axis/directrix perpendicularity. -/
theorem classical_C5_a (P : Parabola) :
    PerpendicularLines P.axis P.directrix.carrier := by sorry

/-- C5: Newton--Gauss existence and parallelism for the inscribed parabola. -/
theorem classical_C5_b (Q : Quadrilateral) (P : Parabola) (hP : Inscribed Q P) :
    ∃ N : ALine, IsNewtonGaussLine Q N ∧ AffineSubspace.Parallel N P.axis := by sorry

-- AMBIGUOUS: tangent to the "sides" means their full supporting lines, not
-- necessarily tangency on the three closed side segments.
theorem classical_C6_a (t : Affine.Triangle ℝ Point) (P : Parabola)
    (ht : ∀ i : Fin 3, Tangent P (triangleSide t i)) :
    OnCircumcircle t P.focus := by sorry

/-- C6's four-triangle consequence, with no assumed Miquel identification. -/
theorem classical_C6_b (Q : Quadrilateral) (P : Parabola) (hP : Inscribed Q P) :
    IsMiquelPoint Q P.focus := by sorry

-- AMBIGUOUS: "midway between the focus and the directrix" means the midpoint
-- of the focus and its perpendicular foot on the directrix.
theorem classical_C7_a (P : Parabola) :
    P.vertex ∈ P.axis ∧ P.vertex ∈ P.locus ∧
    P.vertex = midpoint ℝ P.focus (P.directrix.foot P.focus) ∧
    dist P.vertex P.focus = Metric.infDist P.vertex (P.directrix.carrier : Set Point) ∧
    Metric.infDist P.vertex (P.directrix.carrier : Set Point) =
      Metric.infDist P.focus (P.directrix.carrier : Set Point) / 2 := by sorry

/-- C7: the vertex is the unique point minimizing distance to the directrix. -/
theorem classical_C7_b (P : Parabola) :
    (∀ z ∈ P.locus,
      Metric.infDist P.vertex (P.directrix.carrier : Set Point) ≤
      Metric.infDist z (P.directrix.carrier : Set Point)) ∧
    (∀ z ∈ P.locus,
      Metric.infDist z (P.directrix.carrier : Set Point) =
      Metric.infDist P.vertex (P.directrix.carrier : Set Point) → z = P.vertex) := by sorry

end CompleteQuadrilateral

section CompleteQuadrangle

/-- Four points; affine independence of each omitted-point triple is precisely
"no three collinear", and also rules out repeated points. -/
structure Quadrangle where
  points : Fin 4 → Point
  no_three_collinear : ∀ i : Fin 4,
    AffineIndependent ℝ (fun j : Fin 3 => points (omit4 i j))

def Quadrangle.triangle (Q : Quadrangle) (i : Fin 4) : Affine.Triangle ℝ Point :=
  ⟨fun j : Fin 3 => Q.points (omit4 i j), Q.no_three_collinear i⟩

def IsPonceletPoint (Q : Quadrangle) (P : Point) : Prop :=
  ∀ i : Fin 4, OnNinePointCircle (Q.triangle i) P

def OrthocentricSystem (Q : Quadrangle) : Prop :=
  ∃ i : Fin 4, Q.points i = Affine.Triangle.orthocenter (Q.triangle i)

/-- A centred rectangular conic with perpendicular asymptote directions u and i*u.
The normalized equation is x*y=k. If k=0, the locus is the two perpendicular
asymptotes themselves; if k!=0 it is a genuine rectangular hyperbola. -/
structure RectangularConic where
  center : Point
  u : Point
  unit_u : dot u u = 1
  k : ℝ

def RectangularConic.locus (H : RectangularConic) : Set Point :=
  {z | dot (z - H.center) H.u * dot (z - H.center) (Complex.I * H.u) = H.k}

/-- Proper rectangular hyperbolas exclude the pair-of-lines degeneration. -/
structure RectangularHyperbola extends RectangularConic where
  nondegenerate : k ≠ 0

def OnFourPoints (Q : Quadrangle) (S : Set Point) : Prop :=
  ∀ i : Fin 4, Q.points i ∈ S

/-- Opposite joins: AB/CD, AC/BD, AD/BC. -/
def Quadrangle.oppositeJoins (Q : Quadrangle) : Fin 3 → ALine × ALine :=
  ![(line[ℝ, Q.points 0, Q.points 1], line[ℝ, Q.points 2, Q.points 3]),
    (line[ℝ, Q.points 0, Q.points 2], line[ℝ, Q.points 1, Q.points 3]),
    (line[ℝ, Q.points 0, Q.points 3], line[ℝ, Q.points 1, Q.points 2])]

/-- Exactly the centres forced to have a degenerate rectangular conic. -/
def IsDegenerateRectangularCenter (Q : Quadrangle) (P : Point) : Prop :=
  ∃ i : Fin 3, PerpendicularLines (Q.oppositeJoins i).1 (Q.oppositeJoins i).2 ∧
    P ∈ (Q.oppositeJoins i).1 ∧ P ∈ (Q.oppositeJoins i).2

def HasFiniteDiagonalTriangle (Q : Quadrangle) : Prop :=
  ∀ i : Fin 3, ¬ AffineSubspace.Parallel (Q.oppositeJoins i).1 (Q.oppositeJoins i).2

def Quadrangle.diagonalVertices (Q : Quadrangle) : Fin 3 → Point :=
  fun i => intersection (Q.oppositeJoins i).1 (Q.oppositeJoins i).2

/-- Construction obligation: noncollinearity follows, and is not assumed anew. -/
theorem diagonal_triangle_independent (Q : Quadrangle) (h : HasFiniteDiagonalTriangle Q) :
    AffineIndependent ℝ Q.diagonalVertices := by sorry

def Quadrangle.diagonalTriangle (Q : Quadrangle) (h : HasFiniteDiagonalTriangle Q) :
    Affine.Triangle ℝ Point :=
  ⟨Q.diagonalVertices, diagonal_triangle_independent Q h⟩

def pedalFeet (t : Affine.Triangle ℝ Point) (z : Point) : Fin 3 → Point :=
  fun i => footThrough (t.points (omit3 i 0)) (t.points (omit3 i 1)) z

/-- Pedal circle means a genuine positive-radius circle through the three feet.
Its centre and radius are specified by incidence, not by a circumcentre formula. -/
def IsPedalCircle (t : Affine.Triangle ℝ Point) (z : Point) (cr : Point × ℝ) : Prop :=
  0 < cr.2 ∧ ∀ i : Fin 3, dist (pedalFeet t z i) cr.1 = cr.2

/-- D1: unconditional existence of a common point of the four nine-point circles. -/
theorem classical_D1_a (Q : Quadrangle) :
    ∃ P : Point, IsPonceletPoint Q P := by sorry

-- EXTRA HYPOTHESIS: uniqueness needs exclusion of the orthocentric system,
-- where D2 makes every point of one positive-radius circle a common point.
theorem classical_D1_b (Q : Quadrangle) (h : ¬ OrthocentricSystem Q) :
    ∃! P : Point, IsPonceletPoint Q P := by sorry

-- AMBIGUOUS: "rectangular hyperbola" sometimes includes a degenerate pair of
-- perpendicular lines. This unconditional version uses that inclusive conic
-- notion; the following version explicitly states the proper-hyperbola reading.
-- AMBIGUOUS: in an orthocentric system there is no distinguished common point;
-- the centre assertion is interpreted pointwise for every common point.
theorem classical_D1_c (Q : Quadrangle) (P : Point) (hP : IsPonceletPoint Q P) :
    ∃ H : RectangularConic, H.center = P ∧ OnFourPoints Q H.locus := by sorry

-- EXTRA HYPOTHESIS: to demand a proper hyperbola centred at the specified P,
-- exclude P being the intersection of perpendicular opposite joins. This is
-- exactly the obstruction, not the stronger exclusion of all orthocentric
-- systems or all perpendicular opposite joins. A degenerate conic consists
-- of two perpendicular lines; no-three-collinear puts two given points on each.
theorem classical_D1_d (Q : Quadrangle) (P : Point) (hP : IsPonceletPoint Q P)
    (h : ¬ IsDegenerateRectangularCenter Q P) :
    ∃ H : RectangularHyperbola,
      H.toRectangularConic.center = P ∧ OnFourPoints Q H.toRectangularConic.locus := by sorry

/-- D2 uses equality of actual Mathlib circles, stronger than just a common point. -/
theorem classical_D2 (Q : Quadrangle) (h : OrthocentricSystem Q) :
    ∀ i j : Fin 4,
      Affine.Simplex.ninePointCircle (Q.triangle i) =
      Affine.Simplex.ninePointCircle (Q.triangle j) := by sorry

-- EXTRA HYPOTHESIS: the omitted point is not on the opposite circumcircle;
-- otherwise its three feet are collinear (Simson), not a genuine pedal circle.
-- The theorem is pointwise in i, so it does not assume nonconcyclicity at any
-- index other than the one whose pedal circle is being asserted.
theorem classical_D3_a (Q : Quadrangle) (P : Point) (hP : IsPonceletPoint Q P)
    (i : Fin 4) (h : ¬ OnCircumcircle (Q.triangle i) (Q.points i)) :
    ∃! cr : Point × ℝ, IsPedalCircle (Q.triangle i) (Q.points i) cr ∧
      dist P cr.1 = cr.2 := by sorry

/-- The same D3 circle incidence in Mathlib's set-based concyclicity language. -/
-- EXTRA HYPOTHESIS: the same Simson degeneracy exclusion as in classical_D3_a.
theorem classical_D3_b (Q : Quadrangle) (P : Point) (hP : IsPonceletPoint Q P)
    (i : Fin 4) (h : ¬ OnCircumcircle (Q.triangle i) (Q.points i)) :
    EuclideanGeometry.Cospherical
      (Set.range (pedalFeet (Q.triangle i) (Q.points i)) ∪ {P}) := by sorry

-- EXTRA HYPOTHESIS: the three opposite-side intersections must be finite;
-- no-three-collinear alone allows parallel opposite sides (e.g. a parallelogram).
-- Their noncollinearity is derived by diagonal_triangle_independent, not assumed.
theorem classical_D4 (Q : Quadrangle) (h : HasFiniteDiagonalTriangle Q)
    (P : Point) (hP : IsPonceletPoint Q P) :
    OnCircumcircle (Q.diagonalTriangle h) P := by sorry

-- AMBIGUOUS: in the orthocentric exception, "the point" cannot denote a unique
-- point. Symmetry is stated for the complete common-point predicate, which is
-- valid both there and in the generic case. Set equality handles all relabellings.
theorem classical_D5_a (Q R : Quadrangle)
    (h : Set.range Q.points = Set.range R.points) (P : Point) :
    IsPonceletPoint Q P ↔ IsPonceletPoint R P := by sorry

-- EXTRA HYPOTHESIS: the single-valued symmetry corollary needs a nonorthocentric
-- quadrangle, for exactly the uniqueness reason in classical_D1_b.
theorem classical_D5_b (Q R : Quadrangle)
    (h : Set.range Q.points = Set.range R.points) (hQ : ¬ OrthocentricSystem Q)
    (P S : Point) (hP : IsPonceletPoint Q P) (hS : IsPonceletPoint R S) :
    P = S := by sorry

end CompleteQuadrangle
end ClassicalSource
