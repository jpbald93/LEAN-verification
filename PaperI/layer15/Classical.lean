import Mathlib

/-!
# Paper I — classical statements (blind formalisation)

Every statement is `:= by sorry`. Planar statements live in `EuclideanSpace ℝ (Fin 2)`
(written `E2`) or, where coordinates are natural (arbelos, van Aubel, pencils), in `ℂ`.
-/

open EuclideanGeometry RealInnerProductSpace MeasureTheory

local notation "E2" => EuclideanSpace ℝ (Fin 2)

noncomputable section

namespace PaperIClassical

/-! ## Invented definitions (not available in Mathlib) -/

/-- A (non-degenerate) convex quadrilateral `ABCD`: its diagonals `AC` and `BD` cross at a
point strictly inside both, and the vertices are not all on one line. -/
def ClassicalConvexQuad (A B C D : E2) : Prop :=
  (∃ X : E2, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∧ ¬ Collinear ℝ ({A, B, C} : Set E2)

/-- Area of the convex quadrilateral `ABCD` = Lebesgue measure of its convex hull. -/
def ClassicalQuadArea (A B C D : E2) : ℝ :=
  (volume (convexHull ℝ ({A, B, C, D} : Set E2))).toReal

/-- `O`, `r` are the centre and radius of an inscribed circle of the quadrilateral `ABCD`:
the circle is tangent to the four side lines (distance from `O` to each line is `r`) and its
centre lies inside the quadrilateral. -/
def ClassicalIsIncircle (A B C D O : E2) (r : ℝ) : Prop :=
  0 < r ∧ O ∈ interior (convexHull ℝ ({A, B, C, D} : Set E2)) ∧
    Metric.infDist O (line[ℝ, A, B] : Set E2) = r ∧
    Metric.infDist O (line[ℝ, B, C] : Set E2) = r ∧
    Metric.infDist O (line[ℝ, C, D] : Set E2) = r ∧
    Metric.infDist O (line[ℝ, D, A] : Set E2) = r

/-- The quadrilateral has an inscribed circle. -/
def ClassicalHasIncircle (A B C D : E2) : Prop :=
  ∃ O r, ClassicalIsIncircle A B C D O r

/-- `ABCD` is a parallelogram: `AB` and `DC` are equal as vectors. -/
def ClassicalParallelogram (A B C D : E2) : Prop :=
  B -ᵥ A = C -ᵥ D

/-- Twice the signed (shoelace) area of the quadrilateral `ABCD` in `ℂ`; positive iff the
quadrilateral is oriented counterclockwise. -/
def ClassicalSignedArea2 (A B C D : ℂ) : ℝ :=
  (starRingEnd ℂ A * B).im + (starRingEnd ℂ B * C).im + (starRingEnd ℂ C * D).im +
    (starRingEnd ℂ D * A).im

/-- Centre of the square erected on the side `XY`, on the right of the direction `X → Y`
(i.e. outward for a counterclockwise polygon). -/
def ClassicalOutwardSquareCentre (X Y : ℂ) : ℂ :=
  (X + Y) / 2 - Complex.I * (Y - X) / 2

/-- A circle `(c, t)` lying in the annulus between an outer circle `(O, R)` and an inner
circle `(o, ρ)`, tangent to both (externally to the inner, internally to the outer). -/
def ClassicalTangentToBoth (O : E2) (R : ℝ) (o : E2) (ρ : ℝ) (c : E2) (t : ℝ) : Prop :=
  0 < t ∧ dist c o = ρ + t ∧ dist c O = R - t

/-- A closed Steiner chain of `n` circles: each tangent to both given circles, each tangent
to the next one (cyclically), and with pairwise disjoint interiors. -/
def ClassicalSteinerChain (O : E2) (R : ℝ) (o : E2) (ρ : ℝ) (n : ℕ)
    (c : Fin n → E2) (t : Fin n → ℝ) : Prop :=
  (∀ i, ClassicalTangentToBoth O R o ρ (c i) (t i)) ∧
    (∀ i, dist (c i) (c (finRotate n i)) = t i + t (finRotate n i)) ∧
    (∀ i j, i ≠ j → t i + t j ≤ dist (c i) (c j))

/-- Power of the point `p` with respect to the circle `s`. -/
def ClassicalPower {P : Type*} [MetricSpace P] (s : Sphere P) (p : P) : ℝ :=
  dist p s.center ^ 2 - s.radius ^ 2

/-- Radical axis of two circles: the locus of points with equal power. -/
def ClassicalRadicalAxis {P : Type*} [MetricSpace P] (s₁ s₂ : Sphere P) : Set P :=
  {p | ClassicalPower s₁ p = ClassicalPower s₂ p}

/-- Two circles are orthogonal: they meet, and at a common point the radii are perpendicular
(equivalently, the tangent lines are perpendicular). -/
def ClassicalOrthogonal (s₁ s₂ : Sphere E2) : Prop :=
  ∃ p, p ∈ s₁ ∧ p ∈ s₂ ∧ ∠ s₁.center p s₂.center = Real.pi / 2

/-- Foot of the perpendicular from `P` to the line `XY`. -/
def ClassicalFoot (X Y P : E2) : E2 :=
  (EuclideanGeometry.orthogonalProjection line[ℝ, X, Y] P : E2)

/-- Reflection of `P` in the line `XY`. -/
def ClassicalReflect (X Y P : E2) : E2 :=
  EuclideanGeometry.reflection line[ℝ, X, Y] P

/-- Four distinct collinear points lie on their line in the cyclic order `A, B, C, D`
(some cyclic rotation of `A, B, C, D` is monotone along the line). -/
def ClassicalLineCyclicOrder (A B C D : E2) : Prop :=
  (Sbtw ℝ A B C ∧ Sbtw ℝ B C D) ∨ (Sbtw ℝ B C D ∧ Sbtw ℝ C D A) ∨
    (Sbtw ℝ C D A ∧ Sbtw ℝ D A B) ∨ (Sbtw ℝ D A B ∧ Sbtw ℝ A B C)

/-- The Peaucellier cell: `OA = OB = b`, rhombus `PAQB` of side `a` (`P ≠ Q`, `A ≠ B`). -/
def ClassicalPeaucellierCell (O A B P Q : E2) (a b : ℝ) : Prop :=
  dist O A = b ∧ dist O B = b ∧ dist P A = a ∧ dist A Q = a ∧ dist Q B = a ∧ dist B P = a ∧
    A ≠ B ∧ P ≠ Q

/-- A circle with *signed* radius: `(centre, ρ)`, `ρ ≠ 0`; `ρ < 0` marks an enclosing
circle.  Signed curvature is `1/ρ`.  Two such circles are tangent in the Descartes sense:
both positive → externally tangent; one negative → the positive one is inside the negative
one and internally tangent to it; never both negative. -/
def ClassicalSignedTangent (x y : E2 × ℝ) : Prop :=
  x.2 ≠ 0 ∧ y.2 ≠ 0 ∧ ¬ (x.2 < 0 ∧ y.2 < 0) ∧
    ((x.2 < 0 ∨ y.2 < 0) → x.2 + y.2 < 0) ∧ dist x.1 y.1 = |x.2 + y.2|

/-- `n` mutually tangent circles with signed radii (Descartes configuration for `n = 4`). -/
def ClassicalMutuallyTangent {n : ℕ} (C : Fin n → E2 × ℝ) : Prop :=
  (∀ i, (C i).2 ≠ 0) ∧ ∀ i j, i ≠ j → ClassicalSignedTangent (C i) (C j)

/-- The Apollonian packing generated by a Descartes quadruple: the smallest family of
(signed) circles containing the initial four and containing every circle tangent to any three
mutually tangent circles of the family. -/
inductive ClassicalApollonian (init : Fin 4 → E2 × ℝ) : E2 × ℝ → Prop
  | base (i : Fin 4) : ClassicalApollonian init (init i)
  | step (x y z w : E2 × ℝ) :
      ClassicalApollonian init x → ClassicalApollonian init y → ClassicalApollonian init z →
      ClassicalMutuallyTangent ![x, y, z, w] → ClassicalApollonian init w

/-! ## Quadrilaterals -/

/-- Q1 (Bretschneider). "A convex quadrilateral ABCD with sides a=AB, b=BC, c=CD, d=DA,
semiperimeter s and area K satisfies K² = (s−a)(s−b)(s−c)(s−d) − abcd·cos²((B+D)/2), where
B, D are the interior angles at B and D." -/
theorem classical_Q1 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D) :
    let a := dist A B; let b := dist B C; let c := dist C D; let d := dist D A
    let s := (a + b + c + d) / 2
    ClassicalQuadArea A B C D ^ 2 =
      (s - a) * (s - b) * (s - c) * (s - d) -
        a * b * c * d * Real.cos ((∠ A B C + ∠ C D A) / 2) ^ 2 := by
  sorry

/-- Q2 (Brahmagupta). "If moreover ABCD is cyclic, K² = (s−a)(s−b)(s−c)(s−d)." -/
theorem classical_Q2 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set E2)) :
    let a := dist A B; let b := dist B C; let c := dist C D; let d := dist D A
    let s := (a + b + c + d) / 2
    ClassicalQuadArea A B C D ^ 2 = (s - a) * (s - b) * (s - c) * (s - d) := by
  sorry

/-- Q3a (Pitot). "A convex quadrilateral has an inscribed circle (tangent to all four side
lines, inside) iff AB + CD = BC + DA." — direction (⇒). -/
theorem classical_Q3a (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hin : ClassicalHasIncircle A B C D) :
    dist A B + dist C D = dist B C + dist D A := by
  sorry

/-- Q3b (converse of Pitot). Same item, direction (⇐). -/
theorem classical_Q3b (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (h : dist A B + dist C D = dist B C + dist D A) :
    ClassicalHasIncircle A B C D := by
  sorry

/-- Q4 (Euler's quadrilateral theorem). "For any quadrilateral ABCD with diagonal midpoints
M (of AC) and N (of BD): AB² + BC² + CD² + DA² = AC² + BD² + 4MN². (Any four points in a real
inner-product space.)" -/
theorem classical_Q4 {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C D : P) :
    dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2 =
      dist A C ^ 2 + dist B D ^ 2 + 4 * dist (midpoint ℝ A C) (midpoint ℝ B D) ^ 2 := by
  sorry

/-- Q5 (Ptolemy's second theorem). "For a convex cyclic quadrilateral ABCD:
AC/BD = (AB·AD + CB·CD)/(BA·BC + DA·DC)." -/
theorem classical_Q5 (A B C D : E2) (hconv : ClassicalConvexQuad A B C D)
    (hcyc : Cospherical ({A, B, C, D} : Set E2)) :
    dist A C / dist B D =
      (dist A B * dist A D + dist C B * dist C D) /
        (dist B A * dist B C + dist D A * dist D C) := by
  sorry

/-- Q6 (van Aubel). "Erect squares outward on the sides of a quadrilateral ABCD (oriented
counterclockwise); the segments joining the centres of opposite squares are equal in length
and perpendicular."
-- AMBIGUOUS: for a non-simple quadrilateral "counterclockwise" is read as positive signed
-- (shoelace) area; "outward" = to the right of each directed side. -/
theorem classical_Q6 (A B C D : ℂ) (hccw : 0 < ClassicalSignedArea2 A B C D) :
    let P := ClassicalOutwardSquareCentre A B
    let Q := ClassicalOutwardSquareCentre B C
    let R := ClassicalOutwardSquareCentre C D
    let S := ClassicalOutwardSquareCentre D A
    dist P R = dist Q S ∧ ⟪R - P, S - Q⟫ = 0 := by
  sorry

/-- Q7 (Newton). "In a tangential (convex, with incircle) quadrilateral that is not a
parallelogram, the incentre lies on the line through the midpoints of the two diagonals
(Newton line)." -/
theorem classical_Q7 (A B C D O : E2) (r : ℝ) (hconv : ClassicalConvexQuad A B C D)
    (hin : ClassicalIsIncircle A B C D O r) (hnp : ¬ ClassicalParallelogram A B C D) :
    O ∈ line[ℝ, midpoint ℝ A C, midpoint ℝ B D] := by
  sorry

/-- Q8 (Fuss). "For a bicentric (convex, cyclic and tangential) quadrilateral with
circumradius R, inradius r and distance d between circumcentre and incentre:
1/(R−d)² + 1/(R+d)² = 1/r²." -/
theorem classical_Q8 (A B C D I : E2) (r : ℝ) (Ω : Sphere E2)
    (hconv : ClassicalConvexQuad A B C D)
    (hA : A ∈ Ω) (hB : B ∈ Ω) (hC : C ∈ Ω) (hD : D ∈ Ω)
    (hin : ClassicalIsIncircle A B C D I r) :
    let R := Ω.radius; let d := dist Ω.center I
    1 / (R - d) ^ 2 + 1 / (R + d) ^ 2 = 1 / r ^ 2 := by
  sorry

/-! ## Arbelos

Coordinates in `ℂ`: `A = 0`, `C = 2a`, `B = 2a + 2b` on the real axis, the arbelos in the
closed upper half-plane.  Big semicircle: centre `a + b`, radius `a + b`; small ones: centre
`a`, radius `a` and centre `2a + b`, radius `b`; perpendicular at `C`: `re z = 2a`.
(Placing the segment on the real axis is a choice of coordinates, i.e. up to isometry.) -/

/-- A1a (Archimedes' twin circles), left twin. "In the arbelos on a segment AB with C on it,
AC = 2a, CB = 2b: the two circles inscribed on either side of the perpendicular at C (each
tangent to the perpendicular, to the big semicircle and to one small semicircle) both have
radius ab/(a+b)." -/
theorem classical_A1a (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : 0 < z.im)
    (hperp : z.re + ρ = 2 * a)
    (hbig : dist z ((a + b : ℝ) : ℂ) = a + b - ρ)
    (hsmall : dist z (a : ℂ) = a + ρ) :
    ρ = a * b / (a + b) := by
  sorry

/-- A1b (Archimedes' twin circles), right twin. Same item. -/
theorem classical_A1b (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : 0 < z.im)
    (hperp : z.re - ρ = 2 * a)
    (hbig : dist z ((a + b : ℝ) : ℂ) = a + b - ρ)
    (hsmall : dist z ((2 * a + b : ℝ) : ℂ) = b + ρ) :
    ρ = a * b / (a + b) := by
  sorry

/-- The (closed) arbelos region in the coordinates above. -/
def ClassicalArbelos (a b : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ dist z ((a + b : ℝ) : ℂ) ≤ a + b ∧ a ≤ dist z (a : ℂ) ∧
    b ≤ dist z ((2 * a + b : ℝ) : ℂ)}

/-- A2a (Arbelos area). "The arbelos has area π·ab, …" -/
theorem classical_A2a (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (volume (ClassicalArbelos a b)).toReal = Real.pi * a * b := by
  sorry

/-- A2b. "… equal to the area of the circle with diameter the half-chord CD of the
perpendicular at C." -/
theorem classical_A2b (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (D : ℂ) (hDre : D.re = 2 * a)
    (hDim : 0 < D.im) (hD : dist D ((a + b : ℝ) : ℂ) = a + b) :
    let C : ℂ := ((2 * a : ℝ) : ℂ)
    volume (ClassicalArbelos a b) =
      volume (Metric.closedBall (midpoint ℝ C D) (dist C D / 2)) := by
  sorry

/-- A3 (Pappus chain). "In the arbelos, the chain of circles c₀ (the incircle of the arbelos),
c₁, c₂, …, each tangent to the two outer semicircles and to the previous one: the centre of cₙ
is at height n·(diameter of cₙ) above the line AB."
-- AMBIGUOUS: read literally (c₀ = incircle) the claim fails for n = 0 (height of the incircle
-- centre is its diameter, not 0).  We use the standard Pappus indexing: c₀ is the small
-- semicircle on CB (centre on AB, height 0), c₁ is the incircle of the arbelos, and every cₙ
-- (n ≥ 1) is tangent to the big semicircle (internally), to the semicircle on AC (externally)
-- and to cₙ₋₁ (externally).  "The two outer semicircles" is read as these two.
-- EXTRA HYPOTHESIS: `hnew` — cₙ₊₁ is a new circle, not cₙ₋₁ (both are tangent to the same
-- three circles); this encodes "the chain proceeds". -/
theorem classical_A3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℕ → ℂ) (ρ : ℕ → ℝ)
    (h0 : z 0 = ((2 * a + b : ℝ) : ℂ) ∧ ρ 0 = b)
    (hpos : ∀ n, 1 ≤ n → 0 < ρ n ∧ 0 < (z n).im)
    (hbig : ∀ n, 1 ≤ n → dist (z n) ((a + b : ℝ) : ℂ) = a + b - ρ n)
    (hsmall : ∀ n, 1 ≤ n → dist (z n) (a : ℂ) = a + ρ n)
    (hprev : ∀ n, 1 ≤ n → dist (z n) (z (n - 1)) = ρ n + ρ (n - 1))
    (hnew : ∀ n, 1 ≤ n → (z (n + 1), ρ (n + 1)) ≠ (z (n - 1), ρ (n - 1))) :
    ∀ n : ℕ, (z n).im = n * (2 * ρ n) := by
  sorry

/-- A4 (Bankoff). "The circle through C and the two points where the arbelos incircle touches
the two small semicircles has radius ab/(a+b) (a third Archimedean twin)." -/
theorem classical_A4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : 0 < z.im)
    (hbig : dist z ((a + b : ℝ) : ℂ) = a + b - ρ)
    (hsmall₁ : dist z (a : ℂ) = a + ρ)
    (hsmall₂ : dist z ((2 * a + b : ℝ) : ℂ) = b + ρ)
    (T₁ T₂ : ℂ) (hT₁ : dist T₁ (a : ℂ) = a ∧ dist T₁ z = ρ)
    (hT₂ : dist T₂ ((2 * a + b : ℝ) : ℂ) = b ∧ dist T₂ z = ρ)
    (w : ℂ) (R : ℝ) (hwC : dist w ((2 * a : ℝ) : ℂ) = R) (hw₁ : dist w T₁ = R)
    (hw₂ : dist w T₂ = R) :
    R = a * b / (a + b) := by
  sorry

/-- A5 (Steiner's porism). "Given two circles, one inside the other: if a closed chain of n
circles, each tangent to both and to its neighbours, exists, then a closed chain of n circles
exists starting from any circle tangent to both (circles distinct, interiors disjoint)."
-- AMBIGUOUS: "tangent to both" is read as lying in the annulus (externally tangent to the
-- inner circle, internally tangent to the outer one), the classical Steiner-chain setting. -/
theorem classical_A5 (O o : E2) (R ρ : ℝ) (hρ : 0 < ρ) (hin : dist O o + ρ < R) (n : ℕ)
    (hchain : ∃ c t, ClassicalSteinerChain O R o ρ n c t)
    (c₀ : E2) (t₀ : ℝ) (h₀ : ClassicalTangentToBoth O R o ρ c₀ t₀) :
    ∃ c t, ClassicalSteinerChain O R o ρ n c t ∧ ∃ i, c i = c₀ ∧ t i = t₀ := by
  sorry

/-! ## Circles -/

/-- C1 (Power of a point / radical centre). "The radical axes of three circles with
non-collinear centres, taken in pairs, meet in one point." -/
theorem classical_C1 (s₁ s₂ s₃ : Sphere E2)
    (h : ¬ Collinear ℝ ({s₁.center, s₂.center, s₃.center} : Set E2)) :
    ∃! p : E2, p ∈ ClassicalRadicalAxis s₁ s₂ ∧ p ∈ ClassicalRadicalAxis s₂ s₃ ∧
      p ∈ ClassicalRadicalAxis s₃ s₁ := by
  sorry

/-- C2a (Coaxal circles). "The circles x²+y² − 2(p + t·u)·… of a pencil share one radical
axis; …"
-- AMBIGUOUS: the item is truncated.  Read as the linear pencil
-- x²+y² − 2(p₁+t u₁)x − 2(p₂+t u₂)y + (q + t v) = 0, t ∈ ℝ, written in ℂ with
-- p = p₁ + i p₂, u = u₁ + i u₂: circle t has centre p + t u and radius² = |p + t u|² − (q + t v).
-- Claim: any two (real) members of the pencil have the same radical axis. -/
theorem classical_C2a (p u : ℂ) (q v : ℝ) (t₁ t₂ t₃ t₄ : ℝ) (S₁ S₂ S₃ S₄ : Sphere ℂ)
    (h₁ : S₁.center = p + t₁ * u ∧ S₁.radius ^ 2 = Complex.normSq (p + t₁ * u) - (q + t₁ * v))
    (h₂ : S₂.center = p + t₂ * u ∧ S₂.radius ^ 2 = Complex.normSq (p + t₂ * u) - (q + t₂ * v))
    (h₃ : S₃.center = p + t₃ * u ∧ S₃.radius ^ 2 = Complex.normSq (p + t₃ * u) - (q + t₃ * v))
    (h₄ : S₄.center = p + t₄ * u ∧ S₄.radius ^ 2 = Complex.normSq (p + t₄ * u) - (q + t₄ * v))
    (h₁₂ : t₁ ≠ t₂) (h₃₄ : t₃ ≠ t₄) :
    ClassicalRadicalAxis S₁ S₂ = ClassicalRadicalAxis S₃ S₄ := by
  sorry

/-- C2b. "… two circles are orthogonal iff d² = r₁² + r₂²." -/
theorem classical_C2b (s₁ s₂ : Sphere E2) (h₁ : 0 < s₁.radius) (h₂ : 0 < s₂.radius) :
    ClassicalOrthogonal s₁ s₂ ↔
      dist s₁.center s₂.center ^ 2 = s₁.radius ^ 2 + s₂.radius ^ 2 := by
  sorry

/-- C3 (Johnson). "Three circles of equal radius through a common point H meet pairwise again
at three points; the circle through these three points has the same radius." -/
theorem classical_C3 (H O₁ O₂ O₃ : E2) (r : ℝ)
    (h₁ : dist O₁ H = r) (h₂ : dist O₂ H = r) (h₃ : dist O₃ H = r)
    (h₁₂ : O₁ ≠ O₂) (h₂₃ : O₂ ≠ O₃) (h₁₃ : O₁ ≠ O₃)
    (P₁₂ P₂₃ P₁₃ : E2)
    (hP₁₂ : P₁₂ ≠ H ∧ dist P₁₂ O₁ = r ∧ dist P₁₂ O₂ = r)
    (hP₂₃ : P₂₃ ≠ H ∧ dist P₂₃ O₂ = r ∧ dist P₂₃ O₃ = r)
    (hP₁₃ : P₁₃ ≠ H ∧ dist P₁₃ O₁ = r ∧ dist P₁₃ O₃ = r)
    (w : E2) (R : ℝ) (hw₁ : dist P₁₂ w = R) (hw₂ : dist P₂₃ w = R) (hw₃ : dist P₁₃ w = R) :
    R = r := by
  sorry

/-- C4 (Simson–Wallace). "The feet of the perpendiculars from a point P to the sides of
triangle ABC are collinear iff P lies on the circumcircle." -/
theorem classical_C4 (t : Affine.Triangle ℝ E2) (P : E2) :
    Collinear ℝ ({ClassicalFoot (t.points 1) (t.points 2) P,
        ClassicalFoot (t.points 2) (t.points 0) P,
        ClassicalFoot (t.points 0) (t.points 1) P} : Set E2) ↔
      P ∈ t.circumsphere := by
  sorry

/-- C5a (Steiner line). "The reflections of a point P on the circumcircle in the three side
lines are collinear, …" -/
theorem classical_C5a (t : Affine.Triangle ℝ E2) (P : E2) (hP : P ∈ t.circumsphere) :
    Collinear ℝ ({ClassicalReflect (t.points 1) (t.points 2) P,
        ClassicalReflect (t.points 2) (t.points 0) P,
        ClassicalReflect (t.points 0) (t.points 1) P} : Set E2) := by
  sorry

/-- C5b. "… and the line passes through the orthocentre." -/
theorem classical_C5b (t : Affine.Triangle ℝ E2) (P : E2) (hP : P ∈ t.circumsphere) :
    Collinear ℝ ({ClassicalReflect (t.points 1) (t.points 2) P,
        ClassicalReflect (t.points 2) (t.points 0) P,
        ClassicalReflect (t.points 0) (t.points 1) P, t.orthocenter} : Set E2) := by
  sorry

/-! ## Inversion -/

/-- I1a (Inversion). "Inversion in a circle with centre O and radius k is an involution of the
plane minus O, …" -/
theorem classical_I1a (O : E2) (k : ℝ) (hk : 0 < k) (P : E2) (hP : P ≠ O) :
    inversion O k P ≠ O ∧ inversion O k (inversion O k P) = P := by
  sorry

/-- I1b. "… with |P′Q′| = k²|PQ|/(|OP||OQ|); …" -/
theorem classical_I1b (O : E2) (k : ℝ) (hk : 0 < k) (P Q : E2) (hP : P ≠ O) (hQ : Q ≠ O) :
    dist (inversion O k P) (inversion O k Q) = k ^ 2 * dist P Q / (dist O P * dist O Q) := by
  sorry

/-- I1c. "… it maps circles not through O to circles …" -/
theorem classical_I1c (O : E2) (k : ℝ) (hk : 0 < k) (c : E2) (ρ : ℝ) (hρ : 0 < ρ)
    (hO : dist O c ≠ ρ) :
    ∃ c' : E2, ∃ ρ' : ℝ, 0 < ρ' ∧ inversion O k '' Metric.sphere c ρ = Metric.sphere c' ρ' := by
  sorry

/-- I1d. "… and circles through O to lines." (the circle minus `O` maps onto a line) -/
theorem classical_I1d (O : E2) (k : ℝ) (hk : 0 < k) (c : E2) (ρ : ℝ) (hρ : 0 < ρ)
    (hO : dist O c = ρ) :
    ∃ L : AffineSubspace ℝ E2, Module.finrank ℝ L.direction = 1 ∧
      inversion O k '' (Metric.sphere c ρ \ {O}) = (L : Set E2) := by
  sorry

/-- I2a (Ptolemy via inversion). "For four points, AB·CD + BC·DA ≥ AC·BD, …" -/
theorem classical_I2a (A B C D : E2) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist D A := by
  sorry

/-- I2b. "… with equality iff A, B, C, D are concyclic or collinear in that cyclic order."
-- EXTRA HYPOTHESIS: the four points are pairwise distinct ("cyclic order" needs distinct
-- points, and e.g. A = B always gives equality).
-- Concyclic "in that cyclic order" is expressed as: the diagonals AC, BD cross. -/
theorem classical_I2b (A B C D : E2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    dist A B * dist C D + dist B C * dist D A = dist A C * dist B D ↔
      (Cospherical ({A, B, C, D} : Set E2) ∧ ∃ X : E2, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
        ClassicalLineCyclicOrder A B C D := by
  sorry

/-- I3a (Peaucellier–Lipkin). "In the Peaucellier cell (O fixed; OA = OB = b,
PA = AQ = QB = BP = a), O, P, Q are collinear …"
-- EXTRA HYPOTHESIS (inside `ClassicalPeaucellierCell`): A ≠ B and P ≠ Q (the rhombus PAQB is
-- non-degenerate); without them the claim fails. -/
theorem classical_I3a (O A B P Q : E2) (a b : ℝ) (h : ClassicalPeaucellierCell O A B P Q a b) :
    Collinear ℝ ({O, P, Q} : Set E2) := by
  sorry

/-- I3b. "… and OP·OQ = b² − a²; …"
-- EXTRA HYPOTHESIS: 0 < a < b (long arms; for b < a the product is a² − b²). -/
theorem classical_I3b (O A B P Q : E2) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (h : ClassicalPeaucellierCell O A B P Q a b) :
    dist O P * dist O Q = b ^ 2 - a ^ 2 := by
  sorry

/-- I3c. "… hence if P moves on a circle through O, Q moves on a straight line."
-- EXTRA HYPOTHESIS: 0 < a < b, as in I3b. -/
theorem classical_I3c (O : E2) (a b : ℝ) (ha : 0 < a) (hab : a < b) (c : E2) (ρ : ℝ)
    (hρ : 0 < ρ) (hO : dist O c = ρ) :
    ∃ L : AffineSubspace ℝ E2, Module.finrank ℝ L.direction = 1 ∧
      ∀ A B P Q : E2, ClassicalPeaucellierCell O A B P Q a b → dist P c = ρ → Q ∈ L := by
  sorry

/-- I4 (Descartes). "If four circles are mutually tangent with signed curvatures k₁..k₄
(negative for an enclosing circle): (k₁+k₂+k₃+k₄)² = 2(k₁²+k₂²+k₃²+k₄²)." -/
theorem classical_I4 (C : Fin 4 → E2 × ℝ) (h : ClassicalMutuallyTangent C) :
    (∑ i, 1 / (C i).2) ^ 2 = 2 * ∑ i, (1 / (C i).2) ^ 2 := by
  sorry

/-- I5a (Soddy). "Given three mutually tangent circles, the two possible fourth curvatures are
k₁+k₂+k₃ ± 2√(k₁k₂+k₂k₃+k₃k₁); …" — every fourth circle has one of the two curvatures. -/
theorem classical_I5a (C : Fin 4 → E2 × ℝ) (h : ClassicalMutuallyTangent C) :
    let k := fun i => 1 / (C i).2
    k 3 = k 0 + k 1 + k 2 + 2 * Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0) ∨
      k 3 = k 0 + k 1 + k 2 - 2 * Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0) := by
  sorry

/-- I5b (Soddy), existence: both values occur.
-- EXTRA HYPOTHESIS: the three given circles are mutually externally tangent (positive
-- curvatures), and the value is non-zero (curvature 0 would be a line, not a circle). -/
theorem classical_I5b (C : Fin 3 → E2 × ℝ) (h : ClassicalMutuallyTangent C)
    (hpos : ∀ i, 0 < (C i).2) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    let k := fun i => 1 / (C i).2
    let κ := k 0 + k 1 + k 2 + ε * 2 * Real.sqrt (k 0 * k 1 + k 1 * k 2 + k 2 * k 0)
    κ ≠ 0 → ∃ c : E2, ClassicalMutuallyTangent ![C 0, C 1, C 2, (c, 1 / κ)] := by
  sorry

/-- I5c (Apollonian). "… if the initial four curvatures are integers, all curvatures in the
Apollonian packing are integers." -/
theorem classical_I5c (init : Fin 4 → E2 × ℝ) (h : ClassicalMutuallyTangent init)
    (hint : ∀ i, ∃ n : ℤ, 1 / (init i).2 = n) :
    ∀ x, ClassicalApollonian init x → ∃ n : ℤ, 1 / x.2 = n := by
  sorry

end PaperIClassical
