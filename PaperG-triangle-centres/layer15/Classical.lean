import Mathlib

/-!
# Paper G — classical statements (blind formalisation)

Setting: the Euclidean plane `EuclideanSpace ℝ (Fin 2)`, a non-degenerate triangle `ABC`
(`AffineIndependent ℝ ![A, B, C]`), `a = BC`, `b = CA`, `c = AB`.
Notions missing from Mathlib are defined below with the prefix `Classical`.
-/

open EuclideanGeometry

noncomputable section

namespace PaperGClassical

local notation "Pt" => EuclideanSpace ℝ (Fin 2)

/-! ## Basic definitions -/

/-- The triangle `ABC` as a Mathlib `Affine.Triangle`. -/
def ClassicalTri (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Affine.Triangle ℝ Pt :=
  ⟨![A, B, C], h⟩

/-- The point with (unnormalised) barycentric coordinates `wA : wB : wC` with respect to
`A, B, C` (meaningful when `wA + wB + wC ≠ 0`). -/
def ClassicalBary (A B C : Pt) (wA wB wC : ℝ) : Pt :=
  Finset.univ.affineCombination ℝ ![A, B, C] (fun i => ![wA, wB, wC] i / (wA + wB + wC))

/-- Semiperimeter. -/
def ClassicalSemiperimeter (A B C : Pt) : ℝ := (dist B C + dist C A + dist A B) / 2

/-- Area `Δ = ½·AB·AC·sin A`. -/
def ClassicalArea (A B C : Pt) : ℝ := (1 / 2) * dist A B * dist A C * Real.sin (∠ B A C)

/-- Centroid `G`. (Stated for any three points; also used for pedal triangles.) -/
def ClassicalCentroid (A B C : Pt) : Pt := Finset.univ.centroid ℝ ![A, B, C]

/-- Excentre opposite `A`: barycentrics `-a : b : c` (textbook formula). -/
def ClassicalExcenterA (A B C : Pt) : Pt :=
  ClassicalBary A B C (-dist B C) (dist C A) (dist A B)

/-- Point of contact of the excircle opposite `A` with line `BC`: the foot of the
perpendicular from the excentre to `BC`. -/
def ClassicalExContactA (A B C : Pt) : Pt :=
  (orthogonalProjection line[ℝ, B, C] (ClassicalExcenterA A B C) : Pt)

/-- Exradius `r_a`: distance from the excentre opposite `A` to line `BC`. -/
def ClassicalExradiusA (A B C : Pt) : ℝ :=
  dist (ClassicalExcenterA A B C) (ClassicalExContactA A B C)

/-- Point of contact of the incircle with line `BC`: foot of the perpendicular from the
(Mathlib) incentre to `BC`. -/
def ClassicalInContactA (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Pt :=
  (orthogonalProjection line[ℝ, B, C] (ClassicalTri A B C h).incenter : Pt)

/-- Incircle contact points on `CA` and `AB` (feet of perpendiculars from the same incentre). -/
def ClassicalInContactB (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Pt :=
  (orthogonalProjection line[ℝ, C, A] (ClassicalTri A B C h).incenter : Pt)

def ClassicalInContactC (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Pt :=
  (orthogonalProjection line[ℝ, A, B] (ClassicalTri A B C h).incenter : Pt)

/-- A point (other than `A`, in a non-degenerate triangle) on the internal bisector of angle
`BAC`: `A + AB/|AB| + AC/|AC|`. -/
def ClassicalBisectorPoint (A B C : Pt) : Pt :=
  ((dist A B)⁻¹ • (B -ᵥ A) + (dist A C)⁻¹ • (C -ᵥ A)) +ᵥ A

/-- Reflection of the line `AP` in the internal bisector at `A`
(the isogonal line of `AP` at vertex `A`). -/
def ClassicalIsogonalLine (A B C P : Pt) : AffineSubspace ℝ Pt :=
  line[ℝ, A, reflection line[ℝ, A, ClassicalBisectorPoint A B C] P]

/-- Symmedian through `A`: reflection of the median `A M_a` in the internal bisector at `A`. -/
def ClassicalSymmedian (A B C : Pt) : AffineSubspace ℝ Pt :=
  ClassicalIsogonalLine A B C (midpoint ℝ B C)

/-- `P` and `Q` are isogonal conjugates: for each vertex, the reflection of the line
vertex–`P` in the bisector at that vertex passes through `Q`. -/
def ClassicalIsogonalConj (A B C P Q : Pt) : Prop :=
  Q ∈ ClassicalIsogonalLine A B C P ∧ Q ∈ ClassicalIsogonalLine B C A P ∧
    Q ∈ ClassicalIsogonalLine C A B P

/-- Pedal triangle vertex on line `BC` of a point `P`. -/
def ClassicalFoot (B C P : Pt) : Pt := (orthogonalProjection line[ℝ, B, C] P : Pt)

/-- Centroid of the pedal triangle of `P`. -/
def ClassicalPedalCentroid (A B C P : Pt) : Pt :=
  ClassicalCentroid (ClassicalFoot B C P) (ClassicalFoot C A P) (ClassicalFoot A B P)

/-- Anticomplementary-triangle vertex opposite `A`: reflection of `A` in the midpoint of `BC`
(i.e. `B + C - A`); the triangle of these has `ABC` as medial triangle. -/
def ClassicalAnticompl (A B C : Pt) : Pt := AffineEquiv.pointReflection ℝ (midpoint ℝ B C) A

/-! ## Group N -/

/-- N1 (Gergonne). The lines joining each vertex to the point where the incircle touches the
opposite side are concurrent (Gergonne point Ge). -/
theorem classical_N1 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ Ge : Pt, Ge ∈ line[ℝ, A, ClassicalInContactA A B C h] ∧
      Ge ∈ line[ℝ, B, ClassicalInContactB A B C h] ∧
      Ge ∈ line[ℝ, C, ClassicalInContactC A B C h] := by sorry

/-- N2 (Nagel), concurrency. The lines joining each vertex to the point where the excircle
opposite that vertex touches the opposite side are concurrent (Nagel point Na). -/
theorem classical_N2a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ Na : Pt, Na ∈ line[ℝ, A, ClassicalExContactA A B C] ∧
      Na ∈ line[ℝ, B, ClassicalExContactA B C A] ∧
      Na ∈ line[ℝ, C, ClassicalExContactA C A B] := by sorry

/-- N2 (Nagel), contact distances. The excircle contact point on BC is at distance s−c from B
and s−b from C. -/
theorem classical_N2b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    dist B (ClassicalExContactA A B C) = ClassicalSemiperimeter A B C - dist A B ∧
      dist C (ClassicalExContactA A B C) = ClassicalSemiperimeter A B C - dist C A := by sorry

/-- N3 (Nagel line). I, G, Na are collinear, with G between I and Na and GNa = 2·IG.
(`Na` is characterised as a common point of the three Nagel cevians; two of them already
determine it.) -/
theorem classical_N3 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Na : Pt)
    (hA : Na ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hB : Na ∈ line[ℝ, B, ClassicalExContactA B C A])
    (hC : Na ∈ line[ℝ, C, ClassicalExContactA C A B]) :
    Collinear ℝ {(ClassicalTri A B C h).incenter, ClassicalCentroid A B C, Na} ∧
      Wbtw ℝ (ClassicalTri A B C h).incenter (ClassicalCentroid A B C) Na ∧
      dist (ClassicalCentroid A B C) Na =
        2 * dist (ClassicalTri A B C h).incenter (ClassicalCentroid A B C) := by sorry

/-- N4 (Spieker). The incentre Sp of the medial triangle (Spieker centre) is the midpoint of I
and Na; hence it lies on the Nagel line. -/
theorem classical_N4 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C])
    -- EXTRA HYPOTHESIS: non-degeneracy of the medial triangle (true, provable from h) so that
    -- Mathlib's `incenter` can be applied to it.
    (hM : AffineIndependent ℝ ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B]) (Na : Pt)
    (hA : Na ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hB : Na ∈ line[ℝ, B, ClassicalExContactA B C A])
    (hC : Na ∈ line[ℝ, C, ClassicalExContactA C A B]) :
    (ClassicalTri _ _ _ hM).incenter = midpoint ℝ (ClassicalTri A B C h).incenter Na ∧
      Collinear ℝ {(ClassicalTri A B C h).incenter, ClassicalCentroid A B C, Na,
        (ClassicalTri _ _ _ hM).incenter} := by sorry

/-- N5 (isotomic contacts). On each side, the incircle contact point and the excircle contact
point are symmetric about the midpoint of that side. (Stated for side BC; the other sides are
relabellings.) -/
theorem classical_N5 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    midpoint ℝ (ClassicalInContactA A B C h) (ClassicalExContactA A B C) = midpoint ℝ B C := by
  sorry

/-- N6 (medial), first part. The Nagel point of the medial triangle is the incentre I of ABC. -/
theorem classical_N6a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (X : Pt)
    (hA : X ∈ line[ℝ, midpoint ℝ B C,
      ClassicalExContactA (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)])
    (hB : X ∈ line[ℝ, midpoint ℝ C A,
      ClassicalExContactA (midpoint ℝ C A) (midpoint ℝ A B) (midpoint ℝ B C)])
    (hC : X ∈ line[ℝ, midpoint ℝ A B,
      ClassicalExContactA (midpoint ℝ A B) (midpoint ℝ B C) (midpoint ℝ C A)]) :
    X = (ClassicalTri A B C h).incenter := by sorry

/-- N6 (anticomplementary), second part. The Nagel point of ABC is the incentre of the
anticomplementary triangle (the triangle whose medial triangle is ABC). -/
theorem classical_N6b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C])
    -- EXTRA HYPOTHESIS: non-degeneracy of the anticomplementary triangle (true, provable from
    -- h), needed to apply Mathlib's `incenter`.
    (hT : AffineIndependent ℝ
      ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B])
    (Na : Pt)
    (hA : Na ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hB : Na ∈ line[ℝ, B, ClassicalExContactA B C A])
    (hC : Na ∈ line[ℝ, C, ClassicalExContactA C A B]) :
    Na = (ClassicalTri _ _ _ hT).incenter := by sorry

/-- N7 (de Longchamps). The de Longchamps point L, the reflection of H in O, lies on the Euler
line, and is the orthocentre of the anticomplementary triangle. -/
theorem classical_N7 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C])
    -- EXTRA HYPOTHESIS: non-degeneracy of the anticomplementary triangle (provable from h).
    (hT : AffineIndependent ℝ
      ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B]) :
    -- AMBIGUOUS: "lies on the Euler line" is rendered as collinearity of O, G, H, L (this also
    -- covers the equilateral case, where the Euler line is undefined and O = G = H = L).
    Collinear ℝ {(ClassicalTri A B C h).circumcenter, ClassicalCentroid A B C,
        (ClassicalTri A B C h).orthocenter,
        AffineEquiv.pointReflection ℝ (ClassicalTri A B C h).circumcenter
          (ClassicalTri A B C h).orthocenter} ∧
      AffineEquiv.pointReflection ℝ (ClassicalTri A B C h).circumcenter
          (ClassicalTri A B C h).orthocenter = (ClassicalTri _ _ _ hT).orthocenter := by sorry

/-- N8 (Spieker radical centre). The Spieker centre is the radical centre of the three
excircles (it has equal power with respect to all three). -/
theorem classical_N8 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C])
    -- EXTRA HYPOTHESIS: non-degeneracy of the medial triangle (provable from h).
    (hM : AffineIndependent ℝ ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B]) :
    let Sp := (ClassicalTri _ _ _ hM).incenter
    dist Sp (ClassicalExcenterA A B C) ^ 2 - ClassicalExradiusA A B C ^ 2 =
        dist Sp (ClassicalExcenterA B C A) ^ 2 - ClassicalExradiusA B C A ^ 2 ∧
      dist Sp (ClassicalExcenterA B C A) ^ 2 - ClassicalExradiusA B C A ^ 2 =
        dist Sp (ClassicalExcenterA C A B) ^ 2 - ClassicalExradiusA C A B ^ 2 := by sorry

/-! ## Group S -/

/-- S1 (Lemoine), concurrency and position. The symmedians (reflections of the medians in the
corresponding internal angle bisectors) are concurrent at the symmedian point K, which lies
inside the triangle. -/
theorem classical_S1a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ K : Pt, K ∈ ClassicalSymmedian A B C ∧ K ∈ ClassicalSymmedian B C A ∧
      K ∈ ClassicalSymmedian C A B ∧ K ∈ interior (convexHull ℝ {A, B, C}) := by sorry

/-- S1 (Lemoine), barycentrics. Its barycentric coordinates are a² : b² : c². -/
theorem classical_S1b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (K : Pt)
    (hA : K ∈ ClassicalSymmedian A B C) (hB : K ∈ ClassicalSymmedian B C A)
    (hC : K ∈ ClassicalSymmedian C A B) :
    K = ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2) := by sorry

/-- S2, existence part. K is the centroid of its own pedal triangle. -/
theorem classical_S2a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ClassicalPedalCentroid A B C (ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2)
      (dist A B ^ 2)) = ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2) := by
  sorry

/-- S2, uniqueness part. K is the only point which is the centroid of its own pedal triangle.
-- AMBIGUOUS: uniqueness is taken over all points of the plane (not only interior points). -/
theorem classical_S2b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (P : Pt)
    (hP : ClassicalPedalCentroid A B C P = P) :
    P = ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2) := by sorry

/-- S3 (Brocard), first point. There is a unique point Ω inside the triangle with
∠ΩAB = ∠ΩBC = ∠ΩCA. -/
theorem classical_S3a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃! Ω : Pt, Ω ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A := by sorry

/-- S3 (Brocard), second point. There is a (unique) point Ω′ inside the triangle with
∠Ω′BA = ∠Ω′CB = ∠Ω′AC.
-- AMBIGUOUS: the text says "a second point"; we state existence and uniqueness inside the
-- triangle, by symmetry with the first point. -/
theorem classical_S3b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃! Ω' : Pt, Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C := by sorry

/-- S3 (Brocard), same angle. The second point has the same angle ω. -/
theorem classical_S3c (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω Ω' : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A)
    (hΩ' : Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C) :
    ∠ Ω A B = ∠ Ω' B A := by sorry

/-- S3 (Brocard), cotangent formulas. cot ω = cot A + cot B + cot C = (a²+b²+c²)/(4Δ). -/
theorem classical_S3d (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A) :
    Real.cot (∠ Ω A B) = Real.cot (∠ B A C) + Real.cot (∠ C B A) + Real.cot (∠ A C B) ∧
      Real.cot (∠ B A C) + Real.cot (∠ C B A) + Real.cot (∠ A C B) =
        (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (4 * ClassicalArea A B C) := by sorry

/-- S3 (Brocard), bounds. 0 < ω ≤ π/6. -/
theorem classical_S3e (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A) :
    0 < ∠ Ω A B ∧ ∠ Ω A B ≤ Real.pi / 6 := by sorry

/-- S4. The two Brocard points are isogonal conjugates and are equidistant from O. -/
theorem classical_S4 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω Ω' : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A)
    (hΩ' : Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C) :
    ClassicalIsogonalConj A B C Ω Ω' ∧
      dist Ω (ClassicalTri A B C h).circumcenter = dist Ω' (ClassicalTri A B C h).circumcenter := by
  sorry

/-- S5 (Brocard circle). O, K, Ω, Ω′ lie on the circle with diameter OK.
-- AMBIGUOUS: "the circle with diameter OK" is expressed as: every listed point is at distance
-- OK/2 from the midpoint of OK (for O and K this is automatic; in the equilateral case
-- O = K and the circle degenerates to a point). -/
theorem classical_S5 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω Ω' : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A)
    (hΩ' : Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C) :
    let O := (ClassicalTri A B C h).circumcenter
    let K := ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2)
    dist Ω (midpoint ℝ O K) = dist O K / 2 ∧ dist Ω' (midpoint ℝ O K) = dist O K / 2 := by
  sorry

/-- S6 (first Lemoine circle). The lines through K parallel to the sides meet the sides in six
points that lie on one circle, whose centre is the midpoint of OK.
(`P₁ P₂`: parallel to BC meets AB, AC; `P₃ P₄`: parallel to CA meets BC, BA;
`P₅ P₆`: parallel to AB meets CA, CB. Each such point is unique.)
-- AMBIGUOUS: "sides" read as side lines. -/
theorem classical_S6 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C])
    (P₁ P₂ P₃ P₄ P₅ P₆ : Pt) :
    let K := ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2)
    P₁ ∈ line[ℝ, A, B] → P₁ ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction →
    P₂ ∈ line[ℝ, A, C] → P₂ ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction →
    P₃ ∈ line[ℝ, B, C] → P₃ ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction →
    P₄ ∈ line[ℝ, B, A] → P₄ ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction →
    P₅ ∈ line[ℝ, C, A] → P₅ ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction →
    P₆ ∈ line[ℝ, C, B] → P₆ ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction →
    ∃ ρ : ℝ, ∀ P ∈ ({P₁, P₂, P₃, P₄, P₅, P₆} : Set Pt),
      dist P (midpoint ℝ (ClassicalTri A B C h).circumcenter K) = ρ := by sorry

/-- S7 (Droz-Farny). If two perpendicular lines through H meet the three side lines, the
midpoints of the three segments they cut off on the side lines are collinear.
The lines are `H + ℝ u` and `H + ℝ v` with `⟪u, v⟫ = 0`. -/
theorem classical_S7 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (u v : Pt)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : inner ℝ u v = 0)
    -- EXTRA HYPOTHESIS: neither line is parallel to (or equal to) a side line, i.e. each meets
    -- each side line in exactly one point. Without this, in a right triangle a line through
    -- H = the right-angle vertex can coincide with a side line, the "segment" is not
    -- determined, and the statement (read with arbitrary intersection points) is false.
    (hu₁ : u ∉ (line[ℝ, B, C]).direction) (hu₂ : u ∉ (line[ℝ, C, A]).direction)
    (hu₃ : u ∉ (line[ℝ, A, B]).direction)
    (hv₁ : v ∉ (line[ℝ, B, C]).direction) (hv₂ : v ∉ (line[ℝ, C, A]).direction)
    (hv₃ : v ∉ (line[ℝ, A, B]).direction)
    (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Pt) :
    let H := (ClassicalTri A B C h).orthocenter
    let ℓ₁ := AffineSubspace.mk' H (Submodule.span ℝ {u})
    let ℓ₂ := AffineSubspace.mk' H (Submodule.span ℝ {v})
    X₁ ∈ ℓ₁ → X₁ ∈ line[ℝ, B, C] → X₂ ∈ ℓ₂ → X₂ ∈ line[ℝ, B, C] →
    Y₁ ∈ ℓ₁ → Y₁ ∈ line[ℝ, C, A] → Y₂ ∈ ℓ₂ → Y₂ ∈ line[ℝ, C, A] →
    Z₁ ∈ ℓ₁ → Z₁ ∈ line[ℝ, A, B] → Z₂ ∈ ℓ₂ → Z₂ ∈ line[ℝ, A, B] →
    Collinear ℝ {midpoint ℝ X₁ X₂, midpoint ℝ Y₁ Y₂, midpoint ℝ Z₁ Z₂} := by sorry

end PaperGClassical

end
