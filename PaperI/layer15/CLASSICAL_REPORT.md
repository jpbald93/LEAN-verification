# CLASSICAL_REPORT — Layer 15, Paper I (blind classical-source formalisation)

File: `./Classical.lean`. It is byte-identical to `john@100.101.160.66:~/lean/reformalH/PaperIClassical.lean`; both have md5 `fbca7226092426c38804e93228b9526e`.
Namespace `PaperIClassical`. Notation `E2 := EuclideanSpace ℝ (Fin 2)`.

## Statement list (36 theorems, all `:= by sorry`)

| name | item | gloss |
|---|---|---|
| classical_Q1 | Q1 Bretschneider | convex ABCD: area² = ∏(s−side) − abcd·cos²((∠ABC+∠CDA)/2) |
| classical_Q2 | Q2 Brahmagupta | convex + cospherical: area² = ∏(s−side) |
| classical_Q3a | Q3 Pitot (⇒) | convex with incircle ⇒ AB+CD = BC+DA |
| classical_Q3b | Q3 converse (⇐) | convex with AB+CD = BC+DA ⇒ an incircle exists |
| classical_Q4 | Q4 Euler | any 4 points in a real inner-product (torsor) space: Σsides² = AC²+BD²+4MN² |
| classical_Q5 | Q5 Ptolemy II | convex cyclic: AC/BD = (AB·AD+CB·CD)/(BA·BC+DA·DC) |
| classical_Q6 | Q6 van Aubel | in ℂ, positive signed area: centres P,Q,R,S of outward squares satisfy PR = QS and PR ⊥ QS |
| classical_Q7 | Q7 Newton | tangential, not a parallelogram: incentre ∈ line through the diagonal midpoints |
| classical_Q8 | Q8 Fuss | bicentric: 1/(R−d)² + 1/(R+d)² = 1/r² |
| classical_A1a / A1b | A1 Archimedes twins | left / right twin circle has radius ab/(a+b) |
| classical_A2a | A2 | arbelos area (Lebesgue) = π·a·b |
| classical_A2b | A2 | arbelos area = area of the disc with diameter CD |
| classical_A3 | A3 Pappus chain | centre height of cₙ = n·diameter(cₙ) |
| classical_A4 | A4 Bankoff | circle through C and the incircle's two contact points has radius ab/(a+b) |
| classical_A5 | A5 Steiner porism | a closed n-chain exists ⇒ a closed n-chain exists through any circle tangent to both |
| classical_C1 | C1 radical centre | non-collinear centres ⇒ the three radical axes have exactly one common point |
| classical_C2a | C2 coaxal | any two members of a linear pencil have the same radical axis |
| classical_C2b | C2 orthogonality | orthogonal ⇔ d² = r₁²+r₂² |
| classical_C3 | C3 Johnson | the circle through the 3 second intersections has radius r |
| classical_C4 | C4 Simson–Wallace | feet collinear ⇔ P ∈ circumsphere |
| classical_C5a | C5 Steiner line | the reflections of P ∈ circumcircle are collinear |
| classical_C5b | C5 | … and collinear with the orthocentre |
| classical_I1a | I1 | inversion maps E2∖{O} into itself and is an involution there |
| classical_I1b | I1 | distance formula |
| classical_I1c | I1 | a circle not through O maps onto a circle |
| classical_I1d | I1 | a circle through O, minus O, maps onto a line |
| classical_I2a | I2 Ptolemy inequality | AC·BD ≤ AB·CD + BC·DA |
| classical_I2b | I2 equality case | equality ⇔ (concyclic with crossing diagonals) ∨ collinear in cyclic order |
| classical_I3a | I3 Peaucellier | O, P, Q collinear |
| classical_I3b | I3 | OP·OQ = b²−a² |
| classical_I3c | I3 | P on a circle through O ⇒ Q on one fixed line |
| classical_I4 | I4 Descartes | (Σk)² = 2Σk² for four mutually tangent signed circles |
| classical_I5a | I5 Soddy | the fourth curvature is one of k₁+k₂+k₃ ± 2√(…) |
| classical_I5b | I5 Soddy | both values occur, as curvatures of actual tangent circles |
| classical_I5c | I5 Apollonian | integer initial curvatures ⇒ every curvature in the packing is an integer |

## Invented definitions (Mathlib lacks them)

- `ClassicalConvexQuad A B C D`: the diagonals meet at a point strictly inside both (`Sbtw`), and A, B, C are not collinear. This is the textbook characterisation of a non-degenerate convex quadrilateral.
- `ClassicalQuadArea`: `volume` of the convex hull of {A,B,C,D}, which is the area of a convex quadrilateral.
- `ClassicalIsIncircle A B C D O r` / `ClassicalHasIncircle`: r > 0, O lies in the interior of the hull, and `Metric.infDist` from O to each of the four side lines equals r. This is the textbook "tangent to all four side lines, inside".
- `ClassicalParallelogram`: the vectors B−A and C−D are equal.
- `ClassicalSignedArea2` (ℂ): the shoelace sum, used to express "oriented counterclockwise".
- `ClassicalOutwardSquareCentre X Y = (X+Y)/2 − i(Y−X)/2`: the centre of the square on the right of X→Y. For a CCW polygon that side is outward.
- `ClassicalTangentToBoth`, `ClassicalSteinerChain`: a circle in the annulus, externally tangent to the inner circle and internally tangent to the outer. A chain is cyclic tangency of neighbours (`finRotate`) plus pairwise disjoint interiors (tᵢ+tⱼ ≤ dist).
- `ClassicalPower`, `ClassicalRadicalAxis`: power d²−r², and the locus of points with equal power.
- `ClassicalOrthogonal`: the circles meet, and at a common point the angle between the radii is π/2.
- `ClassicalFoot`, `ClassicalReflect`: Mathlib's `EuclideanGeometry.orthogonalProjection` / `reflection` onto `line[ℝ,X,Y]`.
- `ClassicalLineCyclicOrder`: some cyclic rotation of A,B,C,D is monotone along the line, expressed with chained `Sbtw`.
- `ClassicalPeaucellierCell`: the linkage distances, plus A ≠ B and P ≠ Q.
- `ClassicalSignedTangent`, `ClassicalMutuallyTangent`: circles with a signed radius (negative = enclosing, curvature 1/ρ). Two positive circles are externally tangent. A positive circle inside a negative one is internally tangent, which needs ρ₁+ρ₂ < 0. Two negative circles are never tangent. In every case dist of centres = |ρ₁+ρ₂|.
- `ClassicalApollonian init`: an inductive closure. It contains the initial four circles, plus every circle mutually tangent to three circles already in the family.
- `ClassicalArbelos a b` (ℂ): the closed region in the upper half-plane inside the big semicircle and outside both small ones, with A=0, C=2a, B=2a+2b. Fixing these coordinates is a choice of coordinates.

## AMBIGUOUS marks

- **Q6**: for a possibly non-simple quadrilateral, "counterclockwise" is read as positive shoelace area, and "outward" as the right of each directed side.
- **A3**: read literally (c₀ = the arbelos incircle), the claim fails for n = 0. The height of the incircle's centre equals its diameter, not 0. I use the standard Pappus indexing instead: c₀ is the semicircle on CB (height 0) and c₁ is the incircle. Each cₙ (n ≥ 1) is tangent to the big semicircle, to the semicircle on AC and to cₙ₋₁.
- **A5**: "tangent to both" is read as lying in the annulus, the classical Steiner setting.
- **C2a**: the item text is truncated ("2(p + t·u)·…"). I read it as the linear pencil x²+y² − 2(p₁+tu₁)x − 2(p₂+tu₂)y + (q+tv) = 0. The claim is that any two distinct members have the same radical axis.

## EXTRA HYPOTHESIS marks

- **A3** `hnew`: cₙ₊₁ ≠ cₙ₋₁. Both are tangent to the same three circles, so this hypothesis is what encodes "the chain proceeds".
- **I2b**: the four points are pairwise distinct. "Cyclic order" needs distinct points, and A = B trivially gives equality.
- **I3a/I3b/I3c**: A ≠ B and P ≠ Q, built into `ClassicalPeaucellierCell`. Without them the rhombus degenerates and collinearity fails.
- **I3b/I3c**: 0 < a < b (long arms). For b < a the product is a² − b².
- **I5b**: the three given circles have positive radii (mutually externally tangent), and the target curvature κ ≠ 0, since κ = 0 would be a line rather than a circle.

## Compiler summary

`lake env lean PaperIClassical.lean` on the arm64 machine gave **36 `declaration uses 'sorry'` warnings, 0 errors, no other messages**. The first run had one error, from the `⟪·,·⟫_ℝ` notation in Q6; changing it to `⟪·,·⟫` fixed it. No lake update or cache get was run.

## Files read

Only my own outputs: `./Classical.lean`, which I wrote and compiled (its remote copy was only compiled and md5-checked), and `./out.txt`, the captured compiler output. No other files on either machine, no web, no other repositories.
