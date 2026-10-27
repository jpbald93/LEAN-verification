# Paper G — Classical-source blind formalisation report

File: `./Classical.lean` (namespace `PaperGClassical`). It is identical to `~/lean/reformalG/PaperGClassical.lean` on the Mac, because it was copied there with scp right before the last compile.
Setting: `Pt := EuclideanSpace ℝ (Fin 2)`. Every theorem assumes `h : AffineIndependent ℝ ![A, B, C]` (non-degenerate triangle), with a = `dist B C`, b = `dist C A`, c = `dist A B`.

## Statement list
| Name | Item | Gloss |
|---|---|---|
| classical_N1 | N1 | Some point Ge lies on all three lines A–(incircle contact on BC), B–(contact on CA), C–(contact on AB) |
| classical_N2a | N2 | Some point Na lies on all three lines vertex–(contact point of the excircle opposite that vertex) |
| classical_N2b | N2 | B to the A-excircle contact point = s−c, and C to it = s−b |
| classical_N3 | N3 | For any Na on the three Nagel cevians: I, G, Na are collinear, `Wbtw I G Na`, and GNa = 2·IG |
| classical_N4 | N4 | Incentre of the medial triangle = midpoint(I, Na), and I, G, Na, Sp are collinear |
| classical_N5 | N5 | midpoint(incircle contact, A-excircle contact) = midpoint of BC (side BC; the other sides follow by relabelling) |
| classical_N6a | N6 | Any common point of the medial triangle's three Nagel cevians equals the incentre of ABC |
| classical_N6b | N6 | The Nagel point of ABC = the incentre of the anticomplementary triangle |
| classical_N7 | N7 | O, G, H, L = reflection of H in O are collinear, and L = the orthocentre of the anticomplementary triangle |
| classical_N8 | N8 | The Spieker centre has equal power (d² − r_x²) with respect to the three excircles |
| classical_S1a | S1 | Some K lies on all three symmedians and in the interior of the triangle |
| classical_S1b | S1 | Any common point of the three symmedians = the point with barycentrics a² : b² : c² |
| classical_S2a | S2 | The pedal-triangle centroid of K (a² : b² : c²) is K |
| classical_S2b | S2 | Any P that is the centroid of its own pedal triangle equals K |
| classical_S3a | S3 | There is exactly one interior Ω with ∠ΩAB = ∠ΩBC = ∠ΩCA |
| classical_S3b | S3 | There is exactly one interior Ω′ with ∠Ω′BA = ∠Ω′CB = ∠Ω′AC |
| classical_S3c | S3 | The two Brocard angles are equal: ∠ΩAB = ∠Ω′BA |
| classical_S3d | S3 | cot ω = cot A + cot B + cot C = (a²+b²+c²)/(4Δ) |
| classical_S3e | S3 | 0 < ω ≤ π/6 |
| classical_S4 | S4 | Ω and Ω′ are isogonal conjugates, and dist(Ω, O) = dist(Ω′, O) |
| classical_S5 | S5 | Ω and Ω′ are at distance OK/2 from midpoint(O, K) (for O and K themselves this is trivial) |
| classical_S6 | S6 | The six points where the parallels through K meet the side lines are all equidistant from midpoint(O, K) |
| classical_S7 | S7 | Droz-Farny: for perpendicular lines through H, the midpoints of the three cut-off segments are collinear |

## Invented definitions (prefix `Classical`)
- `ClassicalTri A B C h`: the Mathlib `Affine.Triangle` `⟨![A,B,C], h⟩`. This lets me use Mathlib's `incenter`, `circumcenter` and `orthocenter`.
- `ClassicalBary A B C wA wB wC`: the affine combination with weights wᵢ/Σw. This is the textbook normalised-barycentrics definition.
- `ClassicalSemiperimeter`: (a+b+c)/2.
- `ClassicalArea`: ½·AB·AC·sin A (standard formula, positive for a non-degenerate triangle).
- `ClassicalCentroid`: Mathlib `Finset.centroid` of the three points.
- `ClassicalExcenterA A B C`: the excentre opposite A, defined by the textbook barycentrics −a : b : c. The weight sum b+c−a is > 0 by the triangle inequality. I did not use Mathlib's `Affine.Simplex.excenter` (with its Finset index) because I was not sure which index convention it uses, and my rules forbid reading the source. Excentres opposite B and C are obtained by cyclic relabelling (`ClassicalExcenterA B C A`, …).
- `ClassicalExContactA`: the foot of the perpendicular from that excentre to line BC. This is the tangency point, because the tangent is perpendicular to the radius.
- `ClassicalExradiusA`: the distance from the excentre to its contact point.
- `ClassicalInContactA/B/C`: the feet of the perpendiculars from Mathlib's incentre to BC, CA and AB.
- `ClassicalBisectorPoint A B C`: A + AB/|AB| + AC/|AC|. This point lies on the internal bisector at A.
- `ClassicalIsogonalLine A B C P`: the line through A and the reflection of P in the internal bisector at A. In other words, the line AP reflected in the bisector.
- `ClassicalSymmedian A B C`: the isogonal line of the median, i.e. `ClassicalIsogonalLine A B C (midpoint B C)`. This is exactly the textbook definition.
- `ClassicalIsogonalConj A B C P Q`: Q lies on the reflection of each vertex–P line in that vertex's bisector.
- `ClassicalFoot`, `ClassicalPedalCentroid`: the feet of the perpendiculars to the side lines (`orthogonalProjection`), and the centroid of those three feet.
- `ClassicalAnticompl A B C`: the reflection of A through midpoint(B, C), i.e. B + C − A. The triangle of these points has ABC as its medial triangle.

The Nagel point, Brocard points and symmedian point are never defined as constants. They appear either as universally quantified points satisfying their defining property (N3, N4, N6, S1b, S3c–S6), or via the barycentric formula proved in S1b (S2, S5, S6).

## EXTRA HYPOTHESIS marks
- **N4, N8** `hM`: the medial triangle is affinely independent. This is needed to apply Mathlib's `incenter`, and it follows from `h`.
- **N6b, N7** `hT`: the anticomplementary triangle is affinely independent. Same reason; it also follows from `h`.
- **S7** `hu₁…hv₃`: neither perpendicular line is parallel to a side line. Without this, each line may not meet each side line in exactly one point. In a right triangle, H is a vertex and a line through H can coincide with a side line, so the cut-off segment is undefined and the statement as written would be false. The textbook statement says "meet the three side lines", so I read it as transversal intersection. Also, `u ≠ 0` and `v ≠ 0` are part of what "line" means.

## AMBIGUOUS marks
- **N7**: "lies on the Euler line" is stated as `Collinear {O, G, H, L}`. This also covers the equilateral case, where there is no Euler line.
- **S2b**: uniqueness is over all points of the plane, not only interior ones. This is the stronger reading, and I believe it is true because the pedal-centroid map is an affine contraction-like map.
- **S3b**: "a second point Ω′" is stated with existence and uniqueness inside the triangle, mirroring S3a.
- **S5**: "the circle with diameter OK" is expressed as distance OK/2 from midpoint(O, K). In the equilateral case this circle degenerates to a point.
- **S6**: "sides" is read as side lines.

## Compiler summary
`lake env lean PaperGClassical.lean` on the Mac gives **23 warnings, all `declaration uses 'sorry'` (one per theorem), and 0 errors**.

## Files read
- I read no files on either machine apart from my own: `./Classical.lean` and `./CLASSICAL_REPORT.md`.
- `ls` of the working directory showed `brief.txt` and `run.log`; I did not open either.
- On the Mac I only ran scp/ssh to compile my own file. Early on I compiled a probe version of `Classical.lean` containing `#check` commands. That printed the type signatures of Mathlib constants, but I opened no Mathlib source files.
- I did no web searches.
