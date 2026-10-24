# Layer 15 — Classical-source blind writer report

## Completion and compilation

- Local deliverable: `<oc>/tmp/l15f/w/Classical.lean`.
- Jack deliverable: `jack:~/reformal/PaperFClassical.lean`.
- Final compilation: **exit 0; 24 `declaration uses 'sorry'` warnings; 0 errors; no other messages**.
- The 24 admissions comprise **22 classical theorem statements and 2 triangle-construction obligations**. These are type-checked statements, not proved theorems.
- The remote deliverable was copied back to `Classical.jack-copy.lean`; `cmp` confirmed byte-for-byte identity with the local deliverable.
- SHA-256 of both copies: `afe16593f65ef05be32ba0cab87257fb82b0c76509eca6930fc2095d68441062`.
- Final compiler output is preserved in `<oc>/tmp/l15f/w/COMPILER_OUTPUT.txt`.
- Four compile iterations were performed. The initial unknown `Complex.conj` name and the subsequent line-membership proof errors were fixed. The final definitions use Mathlib's real inner product, perpendicular projection, and reflection; no coordinate-formula substitutes remain for these operations.

Compiler command:

```sh
ssh -o BatchMode=yes jack 'cd ~/reformal && PATH=$HOME/.elan/bin:$PATH timeout 900 lake env lean PaperFClassical.lean'
```

## Statement list

All names are in namespace `ClassicalSource`. Each listed theorem ends with `:= by sorry`.

| Name | Classical item | Statement |
|---|---|---|
| `classical_C1` | C1, optional background | There exists exactly one point on all four triangle circumcircles. |
| `classical_C2` | C2 | There exists a genuine line containing all four orthocentres; their range is `Collinear ℝ`. |
| `classical_C3` | C3 | Every reflection of a Miquel point in the four lines belongs to the orthocentre line; the reflections are collinear. |
| `classical_C4_a` | C4, existence | There exists a parabola tangent to all four lines whose focus is a Miquel point and whose directrix is an orthocentre line. |
| `classical_C4_b` | C4, uniqueness | The geometric focus/directrix pair of an inscribed parabola is unique. |
| `classical_C4_c` | C4, nonincidence | A Miquel point does not lie on an orthocentre line, independently of the parabola structure's nondegeneracy field. |
| `classical_C5_a` | C5, intrinsic axis | Every parabola's axis is perpendicular to its directrix. |
| `classical_C5_b` | C5, Newton–Gauss | There exists a line through the three diagonal midpoints parallel to the inscribed parabola's axis. |
| `classical_C6_a` | C6, Lambert | A parabola tangent to all three triangle supporting lines has its focus on the triangle circumcircle. |
| `classical_C6_b` | C6, consequence | The focus of any parabola inscribed in the quadrilateral satisfies the Miquel-point predicate. |
| `classical_C7_a` | C7, vertex | The vertex belongs to the axis and parabola, is the focus/foot midpoint, and has half the focus-to-directrix distance. |
| `classical_C7_b` | C7, minimization | The vertex uniquely minimizes distance to the directrix among parabola points. |
| `classical_D1_a` | D1, existence | There exists a common point of the four nine-point circles. |
| `classical_D1_b` | D1, uniqueness | Outside the orthocentric exception, the common point is unique. |
| `classical_D1_c` | D1, conic centre | Every common point is the centre of a rectangular conic through the four points, permitting perpendicular-line degeneration. |
| `classical_D1_d` | D1, proper hyperbola | A common point not at a perpendicular-opposite-join intersection is the centre of a proper rectangular hyperbola through the points. |
| `classical_D2` | D2 | In an orthocentric system the actual four Mathlib nine-point circles are equal. |
| `classical_D3_a` | D3 | With Simson degeneracy excluded, the omitted point has a unique pedal circle through the Poncelet point. |
| `classical_D3_b` | D3, concyclicity | The three pedal feet together with the Poncelet point are `EuclideanGeometry.Cospherical`. |
| `classical_D4` | D4 | When the three opposite-side intersections are finite, the Poncelet point lies on their triangle's circumcircle. |
| `classical_D5_a` | D5, unconditional symmetry | Equal unordered vertex sets give equivalent common-point predicates, including the orthocentric exception. |
| `classical_D5_b` | D5, single-valued symmetry | For a nonorthocentric quadrangle, common points obtained from any two labellings are equal. |

The source has one named section for each setting: `CompleteQuadrilateral` and `CompleteQuadrangle`. Shared definitions precede them in a noncomputable namespace context.

## Definitions introduced and their justification

The following list covers all explicit abbreviations, structures, and definitions introduced in the source; automatically generated structure projections are implicit.

### Shared Euclidean geometry

- `Point`: abbreviation for `ℂ`, with its real Euclidean structure.
- `ALine`: abbreviation for `AffineSubspace ℝ Point`; predicates below restrict arbitrary affine subspaces to genuine lines where needed.
- `IsLine`: existence of two distinct points whose affine span is the given subspace. This excludes empty, singleton, and whole-plane subspaces.
- `PresentedLine`: two distinct endpoint witnesses for a geometric line. Endpoint presentations are never used as the criterion for geometric uniqueness.
- `PresentedLine.carrier`: the Mathlib line `line[ℝ, p, q]` determined by those endpoints.
- `dot`: a wrapper for Mathlib's `inner ℝ`, not an independently assumed scalar product.
- `footThrough`: Mathlib's `EuclideanGeometry.orthogonalProjection` onto `line[ℝ, p, q]`; the line's `Nonempty` instance is proved using endpoint membership.
- `PresentedLine.foot`: the preceding projection applied to a presented line.
- `PresentedLine.reflect`: Mathlib's `EuclideanGeometry.reflection` in the carrier. No own reflection formula is used in the final file.
- `PerpendicularLines`: genuine lines with orthogonal nonzero direction vectors, using the real inner product. The condition is independent of the chosen endpoint witnesses.
- `intersection`: classical epsilon selection from the incidence predicate. Geometric uses are guarded by hypotheses guaranteeing a unique finite intersection; no external data or coordinate intersection formula is used.
- `omit4` and `omit3`: `Fin.succAbove` enumerations of the indices other than a selected index.
- `OnCircumcircle`: distance to the centre equals the radius of Mathlib's `Affine.Simplex.circumsphere`.
- `OnNinePointCircle`: the corresponding membership equation for Mathlib's `Affine.Simplex.ninePointCircle`.
- `triangleSide`: the full affine line through the two vertices other than the selected triangle vertex.

### Parabolas

- `Parabola`: a focus and a genuine directrix with the focus off the directrix. This is the usual nondegeneracy requirement, not an extra assumption on the original quadrilateral.
- `Parabola.locus`: equality of focus distance and `Metric.infDist` to the directrix.
- `Parabola.axis`: the line joining the focus to its perpendicular foot on the directrix.
- `Parabola.vertex`: the midpoint of that focus and foot. The theorems separately assert membership in the parabola and the unique minimizing property, so these substantive properties are not hidden in the definition.
- `Tangent`: a genuine line, not parallel to the axis, meeting the parabola in exactly one real point. Excluding axis-parallel lines is essential: they also have exactly one real intersection but are not tangent. This avoids introducing differentiability machinery while expressing ordinary parabola tangency.

### Complete quadrilateral

- `Quadrilateral`: four presented lines, pairwise nonparallel, with no concurrent triple. Distinctness follows from the nonparallel condition.
- `Quadrilateral.meet`: the selected intersection of a pair of lines.
- `Quadrilateral.triangleVertices`: the three pairwise intersections of the three lines remaining after omission of one line.
- `Quadrilateral.triangle`: the resulting Mathlib `Affine.Triangle ℝ ℂ`.
- `IsMiquelPoint`: incidence with all four circumcircles; the point is not selected by a formula.
- `IsOrthocentreLine`: a genuine line containing all four Mathlib `Affine.Triangle.orthocenter` points.
- `Quadrilateral.diagonalMidpoints`: midpoints of the three opposite-vertex pairs `(01,23)`, `(02,13)`, and `(03,12)`.
- `IsNewtonGaussLine`: a genuine line containing all three diagonal midpoints.
- `Inscribed`: tangency of the parabola to every quadrilateral line.
- `IsInscribedFocusDirectrix`: a geometric point/subspace pair realized as focus/directrix data of an inscribed parabola. This allows meaningful uniqueness without quotienting endpoint presentations.

### Complete quadrangle

- `Quadrangle`: four points with each omitted-point triple affine independent over `ℝ`. This is exactly the noncollinearity condition needed for the four triangle objects and excludes repeated points.
- `Quadrangle.triangle`: the Mathlib triangle on an omitted-point triple.
- `IsPonceletPoint`: incidence with all four Mathlib nine-point circles; again no formula selects the point.
- `OrthocentricSystem`: one of the points equals the Mathlib orthocentre of the opposite triangle.
- `RectangularConic`: a centre, unit vector `u`, and real parameter `k`.
- `RectangularConic.locus`: the equation `dot (z-center) u * dot (z-center) (I*u) = k`. The axes `u` and `I*u` are perpendicular, so `k ≠ 0` gives a rectangular hyperbola and `k = 0` gives its two perpendicular asymptote lines.
- `RectangularHyperbola`: a rectangular conic with `k ≠ 0`; this distinguishes proper hyperbolas from the possible degeneration.
- `OnFourPoints`: incidence of all four quadrangle points with a locus.
- `Quadrangle.oppositeJoins`: the three opposite-side pairs `AB/CD`, `AC/BD`, and `AD/BC`.
- `IsDegenerateRectangularCenter`: the specified point lies on both lines of one perpendicular opposite-join pair. This records the precise pointwise obstruction to demanding a proper hyperbola.
- `HasFiniteDiagonalTriangle`: each opposite-join pair is nonparallel. No projective points at infinity are present in `ℂ`.
- `Quadrangle.diagonalVertices`: the three opposite-join intersections.
- `Quadrangle.diagonalTriangle`: their Mathlib triangle, constructed using the admitted consequence that these vertices are noncollinear.
- `pedalFeet`: Mathlib perpendicular projections onto the three supporting lines.
- `IsPedalCircle`: a positive-radius centre/radius pair through all three feet. The centre is specified by incidence, not a custom circumcentre formula.

### Explicit construction obligations

Two supporting lemmas, both admitted and counted in the compiler summary, convert incidence hypotheses to the affine-independence evidence required by Mathlib triangle constructors:

1. `quadrilateral_triangle_independent`: the three pairwise intersections of three nonparallel, nonconcurrent lines are affine independent.
2. `diagonal_triangle_independent`: the three finite diagonal vertices of a no-three-collinear quadrangle are affine independent.

These are not extra assumptions on theorem callers. Their proofs remain obligations, just as the requested classical theorem proofs remain obligations.

## Every AMBIGUOUS mark — 7 total

1. **Tangency:** selected unique real intersection plus nonparallelism to the axis; differential tangency is the alternative.
2. **C4 uniqueness:** unique geometric focus/directrix data, not equality of arbitrary endpoint presentations.
3. **C6 sides:** full supporting lines, rather than requiring contact on closed side segments.
4. **C7 midpoint:** midpoint of the focus and its perpendicular foot, not an unspecified point of the directrix.
5. **D1 rectangular hyperbola:** `classical_D1_c` allows the degenerate perpendicular-line conic; `classical_D1_d` states the proper-hyperbola version separately.
6. **D1 orthocentric centre:** no distinguished common point exists when all nine-point circles coincide; the centre statement is interpreted for each point satisfying the common-point predicate.
7. **D5 exceptional symmetry:** predicate/set-valued symmetry is unconditional; single-valued symmetry is stated separately outside the orthocentric exception.

## Every EXTRA HYPOTHESIS mark — 6 total

1. **`classical_D1_b`:** nonorthocentricity for uniqueness. Otherwise the common-point set is an entire positive-radius circle by D2.
2. **`classical_D1_d`:** the specified common point is not the intersection of perpendicular opposite joins. A degenerate rectangular conic is a perpendicular line pair; no-three-collinear forces two original points onto each line. The pointwise condition is weaker than globally forbidding all perpendicular opposite joins and does not unnecessarily exclude all orthocentric systems.
3. **`classical_D3_a`:** the omitted point is off the opposite circumcircle, excluding the Simson-line degeneration. This condition was already flagged in the supplied classical statement and is explicit for the selected index only.
4. **`classical_D3_b`:** the same non-Simson hypothesis for the `Cospherical` restatement.
5. **`classical_D4`:** all three opposite-side intersections are finite, expressed by nonparallel opposite joins. No-three-collinear alone allows parallelograms, which do not have the required affine diagonal triangle. Noncollinearity of the finite diagonal vertices is derived as a construction obligation, not added as a further hypothesis.
6. **`classical_D5_b`:** nonorthocentricity for single-valued label independence, for the same reason as D1 uniqueness.

There are no extra general-position assumptions on Setting A beyond the brief's pairwise nonparallel and no-three-concurrent conditions. Setting B starts with exactly the no-three-collinear condition; all theorem-specific additions are marked above.

## Files read and blindness declaration

The only input file read was:

- `<ws>/AFM/PaperF/layer15/writer_brief.txt`.

Own output files read during editing, checking, or reporting:

- `<oc>/tmp/l15f/w/Classical.lean`.
- `<oc>/tmp/l15f/w/COMPILER_OUTPUT.txt`.
- `<oc>/tmp/l15f/w/Classical.jack-copy.lean` — a copied-back instance of my own remote output, read by `cmp` and hashing.
- `<oc>/tmp/l15f/w/CLASSICAL_REPORT.md` — this report, read back for the final response.
- `jack:~/reformal/PaperFClassical.lean` — my own submitted output, consumed by the allowed compiler and copied back for identity verification.

I also read the compiler output for my own submitted file on each compilation. I did not read any paper, other AFM/PaperF file, repository source, skill file, memory file, or other local or remote input. No web search, external mathematical reference, subagent, repository update, or cache download was used. Mathlib was loaded only by the prescribed compilation of my own source.
