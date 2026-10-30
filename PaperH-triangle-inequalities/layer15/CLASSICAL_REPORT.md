# Paper H — Classical-source blind formalisation report

File: `./Classical.lean` (identical copy at `arm64-machine:~/lean/reformalH/PaperHClassical.lean`).
Namespace `PaperHClassical`. Conventions: `t : Affine.Triangle ℝ P` in any real Euclidean affine
space `P` (any dimension, unless marked as plane); `A,B,C = t.points 0,1,2`; `a=BC`, `b=CA`, `c=AB`.

## Statement list

| Name | Item | Gloss |
|---|---|---|
| classical_E1 | E1 | OI² = R² − 2Rr (Mathlib circumcenter/incenter/circumradius/inradius) |
| classical_E2a | E2 | 2r ≤ R |
| classical_E2b | E2 | R = 2r ↔ equilateral |
| classical_E3 | E3 | ∀ i, OI_i² = R² + 2R r_i, with `t.excenter {i}`, `t.exradius {i}` |
| classical_E4a | E4 | OG² = R² − (a²+b²+c²)/9 |
| classical_E4b | E4 | OH² = 9R² − (a²+b²+c²) (Mathlib orthocenter) |
| classical_E4c | E4 | IG² = (s² + 5r² − 16Rr)/9 |
| classical_E5 | E5 | Blundon's fundamental quartic ≤ 0 |
| classical_E6a | E6 | 16Rr − 5r² ≤ s² |
| classical_E6b | E6 | s² ≤ 4R² + 4Rr + 3r² |
| classical_E7 | E7 | Kooi: s² ≤ R(4R+r)²/(2(2R−r)) |
| classical_E8a / E8b | E8 | Weitzenböck inequality / equality ↔ equilateral |
| classical_E9a / E9b | E9 | Hadwiger–Finsler inequality / equality ↔ equilateral |
| classical_E10a / E10b | E10 | (a+b+c)² ≥ 12√3Δ / equality ↔ equilateral |
| classical_E11a | E11 | Leibniz identity ΣXA² = 3XG² + Σa²/3 |
| classical_E11b | E11 | G minimises ΣXA², and is the unique minimiser |
| classical_E12a | E12 | Neuberg–Pedoe inequality (two triangles, possibly in different spaces) |
| classical_E12b | E12 | equality ↔ ∃ k>0, (a′,b′,c′) = k(a,b,c) |
| classical_P1 | P1 | Ptolemy inequality for any four points |
| classical_P2 | P2 | for distinct points: equality ↔ in order on a circle or line |
| classical_M1a | M1 | Erdős–Mordell for X inside or on the triangle |
| classical_M1b | M1 | equality ↔ equilateral ∧ X = centroid |
| classical_M2 | M2 | Barrow, bisector feet U,V,W on the sides |
| classical_F1a | F1 | angles < 120° ⇒ ∃ F with 120° views minimising ΣXA |
| classical_F1b | F1 | every such 120° point F minimises ΣXA (stronger reading) |
| classical_F2a | F2 | (plane) AA′ = BB′ = CC′ |
| classical_F2b | F2 | (plane) lines AA′, BB′, CC′ concurrent |
| classical_F2c | F2 | (plane, angles < 120°) Fermat point F lies on all three lines, AA′ = FA+FB+FC |
| classical_F2d | F2 | (plane) pairwise angles between the lines are 60° (vector angle 60° or 120°) |
| classical_F3 | F3 | (plane) Napoleon: centres equilateral, centre = centroid of ABC |

33 theorems in total.

## Definitions I wrote (Mathlib lacks a direct form)

- `ClassicalSideA/B/C`: a = dist B C, b = dist C A, c = dist A B, straight from the textbook.
- `ClassicalSemiperimeter`: (a+b+c)/2.
- `ClassicalAreaPts`, `ClassicalArea`: Δ = ½·AB·AC·sin∠BAC (the standard SAS area formula, using
  `EuclideanGeometry.angle`). Works in any dimension.
- `ClassicalCentroid`: `Finset.univ.centroid ℝ t.points` (just a shorthand for Mathlib's notion).
- `ClassicalEquilateral`: a = b ∧ b = c.
- `ClassicalSumSq`: a² + b² + c².
- `ClassicalInsideOrOn`: X is an affine combination of A,B,C with nonnegative weights (= closed
  convex hull). I used barycentric weights because `convexHull` needs a vector space, not a torsor.
- `ClassicalStrictlyInside`: all barycentric weights strictly positive (relative interior), for M2.
- `ClassicalDistToLine X Y Z`: `Metric.infDist X (affineSpan ℝ {Y,Z})`, the distance to the side line.
- `ClassicalIsFermatPoint`: ∠BFC = ∠CFA = ∠AFB = 2π/3.
- `ClassicalAnglesLt120`: all three angles of the triangle < 2π/3.
- `ClassicalOutwardEquilateralApex X Y Z X'`: X′Y = X′Z = YZ, and X′ strictly on the opposite side of
  line YZ from X (`SOppSide`). This is what "erected outward" means.
- `ClassicalDistSum`, `ClassicalDistSqSum`: XA+XB+XC and XA²+XB²+XC².
- `ClassicalInOrderOnCircleOrLine A B C D`: either (`Concyclic {A,B,C,D}` and the closed segments AC
  and BD meet, written with `Wbtw`: the quadrilateral ABCD is convex in that order), or
  (`Collinear` and exactly one of B, D lies strictly between A and C: {A,C} separates {B,D}).
- In F3 the centre of equilateral triangle BCA′ is its centroid (centroid = circumcentre for an
  equilateral triangle).

## AMBIGUOUS / EXTRA HYPOTHESIS marks

- **AMBIGUOUS (E12):** the two triangles may live in different Euclidean spaces P, P′. This is the
  most general reading, and the claim depends only on side lengths.
- **AMBIGUOUS (P2):** "in this order" is read cyclically: {A,C} separates {B,D}. On a line, the
  literal reading A–B–C–D would make the "only if" direction false: the order B,C,D,A also gives
  equality.
- **AMBIGUOUS (F1):** two readings. F1a is existence plus minimality. F1b says every 120° point is a
  minimiser.
- **AMBIGUOUS (F2d):** the angle between unoriented lines is taken as the vector angle of the
  direction vectors AA′, BB′, CC′ being 60° or 120°.
- **No EXTRA HYPOTHESIS marks.** Unmarked modelling choices:
  - F2/F3 live in a `section` with `[Fact (Module.finrank ℝ V = 2)]`, because the textbook says
    "in the plane".
  - P2's distinctness hypotheses come from the statement itself.
  - E7 divides by 2(2R − r). This is positive by E2, so no hypothesis is needed.
  - E3 assumes Mathlib's `excenter {i}` / `exradius {i}` is the excentre/exradius opposite vertex
    i. I could not read the Mathlib source to confirm this.
  - In M2, "internal bisector of ∠BXC meets BC at U" is encoded as U ∈ segment BC (`Wbtw`) with
    ∠BXU = ∠UXC.

## Compiler summary

`lake env lean PaperHClassical.lean` on the arm64 machine finished with exit code 0. The output
contains exactly **33 `declaration uses 'sorry'` warnings, 0 errors and no other messages**. Before
that I ran one `#check` probe file to confirm the Mathlib names, and one earlier version failed:
`convexHull`/`segment` on a torsor needed `AddCommMonoid P`. I fixed it with barycentric/`Wbtw`
formulations.

## Files read

Only my own output files: `./Classical.lean` (written and edited by me, also copied as
`PaperHClassical.lean` and compiled), and the compiler output `./out.txt`, which I captured myself.
I read no other files, made no web searches and opened no other repositories.
