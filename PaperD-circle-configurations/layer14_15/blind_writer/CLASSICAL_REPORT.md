# Paper D — Classical-source blind formalisation report

Ambient: `Pt := EuclideanSpace ℝ (Fin 2)`, namespace `PaperDClassical`. Triangles are `⟨![a,b,c], h⟩ : Affine.Triangle ℝ Pt`.
Constructed points are passed in as data with their defining property. Their existence is a separate `_obligation`.

## Statements
| Name | Item | Gloss |
|---|---|---|
| classical_D1_a | D1(a) | Four circles through M in general position (`CliffordGP 4`): ∃ X lying on all four Γ_ijk |
| classical_D1_b | D1(b) | Five circles: the five Clifford points X l (the ones from omitting circle l) are cospherical |
| classical_D1_c | D1(c) | Six circles: the six circles C m (from (b), omitting m) have a common point |
| classical_D1_d_even | D1(d) | Chain, any even n ≥ 4: the n level-(n−1) circles share a point |
| classical_D1_d_odd | D1(d) | Chain, any odd n ≥ 3: the n level-(n−1) points are cospherical |
| classical_D2 | D2 | Pentagram: the five second intersections Q i of consecutive outer circumcircles are cospherical |
| classical_D2_obligation | D2 | The vertices V, T exist and every outer triangle is non-degenerate |
| classical_D3 | D3 | Scalene triangle: F₁, F₂, circumcentre and nine-point centre (`ninePointCircle.center`) are cospherical |
| classical_D3_obligation | D3 | Both Fermat points exist |
| classical_D4 | D4 | Sawayama–Thébault: the centres of ω₁, ω₂ and `incenter` are collinear |
| classical_D4_obligation | D4 | The two Thébault circles exist |
| classical_D5 | D5 | Kosnita: lines A O_a, B O_b, C O_c are concurrent (or all parallel) |
| classical_D5_obligation | D5 | O_a exists when O is not on BC |
| classical_D6_lower / _upper | D6 | Blundon, both bounds (`circumradius`, `inradius`, s = half the perimeter) |
| classical_D6_obligation | D6 | R² − 2Rr ≥ 0, so the square root is genuine |
| classical_D7 | D7 | Steiner–Lehmus: equal bisectors from B and C give AB = AC |
| classical_D7_obligation | D7 | The bisector foot exists |

D1(d) is stated for **all n** (not capped at n ≤ 7). The levels are indexed by subsets S ⊆ Fin n through the structure `CliffordChain`, rather than by recursive functions: odd |S| gives a circle `circ S` and even |S| gives a point `pt S`. Every level below n is a hypothesis, determined uniquely by general position. The theorem asserts the step at the top level n. The theorem holds for every n, so this amounts to an inductive statement of the chain.

## Mathlib notions used
`Affine.Simplex.circumcenter`, `circumsphere`, `circumradius`, `ninePointCircle`, `incenter`, `inradius` (all three of the last were confirmed present with `#check`), `Sphere`, `Cospherical`, `Collinear`, `Sbtw`, `Wbtw`, `line[ℝ,p,q]`, `AffineSubspace.SOppSide`/`SSameSide`/`Parallel`, `Metric.infDist`, `EuclideanGeometry.angle`, `Module.finrank`.

## Own definitions (with justification)
- `CliffordGP n c M P`: the "general position" of D1, taken literally from the brief. It requires positive radii, every circle through M, pairwise distinct circles, P i j a second common point that is ≠ M, and the three P's of any triple non-collinear. P i j is then unique, because two distinct circles meet in at most 2 points.
- `OnAllGamma P S X`: X lies on Γ_ijk for every triple in S. This is written as `Cospherical {P i j, P i k, P j k, X}`. Since the three P's are non-collinear, that is equivalent to X lying on their unique circumcircle, so no circumcircle data is needed.
- `CliffordChain n c M pt circ`: the recursive levels of Clifford's chain, as described above.
- `IsOuterApex`/`IsInnerApex`: the apex of an equilateral triangle on side qr, on the side of line qr opposite to p (outer) or the same side as p (inner).
- `IsFirstFermatPoint`/`IsSecondFermatPoint`: the defining concurrency of vertex–apex lines, as in the brief.
- `TangentToLine ω p q`: radius > 0 and the distance from the centre to line pq equals the radius.
- `InternallyTangent ω Ω`: 0 < r_ω < r_Ω and dist of centres = r_Ω − r_ω.
- `IsCircumcenterOf o p q r`: o is equidistant from p, q, r.
- `IsBisectorFoot v p q e`: `Wbtw ℝ p e q` and ∠p v e = ∠e v q. In D7 the bisector length is `dist b e`, i.e. measured from the vertex to the opposite side.

## AMBIGUOUS / EXTRA HYPOTHESIS marks
- D1_b `hXu`, D1_c `hXu` (EXTRA): the Clifford point of each four circles is unique, which is part of "general position". Without it, "the point given by (a)" is not well defined.
- D1_b `hnc`, D1_d_odd `hnc`, D2 `hnc` (EXTRA + AMBIGUOUS): the points are not collinear, so the result is "one circle". The alternative is to conclude `Cospherical ∨ Collinear` ("circle or line").
- D1_c `hCnc` (EXTRA): the five points on C m are not collinear, which is what makes C m unique.
- D1_d: the general-position conditions `odd_gp` and `even_gp` for lower levels are built into `CliffordChain`. This is the same extra hypothesis as above, made uniform.
- D2 (AMBIGUOUS): only the cyclic labelling of the lines is required, not convexity of the inner pentagon or a genuine "star" shape. Q i ≠ V i is required, which excludes tangent consecutive circles.
- D3: "scalene" is three pairwise-distinct side lengths, used as stated in the brief. (Strictly, only "not equilateral" is needed for F₂ to exist; Lester needs scalene.)
- D4 `hd` (AMBIGUOUS): "on side BC" is taken as `Sbtw` (strictly inside). `Wbtw` would allow D = B or D = C, where one of the circles degenerates.
- D4 (EXTRA/AMBIGUOUS): both circle centres are on A's side of BC. Otherwise the small circles in the segment beyond BC would also qualify. "One on each side of AD" is written as `SOppSide` of the two centres with respect to line AD.
- D5 (EXTRA): a ≠ O_a, b ≠ O_b, c ≠ O_c, so that the lines are defined.
- D5 (AMBIGUOUS): the conclusion is "concurrent ∨ all parallel" (concurrency at infinity, which occurs when the nine-point centre lies on the circumcircle). The strict alternative is to exclude the parallel case and keep only the first disjunct.
- D5: for a right triangle, O lies on a side, so the corresponding O_x does not exist and the statement is vacuous. This is noted in the docstring.

## Obligations (well-formedness only)
D2_obligation, D3_obligation, D4_obligation, D5_obligation, D6_obligation (radicand ≥ 0, Euler's inequality), D7_obligation. D1 needs no separate obligation: the general-position hypotheses are the data, and the existence of the Clifford points/circles at each level is exactly the theorem at the previous level.

## Compiler summary
`lake env lean PaperDClassical.lean` on jack: **18 `declaration uses 'sorry'` warnings, 0 errors, no other messages.** The local file /tmp/blindD/Classical.lean and ~/reformal/PaperDClassical.lean have the same md5 (c40aaff420be59fbe6d7d9f67d7ba7d8).

## Files read
- /tmp/blindD/brief.txt was not opened as a file; its content was given in the prompt.
- Only my own files: /tmp/blindD/Classical.lean, /tmp/blindD/scratch/Check.lean (a #check probe, also compiled on jack as ~/reformal/PaperDCheck.lean), and /tmp/blindD/scratch/out.txt (compiler output).
- No other files were read on either machine, and no web search was done.
