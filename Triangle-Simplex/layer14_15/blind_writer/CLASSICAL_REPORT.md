# CLASSICAL_REPORT — Paper TriSimplex (blind classical-source formalisation)

File: `/tmp/blindTriSimplex/Classical.lean` (identical to `jack:~/reformal/PaperTriSimplexClassical.lean`,
md5 checked). Namespace `ClassicalTriSimplex`. Ambient: `V` real inner product space, `P` metric affine
torsor over `V` (Euclidean affine space), unless stated otherwise.

## Statement list (25 theorems, all `:= by sorry`)
| Name | Content |
|---|---|
| classical_TriSimplex1_a | Carnot: signed d_a+d_b+d_c = R + r (`Affine.Simplex.circumcenter/circumradius/inradius`) |
| classical_TriSimplex1_b_signed | d_a = R cos A, d_b = R cos B, d_c = R cos C (signed) |
| classical_TriSimplex1_b | cos A + cos B + cos C = 1 + r/R |
| classical_TriSimplex1_b_acute | acute ⇒ unsigned `Metric.infDist`s sum to R + r |
| classical_TriSimplex1_b_acute_inside | acute ⇒ O ∈ `t.interior` |
| classical_TriSimplex2_a | De Gua, trirectangular tetrahedron OABC in ℝ³ |
| classical_TriSimplex2_a_coord | coordinate form: Area(ABC)² = (ab/2)²+(bc/2)²+(ca/2)² |
| classical_TriSimplex2_b | n-simplex form (n ≥ 2), orthogonal edges at vertex 0 |
| classical_TriSimplex2_b_coord | n-simplex coordinate form O=0, a_i e_i |
| classical_TriSimplex3_a | Viviani, P in open interior, sum = (√3/2)s |
| classical_TriSimplex3_b_closed | Viviani on closed triangle (boundary included) |
| classical_TriSimplex3_b | Viviani with signed distances, any point of the plane |
| classical_TriSimplex4_a | Japanese theorem, convex cyclic n-gon, any two triangulations |
| classical_TriSimplex4_b | r(ABC)+r(ACD) = r(ABD)+r(BCD) for convex cyclic ABCD |
| classical_TriSimplex4_b_rectangle | incentres of ABC,BCD,CDA,DAB form a rectangle |
| classical_TriSimplex5_a | Euler: OI² = R(R − 2r) |
| classical_TriSimplex5_b | 2r ≤ R, equality ↔ `Affine.Simplex.Equilateral` |
| classical_TriSimplex6_a | porism: one interscribed triangle ⇒ every X ∈ Γ is a vertex of one |
| classical_TriSimplex6_a_construction | tangent construction from X closes (YZ tangent, γ = incircle of XYZ) |
| classical_TriSimplex6_b | interscribed triangle exists ↔ d² = R² − 2Rr |
| classical_TriSimplex6_b_converse | d² ≠ R² − 2Rr ⇒ no X ∈ Γ is a vertex of one |
| classical_TriSimplex6_b_noclose | d² ≠ R² − 2Rr ⇒ construction never closes (YZ not tangent) |
| + 3 obligations | see below |

## Invented definitions (OWN DEFINITION)
- `signedDistLine l ref p`: `−infDist p l` if `l.SOppSide p ref`, else `+infDist p l`.
- `triInradius a b c`, `triIncenter a b c`: Mathlib `inradius`/`incenter` of `⟨![a,b,c], h⟩`, junk value if degenerate (ensured non-degenerate by the obligations).
- `IsRectangle`: diagonals share midpoint and have equal length, consecutive vertices distinct.
- `hullVol p s`: Lebesgue (`volume`) measure, inside the inner-product subspace `vectorSpan ℝ s`, of the convex hull of `s` translated by base point `p ∈ s` (intrinsic (dim)-volume).
- `IsConvexPolygon v`: n ≥ 3, injective, every other vertex strictly on the same side of every edge line.
- `IsTriangulation v T`: index triples i<j<k, triangles cover the hull, interiors pairwise disjoint.
- `IsConvexQuad A B C D`: diagonals AC and BD cross strictly inside both.
- `Interscribed Γ γ t`: vertices on Γ and `t.insphere = γ`.

## AMBIGUOUS / EXTRA HYPOTHESIS marks
- 1a: interior side of BC represented by the opposite vertex A (equivalent).
- 3a/3b_closed: no planarity hypothesis (not needed). 3b: EXTRA HYPOTHESIS `finrank V = 2` ("point of the plane").
- 4a: EXTRA HYPOTHESIS `finrank V = 2`; polygon lives in `V` (convex hull needs vector structure); triangulation defined via cover + disjoint interiors rather than literally "non-crossing diagonals" (equivalent for convex polygons).
- 4b: `Cospherical` with no planarity (convex quad is planar, so concyclic).
- 6: EXTRA HYPOTHESIS `finrank V = 2`; "γ inside Γ" = `0 < r ∧ d < R − r`; AMBIGUOUS: "circumscribed" taken as γ = incircle (not merely tangent side lines, which would admit excircles).
- 2: De Gua statements are in `EuclideanSpace ℝ (Fin n)` with `hullVol`; 2a requires `AffineIndependent` (tetrahedron) — implied by orthogonality only if edges nonzero.

## Obligations (well-formedness)
- `classical_TriSimplex4_a_obligation`: every triangle of a triangulation of a convex polygon is affinely independent.
- `classical_TriSimplex4_b_obligation`: ABC, ACD, ABD, BCD affinely independent.
- `classical_TriSimplex6_a_obligation`: from X ∈ Γ there are exactly two tangent lines to γ meeting Γ again at distinct Y, Z ≠ X.

## Compiler summary
`lake env lean PaperTriSimplexClassical.lean` on jack: **0 errors, 25 warnings, all `declaration uses 'sorry'`**.

## Files read
- `/tmp/blindTriSimplex/classical_statements.txt` (only mathematical input).
- Directory listing of `/tmp/blindTriSimplex` (saw `brief.txt`, not opened).
- Own scratch file `/tmp/blindTriSimplex/scratch/S.lean` (written by me; #check/#print queries compiled on jack as `ScratchTS.lean`, since deleted).
- Own output `Classical.lean`. No other files, repositories, or web resources were read.
