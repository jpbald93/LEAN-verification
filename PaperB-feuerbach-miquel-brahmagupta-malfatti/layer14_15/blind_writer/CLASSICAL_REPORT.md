# Paper B — Classical-source blind formalisation report

Output: `/tmp/blindB/Classical.lean` (copied verbatim to `jack:reformal/PaperBClassical.lean`).
Ambient space: Euclidean plane `E2 := EuclideanSpace ℝ (Fin 2)`; triangles are `tri A B C h := ⟨![A,B,C], h⟩ : Affine.Triangle ℝ E2`, where `h : AffineIndependent ℝ ![A,B,C]` (non-degenerate).

## Statement list
| Name | Content |
|---|---|
| `classical_B1_a` | `insphere.IsIntTangent ninePointCircle` (incircle internally tangent, lying inside) |
| `classical_B1_a_dist` | `dist N I = R/2 - r` (`ninePointCircle.center`, `incenter`, `circumradius`, `inradius`) |
| `classical_B1_b_obligation` | `ExcenterExists {i}` for each `i : Fin 3` |
| `classical_B1_b` | `ninePointCircle.IsExtTangent (exsphere {i})` for each `i` |
| `classical_B1_b_dist` | `dist N (excenter {i}) = R/2 + exradius {i}` |
| `classical_B1_remark_equilateral` | equilateral ⇒ `ninePointCircle = insphere` |
| `classical_B1_remark_unique` | not equilateral ⇒ `∃!` internal-tangency point (Feuerbach point) |
| `classical_B2_a` | Miquel, D,E,F on open sides (`Sbtw`): ∃ M with `Cospherical {A,E,F,M}`, `{B,F,D,M}`, `{C,D,E,M}` |
| `classical_B2_b` | Miquel, D,E,F on side lines, distinct from vertices |
| `classical_B2_obligation` | under B2_b's hypotheses each triple AEF, BFD, CDE is non-collinear |
| `classical_B3_obligation` | volume of convex hull of 4 points is finite |
| `classical_B3_a` | convex cyclic ⇒ `K = √((s-a)(s-b)(s-c)(s-d))` |
| `classical_B3_b` | convex cyclic ⇒ `16K² = (-a+b+c+d)(a-b+c+d)(a+b-c+d)(a+b+c-d)` |
| `classical_B3_remark_bretschneider` | convex ⇒ `K² = Π(s-x) - abcd·cos²((∠DAB+∠BCD)/2)` |
| `classical_B3_remark_cyclic_iff` | convex ⇒ (cyclic ↔ `∠DAB + ∠BCD = π`) |
| `classical_B4_a` | existence of a Malfatti triple |
| `classical_B4_a_unique` | uniqueness of the Malfatti triple |
| `classical_B4_b_obligation` | `0 < s-a, s-b, s-c` |
| `classical_B4_b` | Malfatti radius formulas (with `r = inradius`, `I = incenter`, `d,e,f = IA,IB,IC`) |

Mathlib conventions used: `IsIntTangent s₁ s₂` = `s₁` inside `s₂` (fields: common point `p`, `Wbtw s₂.center s₁.center p`); `IsExtTangent` = `Wbtw s₁.center p s₂.center`; `exsphere {i}` = excircle opposite vertex `i` (0,1,2 ↔ A,B,C); `insphere = exsphere ∅`.

## Invented definitions (OWN DEFINITION)
- `IsConvexQuad A B C D` : ∃ X, `Sbtw ℝ A X C ∧ Sbtw ℝ B X D` (diagonals cross in their interiors).
- `quadArea A B C D` : `(volume (convexHull ℝ {A,B,C,D})).toReal`.
- `IsMalfattiTriple A B C cA cB cC` : positive radii; closed discs ⊆ `convexHull ℝ {A,B,C}`; pairwise `IsExtTangent`; `cA` tangent (`Sphere.IsTangent`) to `line[A,B]`, `line[A,C]`; `cB` to `line[B,A]`, `line[B,C]`; `cC` to `line[C,A]`, `line[C,B]`.

## AMBIGUOUS / EXTRA marks
- B2: "on the sides" — AMBIGUOUS between open segments (`classical_B2_a`), closed segments, side lines (`classical_B2_b`, both formalised). "M on circle XYZ" is written as `Cospherical {X,Y,Z,M}`, which is correct in the plane once XYZ is non-collinear (`classical_B2_obligation`).
- B4: "inside the triangle" — AMBIGUOUS: closed disc ⊆ closed triangle (chosen) vs. open interior; tangency to "sides" read as tangency to side lines (with the disc inside the triangle the contact point is automatically on the segment).
- General (not marked in-file as EXTRA): everything is stated in the plane `E2` rather than an arbitrary Euclidean affine space. That's the classical setting, and it's needed to make `volume`/area and the 4-point `Cospherical` reading of "circle" meaningful.
- No EXTRA HYPOTHESIS was needed: the theorems assume only non-degeneracy, plus convexity and cyclicity for B3.

## Obligations
`classical_B1_b_obligation`, `classical_B2_obligation`, `classical_B3_obligation`, `classical_B4_b_obligation`, all `:= by sorry`.

## Compiler summary
`lake env lean PaperBClassical.lean` on jack: 19 warnings, all `declaration uses 'sorry'`, and no errors.

## Files read
- `/tmp/blindB/classical_statements.txt` (the only mathematical input)
- `ls /tmp/blindB` (directory listing only; `brief.txt` was not opened)
- My own scratch file `/tmp/blindB/scratch/S.lean`, uploaded as `~/reformal/PaperBScratch.lean` for `#check`/`#print` of Mathlib names (output from the compiler only)
- No other files, repositories, notes, or web sources.
