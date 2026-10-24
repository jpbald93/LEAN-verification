# Paper A — Classical-source blind formalisation report

Output: `/tmp/blindA/Classical.lean` (byte-identical to `jack:~/reformal/PaperAClassical.lean`, md5 `303bc56026010b4b9387704c44df68f0`).

## Statements (namespace `PaperAClassical`)
| Name | Content |
|---|---|
| `classical_A1_a` | Desargues in `Projectivization K (Fin 3 → K)`: two triangles, A≠A′ etc., corresponding sides distinct, AA′,BB′,CC′ concurrent ⇒ P,Q,R (given by the property of lying on both side lines) collinear |
| `classical_A1_b` | Converse: same non-degeneracy, P,Q,R collinear ⇒ ∃ O on AA′, BB′, CC′ |
| `classical_A2_a` | Monge: three circles in `EuclideanSpace ℝ (Fin 2)`, distinct centres, pairwise unequal radii ⇒ E₁₂,E₂₃,E₁₃ collinear |
| `classical_A2_b` | Companion: E₁₂, I₂₃, I₁₃ collinear |
| `classical_A3_a` | Simson: P on `circumsphere` of `⟨![A,B,C],h⟩` ⇒ the three `orthogonalProjection`s onto `line[ℝ,B,C]` etc. are collinear |
| `classical_A3_b` | Converse: collinear feet ⇒ P on circumsphere |
| `classical_A4_a` | Outer Napoleon: apexes on the opposite side (`SOppSide`), centroids form a non-degenerate equilateral triangle |
| `classical_A4_b` | Inner Napoleon: apexes on the same side (`SSameSide`), centroids pairwise equidistant (degenerate allowed) |
| `classical_A5` | Lami: F₁+F₂+F₃=0, not all on one line through 0 ⇒ ‖F₁‖/sin α = ‖F₂‖/sin β = ‖F₃‖/sin γ (`InnerProductGeometry.angle`) |

## Obligations (well-formedness only)
- `classical_A1_obligation`: two distinct projective lines meet in exactly one point (P,Q,R well defined).
- `classical_A2_obligation_ext` / `_int`: existence & uniqueness of external / internal centre of similitude.
- `classical_A4_obligation`: on each side of a segment there is exactly one equilateral apex.
- `classical_A5_obligation`: the three sines are nonzero (divisions meaningful).

## OWN DEFINITIONS
- `PPlane K` (abbrev for `Projectivization K (Fin 3 → K)`), `pline p q` = `Projectivization.Subspace.span {p,q}`,
  `PCollinear` = `Projectivization.Dependent ![p,q,r]`, `PTriangle` = `Projectivization.Independent ![a,b,c]`.
- `IsExtSimCenter s t E`: homothety at E with ratio r_t/r_s maps circle s onto circle t (defining property from the text).
- `IsIntSimCenter s t I`: `Wbtw` O_s I O_t and r_t·|O_s I| = r_s·|I O_t|.
- `IsEquilateralApex U V X`: |UX| = |VX| = |UV|.
- Centres of the equilateral triangles: `Finset.univ.centroid ℝ ![…]` (Mathlib).

## AMBIGUOUS / EXTRA marks
- AMBIGUOUS (A1_a): some texts require O distinct from the six vertices; not imposed.
- EXTRA HYPOTHESIS (A2_a, A2_b): radii > 0, because Mathlib `Sphere` permits radius ≤ 0.
- AMBIGUOUS (A2_b): hr₂₃, hr₁₃ unnecessary for this form; kept per "same hypotheses".
- AMBIGUOUS (A4_a): "vertices of an equilateral triangle" read as non-degenerate (affine-independent conjunct included).
- AMBIGUOUS (A5): general real inner product space vs. fixing ℝ²; equivalent since forces span ≤ 2 dims.
- A4(b) conclusion is only pairwise-equal distances (text allows degeneration to a point).
- A3 is stated in the plane `EuclideanSpace ℝ (Fin 2)` (A3(b) is false in higher dimensions).

## Compiler summary
`lake env lean PaperAClassical.lean` on jack: 0 errors, 14 warnings, all `declaration uses 'sorry'`.

## Files read
- `/tmp/blindA/classical_statements.txt` (only mathematical input).
- My own files: `/tmp/blindA/scratch/check.lean` (a #check scratch, copied to jack as `PaperAScratch.lean` and compiled), `/tmp/blindA/Classical.lean`.
- `ls /tmp/blindA` showed `brief.txt`; it was NOT read. No other files, repositories or web resources were consulted.
