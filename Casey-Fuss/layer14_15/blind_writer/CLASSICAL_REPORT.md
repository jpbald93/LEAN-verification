# CLASSICAL_REPORT — Paper CaseyFuss (blind classical-source writer)

File: `/tmp/blindCaseyFuss/Classical.lean` (identical to `jack:~/reformal/PaperCaseyFussClassical.lean`).
Setting: Euclidean plane `Pl := EuclideanSpace ℝ (Fin 2)`; circles are `EuclideanGeometry.Sphere Pl`.

## Statements
| Name | Content |
|---|---|
| `classical_CaseyFuss1_a` | Casey: 4 pairwise-disjoint circles internally tangent to Γ at K_i in cyclic order ⇒ t12·t34 + t14·t23 = t13·t24 (direct tangents) |
| `classical_CaseyFuss1_a_obligation` | direct-tangent radicands ≥ 0 |
| `classical_CaseyFuss1_b` | signed-radius form: t_ij = |K_iK_j|·√((R-ρ_i)(R-ρ_j))/R for all i,j, and the Casey relation |
| `classical_CaseyFuss1_b_obligation` | radicands (ρ_i-ρ_j)² ≤ |O_iO_j|² and (R-ρ_i)(R-ρ_j) ≥ 0 |
| `classical_CaseyFuss1_c` | converse: signs ε_i ∈ {±1} (signed radii ε_i r_i), signs s₁,s₂ with t01 t23 + s₁ t02 t13 + s₂ t03 t12 = 0 ⇒ all four tangent to a circle (r>0) or to a line |
| `classical_CaseyFuss2_a` | Fuss: bicentric ⇒ 1/(R-x)²+1/(R+x)²=1/r², (R²-x²)²=2r²(R²+x²), x²=R²+r²-r√(4R²+r²), √2 r ≤ R, (R=√2 r ↔ x=0), (x=0 ↔ square) |
| `classical_CaseyFuss2_b` | converse: ω strictly inside Γ + Fuss relation ⇒ ∃ bicentric quadrilateral |
| `classical_CaseyFuss3_a` | Poncelet: one bicentric quad ⇒ one through every P ∈ Γ; the tangent-chord path (no immediate backtracking) closes after exactly 4 steps (p4 = p0, p3 ≠ p0) and is bicentric; set of bicentric quads infinite |
| `classical_CaseyFuss3_b` | existence ↔ Fuss relation; then one through every point of Γ |

## Invented definitions (OWN DEFINITION)
- `InternallyTangentAt C Γ K`: circle C ⊆ closed disc of Γ and C ∩ Γ = {K}.
- `ExternallyTangentAt C Γ K`: closed disc of C disjoint from open disc of Γ and C ∩ Γ = {K}.
- `CirclesTangent`, `LineTangent`: exactly one common point.
- `CyclicOrder4 K`: K injective and chords K0K2, K1K3 intersect (this means cyclic order for concyclic points).
- `directTangent`, `signedTangent`: the √-formulas from the notation (`Real.sqrt`, so negative radicand ↦ 0).
- `ConvexQuad`: diagonals cross strictly inside each other (`Sbtw`) and no three vertices collinear.
- `TangentToSide ω P Q`: some point of segment PQ lies on ω and the whole line PQ is at distance ≥ r from the centre.
- `IsIncircleQuad`, `BicentricWith Γ ω A B C D` (convex, vertices on Γ, ω touches all four sides), `StrictlyInside ω Γ` (r>0, d + r < R).

## AMBIGUOUS / EXTRA marks
- 1(a) AMBIGUOUS: "no two intersecting" read as disjoint circles (curves); the alternatives are disjoint closed or open discs. EXTRA HYPOTHESIS: R > 0.
- 1(c) EXTRA HYPOTHESIS: the chosen tangents exist (radicands ≥ 0). AMBIGUOUS: the fifth circle has positive radius; tangency means one common point; internal/external tangency types are not tied to ε. The "consistent choice" is encoded by sign vectors ε, which give exactly the three listed patterns up to a global sign.
- 2(a) AMBIGUOUS: "the square" is formalised as four equal sides plus equal diagonals.
- 1(b): R > 0 is part of the statement. For point-circles either sign convention gives ρ = 0.
- 3(a) modelling choice: the tangent construction is a sequence on Γ with consecutive points distinct, each chord line tangent to ω, and p(n+2) ≠ p(n).

## Obligations
`classical_CaseyFuss1_a_obligation` and `classical_CaseyFuss1_b_obligation`, for the radicands under √. They are stated separately and are not hypotheses of the main theorems.

## Compiler summary
`lake env lean PaperCaseyFussClassical.lean` on jack: 0 errors. There are 9 warnings, all `declaration uses 'sorry'`, one per theorem. The local file and jack copy are confirmed identical with diff.

## Files read
- `/tmp/blindCaseyFuss/classical_statements.txt` (only mathematical input)
- `ls` of `/tmp/blindCaseyFuss` (only to see file names; brief.txt was not opened)
- My own `/tmp/blindCaseyFuss/Classical.lean` (and the jack copy, for the diff check)
No other files, repositories, or web sources were used.
