# CLASSICAL_REPORT — Paper Conics (blind classical-source writer)

File: `/tmp/blindConics/Classical.lean` (identical to `jack:reformal/PaperConicsClassical.lean`, md5 `4361ec20be93f6500a60b8669176a13b`).
Namespace `PaperConicsClassical`. Every theorem is `:= by sorry`.

## Statements
| Name | Content |
|---|---|
| `classical_Conics1_a` | β > α: there are exactly two Dandelin spheres, distinct; their centres are inside the same nappe; they are on strictly opposite sides of P (`SOppSide`) |
| `classical_Conics1_b` | For the two Dandelin spheres (contact circles C₁, C₂, contact points F₁, F₂): ∃ k, for all X ∈ P∩K, XF₁+XF₂ = k; k is the length of the generator segment between C₁ and C₂ for every generator; k is the greatest distance between two points of E (major axis) |
| `classical_Conics2_a` | β < α: exactly two Dandelin spheres, one centre inside each nappe |
| `classical_Conics2_b` | \|XF₁−XF₂\| = k on P∩K; k = generator segment between C₁ and C₂; k = least distance between points of the two branches (transverse axis) |
| `classical_Conics3_obligation` | well-formedness: if β < π/2 then P ⊓ affineSpan C is a line |
| `classical_Conics3_a` | XF = (cos β / cos α)·infDist(X, P ⊓ affineSpan C) for every X ∈ P∩K |
| `classical_Conics3_parabola_unique` | β = α ⇒ there is exactly one Dandelin sphere (the parenthetical claim) |
| `classical_Conics3_b` | e<1 when β>α; e=1 and P∩K = {X ∈ P : XF = dist(X,d)} when β=α; e>1 when β<α |
| `classical_Conics3_c` | planar converse: {X : XF = e·dist(X,d)} is an ellipse / parabola / hyperbola, with focus F and directrix d (for e<1 / e=1 / e>1) |
| `classical_Conics4_a` | ∃! Steiner inellipse |
| `classical_Conics4_b` | it is centrally symmetric about (a+b+c)/3; area = π/(3√3)·area(abc); every other inscribed ellipse has strictly smaller area |
| `classical_Conics5` | roots of p′ (as a multiset) = {f₁, f₂}; f₁+f₂ = 2(a+b+c)/3; f₁f₂ = (ab+bc+ca)/3 |
| `classical_Conics5_double_root` | if p′ has a double root z, the inellipse is a circle centred at z; p′ has a double root ⇔ the triangle is equilateral |

The "General Siebeck form" is marked "not required" in the source, so I did not formalise it.

## Mathlib notions used
`EuclideanSpace ℝ (Fin 3/2)`, `InnerProductGeometry.angle`, `Submodule.starProjection`, `AffineSubspace` (`line[ℝ,_,_]`, `affineSpan`, `⊓`, `direction`, `SOppSide`), `Module.finrank`, `EuclideanGeometry.Sphere`, `Metric.sphere`, `Metric.infDist`, `dist`, `midpoint ℝ`, `Collinear ℝ`, `convexHull ℝ`, `MeasureTheory.volume` (on ℂ), `AffineIsometryEquiv` (`E2 ≃ᵃⁱ[ℝ] E2`), `Polynomial.derivative`, `Polynomial.roots`, `IsGreatest`/`IsLeast`.

## Definitions I made up (OWN DEFINITION)
- `cone V u α`: the apex V together with every X for which ∠(X−V, u) is α or π−α. This is the union of the lines through V at angle α to the axis.
- `IsGenerator V u α g`: g = line through V and V+w, where w ≠ 0 and ∠(w,u) = α.
- `InsideNappe V u α σ X`: X ≠ V and ∠(X−V, σu) < α (σ = ±1).
- `planeAxisAngle u P`: ∠(u, projection of u onto P.direction), which lies in [0, π/2]. It is π/2 when u ⊥ P, because Mathlib sets angle u 0 = π/2.
- `TangentToConeAlong V u α S C`: radius > 0; every generator meets S in exactly one point; C = S ∩ K.
- `TangentToPlaneAt P S F`: P ∩ S = {F}.
- `IsDandelinSphere`: tangent to the cone along some C, and tangent to P at some F.
- `IsEllipseFD`, `IsHyperbolaFD`, `IsParabolaFD` (in E2): after some affine isometry the curve is in standard form (x²/a²+y²/b²=1 with a>b>0 / x²/a²−y²/b²=1 / y²=4px). The focus is (c,0) and the directrix is x=a²/c (for the parabola: (p,0) and x=−p).
- `IsEllipseWithFoci E f₁ f₂` (in ℂ): E = {z : |z−f₁|+|z−f₂| = r} with |f₁−f₂| < r. Circles are included.
- `IsEllipse`: an ellipse with some pair of foci.
- `IsInscribedEllipse a b c E`: E is an ellipse, E ⊆ convexHull{a,b,c}, and E meets each side line in exactly one point. For a strictly convex curve this is the same as tangency.
- `IsSteinerInellipse`: E is an ellipse in the closed triangle, and E ∩ each side line = {midpoint of that side}.

How objects are characterised by property:
- **Foci in Conics1/2:** F₁, F₂ are the points where the spheres touch P. They are not given by a formula.
- **Directrix:** d = P ⊓ affineSpan C.
- **Centre:** taken as the centre of symmetry of E.
- **Major axis:** the diameter (largest distance between two points of E).
- **Transverse axis:** the least distance between the two branches.
- **Area:** `volume (convexHull ℝ E)`.

## AMBIGUOUS marks
1. Conics1_a: I read "lie inside the same nappe" as both centres being strictly inside the same solid nappe. Alternative: the whole closed balls lie in the closed nappe.
2. Conics2_a: "one inside each nappe" is read through the centres, the same way.
3. Conics4_b: I read "the one of maximal area" as the unique maximiser: every other inscribed ellipse has strictly smaller area. Alternative: only ≤ is claimed.

## EXTRA HYPOTHESIS marks
None. Conics1_b and Conics2_b take `S₁ ≠ S₂` and the tangency data as hypotheses. These only restate the source's "two spheres S1, S2 … tangent along C1, C2 … at F1, F2". The hypotheses `hu : u ≠ 0` (the axis needs a direction) and `finrank P.direction = 2` (P is a plane) are part of the setting. Conics3 a/b take β < π/2 because the source says "not a circle".

## Obligations
- `classical_Conics3_obligation`: the directrix P ∩ P_C is a line when β < π/2. This is the only well-formedness obligation. Conics5 needs no obligation, because I treat the foci as given by the ellipse (`IsEllipseWithFoci`), and existence of the inellipse is Conics4_a.

## Compiler summary
Compiled on jack with `lake env lean PaperConicsClassical.lean`. The output is only `declaration uses 'sorry'` warnings (13 declarations), with no errors or other warnings. Earlier iterations fixed:
- an ambiguous `angle`, which I changed to `InnerProductGeometry.angle`;
- comment cleanup.

## Files read
- `/tmp/blindConics/classical_statements.txt` (my only mathematical input).
- My own scratch file `/tmp/blindConics/scratch/S.lean`, used for `#check`s. It was copied to jack as `reformal/PaperConicsScratch.lean` and compiled there.
- My own `Classical.lean`.

I listed `/tmp/blindConics` and saw `brief.txt`, but did **not** read it. I read no other files and did no web search.
