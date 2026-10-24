# Paper C — Classical-source blind formalisation report

Output: `/tmp/blindC/Classical.lean`. It is identical to `jack:~/reformal/PaperCClassical.lean` (both md5 `a624b3d51dc1596ec3f0f6a26588cf19`).
Namespace: `PaperCClassical`. Ambient space: `Plane := EuclideanSpace ℝ (Fin 2)`.

## Statement list
| Name | Source item |
|---|---|
| `classical_C1_a` | C1(a), Barbier, smooth form: a `C²` closed regular simple convex curve of constant width `w` has length `∫₀ᵀ‖γ'‖ = π w` |
| `classical_C1_a_support` | C1(a), support-function form: the envelope length equals `∫₀^{2π} p`, which equals `π w` |
| `classical_C1_b` | C1(b), general form: a convex body of constant width has `perimeter K = π w` |
| `classical_C1_b_equiv` | C1(b), equivalent form: the perimeter equals that of the disk of diameter `w` |
| `classical_C2_boundary` | C2, the boundary is three arcs of radius `w` and angle `π/3`, each centred at one vertex |
| `classical_C2_a` | C2(a): it is a convex body of constant width `w`, it is not a disk, its corners are exactly `{A,B,C}`, and each interior angle is `2π/3` |
| `classical_C2_b` | C2(b): perimeter `= 3(wπ/3) = π w` |
| `classical_C2_c` | C2(c): area `(1/2)(π−√3)w²` |
| `classical_C2_c_blaschke_lebesgue` | C2(c), Blaschke–Lebesgue: the Reuleaux triangle has the minimum area and the disk the maximum; the disk's area is `π w²/4` |
| `classical_C2_reuleaux_polygon` | C2 "more generally": Reuleaux polygons are constant-width bodies with perimeter `π w` |
| `classical_C3_a` | C3(a), Mukhopadhyaya: an oval has ≥ 4 vertices (4 distinct parameters in `[0,T)`) |
| `classical_C3_a_precise` | C3(a), "more precisely": ≥ 2 local maxima and ≥ 2 local minima of `k` |
| `classical_C3_a_doCarmo` | C3, do Carmo's variant: a `C³` curve has ≥ 4 zeros of `k'` |
| `classical_C3_b` | C3(b), Kneser: a simple closed regular `C²` curve has ≥ 4 vertices |
| `classical_C3_remark_ellipse` | Remark: an ellipse with `a ≠ b` has exactly the vertices `{0, π/2, π, 3π/2}` |
| `classical_C3_remark_circle` | Remark: every point of a circle is a vertex |
| `classical_C3_remark_nonsimple` | Remark: there is a non-simple regular closed `C²` curve with exactly 2 vertices |

## Definitions I made up (OWN DEFINITION)
- `IsPlaneConvexBody`: compact, convex, with nonempty interior.
- `supportFn K u := sSup ((⟪·,u⟫) '' K)`.
- `widthIn K u := h(u) + h(−u)`.
- `HasConstantWidth K w := 0 < w ∧ ∀ ‖u‖ = 1, widthIn K u = w`.
- `IsBoundaryParam`: `γ` on `[0,1]` is continuous, closed, injective on `[0,1)`, and its image is `frontier K`.
- `perimeter K`: the supremum over boundary parametrisations of `eVariationOn γ [0,1]`. This is the "supremum of inscribed polygon lengths" in ENNReal.
- `curveLength γ T := ∫₀ᵀ ‖deriv γ‖`.
- `reuleauxTriangle A B C w`: the intersection of the three closed balls of radius `w`.
- `interiorAngleAt K p`: the supremum of `∠ x p y` over `x, y ∈ K \ {p}`.
- `IsCornerPoint K p`: `p` is a boundary point and the interior angle there is `< π`.
- `IsReuleauxPolygonData m v w`: `2m+1` vertices in convex position with all pairwise distances `≤ w`, and each vertex at distance `w` from its two cyclically opposite vertices `i+m` and `i+m+1`. The polygon is `⋂ closedBall (v i) w`.
- `signedCurvature α t := det(α',α'')/‖α'‖³`.
- `IsVertex α t := IsLocalExtr (signedCurvature α) t`.
- `IsRegularClosedC2 α T`: `0 < T`, `T`-periodic, `ContDiff ℝ 2`, and `α' ≠ 0`.

## AMBIGUOUS marks
- `classical_C1_a`, "convex": I took this to mean the trace equals the frontier of its convex hull. The alternative is strict curvature `> 0`.
- `classical_C1_a`, "the curve has constant width": I applied it to `convexHull (range γ)`.
- `classical_C1_a_support`, "C² support function": I encoded it as `p ∈ C²`, `2π`-periodic, with `p + p'' > 0`, and took the length of the envelope curve.
- `IsReuleauxPolygonData`: the source gives no definition. The alternative is a constant-width body whose boundary is made of radius-`w` arcs centred at its corners.
- `classical_C3_a` and its variants, "convex/oval": I used `k > 0` everywhere or `k < 0` everywhere, to allow either orientation. The alternative is `k ≥ 0`.
- `classical_C3_a_precise`: I required the four extremum points to be pairwise distinct.
- `classical_C3_remark_nonsimple`: I stated it as an existence claim. The alternative is a specific limaçon, e.g. `r = 1/2 + cos θ`.

## EXTRA HYPOTHESIS marks
None. Two hypotheses are stated explicitly but come from the source text rather than being added by me:
- `0 < w` in C2, because the source says "side length w > 0".
- `ContDiff ℝ 3` in the do Carmo variant, because it needs `k ∈ C¹`.

## Obligations (needed only for the definitions to make sense)
- `supportFn_obligation`: for a convex body the `sSup` is a maximum attained on `K`.
- `perimeter_obligation`: a convex body has a boundary parametrisation as a simple closed curve, so the `⨆` is not over an empty set.

## Compiler summary
`lake env lean PaperCClassical.lean` on jack exits with code 0. The only diagnostics are 19 `declaration uses 'sorry'` warnings: 17 theorem statements and 2 obligations. There are no errors.

## Files read
- `/tmp/blindC/classical_statements.txt` (the only mathematical input).
- `/tmp/blindC/scratch/S.lean`, a scratch `#check` file I wrote myself.
- `/tmp/blindC/Classical.lean` (my own output), plus the compiler output from jack.

I ran `ls /tmp/blindC`, which listed `brief.txt`, but I did not open it. I read no other files and did no web search.
