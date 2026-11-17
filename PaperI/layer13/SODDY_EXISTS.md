# L15 item I5b — Soddy existence (machine john)

File: `~/lean/l13_inversion/scratch/soddy_exists.lean` (sha256 `0ea3b3feef6fa0e9…`), namespace `SoddyExists`.

## Result: (1) MAIN achieved, plus the (2) "exactly two" classification

For three pairwise externally tangent circles with positive radii in `E2`, the file constructs both
Soddy circles explicitly and proves they are tangent to all three. It also proves that these are the
only circles tangent to the triple.

Definitions `ClassicalSignedTangent` and `ClassicalMutuallyTangent` are copied verbatim from
`PaperIClassical.lean` (sha256 prefix `1c595a90ccb3925a`, the same file the L15 comparison used).
Signed radii: `ρ < 0` means an enclosing circle that is internally tangent.

| Theorem | Statement |
|---|---|
| `soddyCentre C ρ` (def) | Explicit centre `c₀ + (Nₛ/D)(c₁−c₀) + (Nₜ/D)(c₂−c₀)`, with `Nₛ, Nₜ, D = 2r₀r₁r₂(r₀+r₁+r₂)` polynomials in `r₀,r₁,r₂,ρ` |
| `soddy_dist_sq` | If `polyP r₀ r₁ r₂ ρ = 0` (the Descartes relation in radii), then `dist(soddyCentre C ρ, cⱼ)² = (rⱼ+ρ)²` for j = 0,1,2 |
| `soddy_circle` | For `ε = ±1` and `κ = k₀+k₁+k₂ + 2ε√(k₀k₁+k₁k₂+k₂k₀) ≠ 0`, `![C 0, C 1, C 2, (soddyCentre C (1/κ), 1/κ)]` is `ClassicalMutuallyTangent` (curvature from `Inversion.descartes_solve`). The inner circle (κ₊ > 0) is externally tangent; when κ₋ < 0 the outer circle encloses the three and is internally tangent (`κ + kᵢ > 0` is proved, so it is strictly larger) |
| `classical_I5b` | **The L15 classical statement I5b, verbatim, proved** (`∃ c, ClassicalMutuallyTangent ![C 0, C 1, C 2, (c, 1/κ)]`) |
| `centre_unique` | Given ρ, the centre is unique (the centre triangle's Gram determinant is `4r₀r₁r₂(r₀+r₁+r₂) > 0`) |
| `soddy_classify` | Any `(c, ρ)` completing a Descartes configuration has `1/ρ ∈ {κ₊, κ₋}` (via `Inversion.descartes` + `descartes_solve`) and `c = soddyCentre C ρ` |
| `soddy_exactly_two` | `0 < κ₊`, `κ₊ ≠ κ₋`, and `(c,ρ)` is tangent to the triple **iff** it is the inner Soddy circle or (when `κ₋ ≠ 0`) the outer Soddy circle |

Vieta (`κ₊+κ₋ = 2Σk`, `κ₊κ₋ = 2Σk² − (Σk)²`) is already library `descartes_vieta` and is not re-proved.
Together with `soddy_exactly_two` it gives the fallback (2) content in full.

## Method
The centre is solved in barycentric form: the two linear equations from differencing the squared distances
give the coefficients. The key identity: for `α u + β v` with `u = c₁−c₀`, `v = c₂−c₀`,
`|αu+βv|² = (α²+αβ)|u|² + (β²+αβ)|v|² − αβ|u−v|²` (`gen_sq`). With the three side lengths
`(rᵢ+rⱼ)` substituted, this equals `D²(rⱼ+ρ)² + 2D·polyP` (`case0/1/2`, pure `ring`). Here
`polyP = −(r₀r₁r₂ρ)²·descartesForm(1/r₀,1/r₁,1/r₂,1/ρ)` (`polyP_eq`). The certificates were found with
sympy and checked by Lean's `ring` / `linear_combination`.

## Limits (stated plainly)
- Only the case where the three given circles are mutually **externally** tangent with positive radii, as
  in the `classical_I5b` hypotheses. Triples that already contain an enclosing circle aren't covered.
- The "line and two circles" variant isn't covered. When `κ₋ = 0` the outer solution is a line, which isn't a
  signed circle in this framework, so then there is exactly one circle (stated in `soddy_exactly_two`).
- This is a scratch file built on the library. The library itself still doesn't state existence. So the
  L15 verdict "O" for the *library* stands, but I5b is now **proved against the verbatim classical
  statement** and could be re-recorded as covered by `scratch/soddy_exists.lean`.

## Gate
```
$ ssh john@100.101.160.66 'cd ~/lean/l13_inversion && PATH=$HOME/.elan/bin:$PATH lake env lean scratch/soddy_exists.lean'
(no output)   exit 0
$ grep -nE "sorry|admit|native_decide|axiom" scratch/soddy_exists.lean
(no matches)  grep exit 1
```
Axiom check (temporary copy with `#print axioms`): `classical_I5b`, `soddy_circle`, `soddy_classify`,
`soddy_exactly_two`, `centre_unique` depend only on `[propext, Classical.choice, Quot.sound]`.
No library source was edited. `lake update` / `cache get` were not run.
