# Layer 14 — Mathlib-only restatement + witnesses — Paper Conics (Dandelin spheres; Marden)

Machine: jack (`jack`). Start 2026-10-21 21:50 EDT, finish 22:27 EDT. **Wall time ≈ 37 min.**
All work was done inline (no subagents). Nothing was committed or pushed.

## Sources
| repo | URL | pinned commit (from `\commitD`/`\commitM`) | clone dir | toolchain | Mathlib rev |
|---|---|---|---|---|---|
| dandelin | https://github.com/jpbald93/dandelin | 205e4807a71d05898967d870e4528fb97d78b26d | ~/l14Conics_dandelin | v4.33.1 | 0df444a360eaa60ab8c11dca51a86af692955474 |
| marden | https://github.com/jpbald93/marden | bd2cd3c9870905a04d38d079be4d83c824cbf9db | ~/l14Conics_marden | v4.33.1 | 0df444a360eaa60ab8c11dca51a86af692955474 |

Both match the expected pins, so `.lake/packages` is symlinked to `~/barbier/.lake/packages`. There was no `lake update` and no cache download.
Side note: the paper's Availability paragraph says "Line references are to commits `a366dcc` and `bd2cd3c`", but the `\commitD` macro used in every link is `205e480`. I used `205e480`; `a366dcc` is an ancestor of it on master. This is a minor inconsistency in the paper text.

## Files added
- `Dandelin/L14.lean` (732 lines, sha256 22dd0827…d365). `Dandelin.lean` gets `import Dandelin.L14` appended at the end.
- `Marden/L14.lean` (213 lines, sha256 0e9347dd…d014). `Marden.lean` gets `import Marden.L14` appended at the end.
- `gate.sh`: only the `REQUIRED=` line changed (new names appended).
- The L14 files contain no `sorry`/`admit`/`axiom`/`native_decide`/`#eval`/`set_option`/`macro`/`notation`/`run_cmd` (grep is empty, and the gate token filter passes).

## Modelling choices (for A)
- **Cone, by its defining property:** apex `V`, unit axis `u`, half-angle `α ∈ (0, π/2)`.
  - Nappe: `X = V ∨ InnerProductGeometry.angle (X - V) u = α`.
  - Double cone: `X = V ∨ angle (X-V) u = α ∨ angle (X-V) u = π - α`.
  - The `X = V` disjunct is needed because Mathlib sets `angle 0 u = π/2`.
- **Plane:** `AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ`, with `‖n‖ = 1`.
- **Spheres/tangency:** `EuclideanGeometry.Sphere`, `Sphere.IsTangentAt`, `Sphere.IsTangent`.
- **Directrix:** `mk' p₀ (ℝ∙n)ᗮ ⊓ mk' (V + (d cos²α)•u) (ℝ∙u)ᗮ`. Distance to it is `Metric.infDist`.
- **Eccentricity:** written out as `√(1 - ⟪u,n⟫²) / cos α`.
- **Marden:**
  - `¬ Collinear ℝ {a,b,c}`.
  - `Polynomial.derivative ((X - C a)(X - C b)(X - C c)) = C 3 (X - C z₁)(X - C z₂)`.
  - `midpoint ℝ`, `dist`, `line[ℝ,a,b]`, `Finset.univ.centroid ℝ ![a,b,c]`.
  - Tangency is metric, as in the paper: every point of the side line other than the midpoint has a strictly larger focal sum.

## Bridges (new, proved)
| bridge | content |
|---|---|
| `Dandelin.l14_mem_cone_iff` / `l14_mem_cone2_iff` / `l14_mem_lower_iff` | angle form (with apex) ↔ `cone`, `cone2`, `cone V (-u)` (from the repo's `mem_cone_iff_angle`) |
| `Dandelin.l14_mem_plane_iff` | `mk' p₀ (ℝ∙n)ᗮ` ↔ `plane p₀ n` |
| `Dandelin.l14_isTangentAt_plane` | **new direction**: Mathlib `IsTangentAt F (mk' p₀ (ℝ∙n)ᗮ)` ⇒ `F` is the projection of the centre and `|⟪C-p₀,n⟫| = r` |
| `Dandelin.l14_isTangentAt_proj`, `l14_isTangent_plane_iff` | `IsTangent ↔ |⟪C-p₀,n⟫| = r` (distance condition ↔ Mathlib tangency) |
| `Dandelin.l14_directrix_eq` | repo `directrix` = intersection of two Mathlib affine subspaces |
| `Dandelin.l14_proj_ne` | projections of distinct axis points onto a non-perpendicular plane are distinct |
| `Marden.l14_collinear_iff` | `Collinear ℝ {a,b,c} ↔ Im((c-a)/(b-a)) = 0` |
| `Marden.l14_midpoint_eq`, `l14_centroid_eq`, `l14_dist_add_dist`, `l14_strict_on_line`, `l14_strict_of_on_line` | midpoint/centroid/focalSum; "∀ p ∈ line[ℝ,x,y], p ≠ midpoint → S < …" ↔ the repo's `∀ t ≠ 0` parametrisation (the converse needs `x ≠ y`) |

## Repo: marden
| paper theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Thm (Marden) `marden` | `Marden.l14_marden` | yes (0 hits) | `l14w_marden`: triangle `0, 5, 1+4i`, `z₁ = 1+2i`, `z₂ = 3+(2/3)i` (`l14w_derivative` proves `p' = 3(X-z₁)(X-z₂)` exactly) | vertices pairwise distinct; foci distinct (not a circle); 3 midpoints pairwise distinct; `dist z₁ z₂ < S` (non-degenerate ellipse) | the conclusion also includes non-degeneracy (from `nondeg_of_midpoints`) and centre = Mathlib centroid; distinctness hypotheses are derived from `¬Collinear` |
| Thm (uniqueness) `steiner_unique` | `Marden.l14_steiner_unique` | yes | same witness (its hypotheses on `a,b,c,z₁,z₂` are those of `l14w_marden`; `f = z`, `S` = Marden sum satisfies the rest by `l14_marden`) | as above | strong (strict) form only |
| Cor `steiner_inellipse_iff` | not separately restated | — | — | — | equals `l14_marden` ∧ `l14_steiner_unique` |
| `steiner_inellipse_unique` (weak `≤` form), lemmas `midpoint_mul`, `focal_le_of_mul`, … | not restated | — | — | — | internal lemmas / weaker variant; skipped |

Gate before → after: `PASS (18 declarations, standard axioms only)` → `PASS (24 declarations, standard axioms only)`.
REQUIRED added: `Marden.l14_collinear_iff Marden.l14_marden Marden.l14_steiner_unique Marden.l14w_not_collinear Marden.l14w_derivative Marden.l14w_marden`.
Tamper: `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, falsehyp, wrap).
Hashes: 5 of 6 pre-existing `.lean` files are unchanged versus the fresh clone. The one difference is `Marden.lean`, whose only diff is the appended `import Marden.L14` line.

## Repo: dandelin
| paper theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Thm ellipse (i)–(iv) `dandelin_exists` | `Dandelin.l14_dandelin_ellipse` (any real inner product space `E`) | yes | `l14w_dandelin_ellipse`: ℝ³, `V=0`, `u=e₃`, `α=arccos(4/5)`, plane through `e₃` with normal `(0,3/5,4/5)` | `F₁ ≠ F₂`, `L > 0`, section point `(0,12/25,16/25) ≠ V`, every directrix non-empty | tangency is Mathlib `IsTangent`/`IsTangentAt`; uniqueness is among the axis spheres `(V+d•u, d sin α)`, as in the paper |
| Thm hyperbola (i)–(iv) + Thm converse (b, double-cone iff) | `Dandelin.l14_dandelin_hyperbola` | yes | `l14w_dandelin_hyperbola`: plane `x = 1` (`⟪u,n⟫ = 0`) | `F₁ ≠ F₂`, `L > 0`, points `(1,0,±4/3)` on the upper and lower nappes | `e > 1`; the focus–directrix relation is strengthened to the iff on the double cone (combining `dandelin_hyperbola` and `mem_cone2_iff_focal_directrix`); the one-nappe counterexample half of (b) is not restated |
| Thm focus–directrix (ellipse) + Thm converse (a, ellipse) | `Dandelin.l14_directrix_ellipse` | yes | covered by `l14w_dandelin_ellipse` (it includes `|⟪u,n⟫| = 4/5 < 1` and non-empty directrices) | as ellipse | `e < 1`; iff for each focus |
| Thm parabola + Thm converse (a, parabola) | `Dandelin.l14_parabola` | yes | `l14w_parabola`: normal `(4/5,0,3/5)`, `⟪u,n⟫ = 3/5 = sin α` | non-apex section point `(3/8,0,1/2)` | `e = 1`, unique tangent axis sphere |
| Thm regimes (b),(c),(d) in ℝ³ `regime_R3` | `Dandelin.l14_regime_R3` | yes | `l14w_regime_inscribed` (ellipse configuration: apex off the plane, upper-nappe point exists) | non-apex point with angle `α` | (a) and (e), and the general-`E` dimension versions, are not restated |
| Thm apex (a),(b),(c) in ℝ³ `apex_section_R3` | `Dandelin.l14_apex_R3` | yes | `l14w_apex`: normals `e₃` / `(4/5,0,3/5)` / `e₂` (point / line / two-line cases) | line case: `(-3,0,4) ≠ V`; two-line case: `(3,0,4) ≠ (-3,0,4)`, both `≠ V`, both on the section | lines are written as `line[ℝ, V, V + w]`; the two lines meet only at `V` (stated as `∩ = {V}`) |
| Lemma inscribed spheres | `Dandelin.l14_inscribed` | yes | in `l14w_regime_inscribed` (`X = (3,0,4)`, `d = 1`) | `X ≠ V` | Mathlib `IsTangentAt` to the generator line, plus `d sin α ≤ dist X C` |
| Lemmas conetan / infdist / proj, `tangent_lengths_eq`, `focal_dist_eq_ecc_mul` (arbitrary sphere) | not restated | — | — | — | internal lemmas; `l14_isTangent_plane_iff` is the Mathlib-only form of Lemma proj |

Gate before → after: `PASS (85 declarations, standard axioms only)` → `PASS (102 declarations, standard axioms only)`.
REQUIRED added: `Dandelin.l14_mem_cone_iff Dandelin.l14_mem_cone2_iff Dandelin.l14_isTangentAt_plane Dandelin.l14_isTangent_plane_iff Dandelin.l14_directrix_eq Dandelin.l14_dandelin_ellipse Dandelin.l14_inscribed Dandelin.l14_dandelin_hyperbola Dandelin.l14_directrix_ellipse Dandelin.l14_parabola Dandelin.l14_regime_R3 Dandelin.l14_apex_R3 Dandelin.l14w_dandelin_ellipse Dandelin.l14w_dandelin_hyperbola Dandelin.l14w_parabola Dandelin.l14w_apex Dandelin.l14w_regime_inscribed`.
Tamper: `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, falsehyp, wrap).
Hashes: 14 of 15 pre-existing `.lean` files are unchanged versus the fresh clone. The one difference is `Dandelin.lean`, whose only diff is the appended `import Dandelin.L14` line.

## FINDINGS
- **No Mathlib-only restatement turned out false or needed an extra hypothesis.** Every restated theorem was proved with exactly the classical hypotheses (`‖u‖ = ‖n‖ = 1`, `0 < α < π/2`, the regime inequality, the apex off the plane or on the nappe side). The repo's `k² + s² = 1, k > 0, s > 0` are derived from `k = cos α`, `s = sin α`.
- Observations, none of them defects:
  1. Mathlib's `angle 0 u = π/2`, so the angle-defined cone must include the apex explicitly (`X = V ∨ …`). Without that disjunct, "section = focal locus" would still be true here (the plane misses `V`), but the double-cone and apex-section statements would be wrong.
  2. In the ellipse/parabola statements the axis-sphere radius is `d sin α`, following the repo, not `|d| sin α`. For `d < 0` this is a Mathlib `Sphere` with negative radius, which is never tangent, so "tangent ↔ d ∈ {d₁, d₂}" stays faithful. The hyperbola statement uses `|d| sin α`, as in the repo.
  3. The bridge `l14_strict_of_on_line` (Mathlib "line meets the closed region only at the midpoint" ⇒ repo `∀ t ≠ 0`) needs the side to be non-degenerate (`x ≠ y`). This follows from `¬Collinear`, so it is not an extra hypothesis.
  4. Paper text/commit discrepancy (`a366dcc` vs `205e480`); see Sources.

## Type-check output (mechanical namespace check)
- Scratch files are `~/l14Conics_scratch/TypeCheck{Marden,Dandelin}{,Raw}.lean`, outside both repos. The `set_option`s appear only there.
- Each one `#check`s every l14 theorem with `pp.fullNames true`. The `Raw` variants also set `pp.notation false`, so notation such as `!₂[…]` cannot hide a constant.
- After stripping the declaration name itself, grep for `Marden\.` / `Dandelin\.` gives **0 hits in all four outputs**.
- Excerpt:
```
@Dandelin.l14_dandelin_ellipse : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E]
  {V u n p₀ : E} {α : ℝ}, ‖u‖ = 1 → ‖n‖ = 1 → 0 < α → α < Real.pi / 2 →
    Real.sin α < |Inner.inner ℝ u n| → 0 < Inner.inner ℝ u n * Inner.inner ℝ (p₀ - V) n →
      ∃ d₁ d₂ F₁ F₂ L, 0 < d₁ ∧ d₁ < d₂ ∧ 0 < L ∧
        (∀ (d : ℝ), { center := V + d • u, radius := d * Real.sin α }.IsTangent (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ↔ d = d₁ ∨ d = d₂) ∧
        { center := V + d₁ • u, radius := d₁ * Real.sin α }.IsTangentAt F₁ (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ∧
        { center := V + d₂ • u, radius := d₂ * Real.sin α }.IsTangentAt F₂ (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ∧
        Inner.inner ℝ (V + d₁ • u - p₀) n * Inner.inner ℝ (V + d₂ • u - p₀) n < 0 ∧
        ∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ, X = V ∨ InnerProductGeometry.angle (X - V) u = α ↔ Dist.dist X F₁ + Dist.dist X F₂ = L
@Marden.l14_marden : ∀ {a b c z₁ z₂ : ℂ}, ¬Collinear ℝ {a, b, c} →
    Polynomial.derivative ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C c)) =
      Polynomial.C 3 * (Polynomial.X - Polynomial.C z₁) * (Polynomial.X - Polynomial.C z₂) →
    Dist.dist (midpoint ℝ b c) z₁ + Dist.dist (midpoint ℝ b c) z₂ = Dist.dist (midpoint ℝ a b) z₁ + Dist.dist (midpoint ℝ a b) z₂ ∧ … ∧
    (∀ p ∈ line[ℝ, a, b], p ≠ midpoint ℝ a b → Dist.dist (midpoint ℝ a b) z₁ + Dist.dist (midpoint ℝ a b) z₂ < Dist.dist p z₁ + Dist.dist p z₂) ∧ … ∧
    Dist.dist z₁ z₂ < Dist.dist (midpoint ℝ a b) z₁ + Dist.dist (midpoint ℝ a b) z₂ ∧
    midpoint ℝ z₁ z₂ = Finset.centroid ℝ Finset.univ ![a, b, c]
```
- Full outputs are in `~/l14Conics_scratch/typecheck_*.out` on jack and `typecheck_all.txt` next to this report.

## Logs on jack
- Builds: `~/l14Conics_build0_*.log`.
- Gates: `~/l14Conics_gate0_*.log` (before), `~/l14Conics_gate1_*.log` (after).
- Tamper: `~/l14Conics_tamper_*.log`.
- Hashes: `~/l14Conics_hashes_*.pre`.

Status: **COMPLETE** for both repos.
