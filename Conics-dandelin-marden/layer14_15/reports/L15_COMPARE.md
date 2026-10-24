# L15 classical comparer — Paper Conics (Dandelin spheres; Marden / Steiner inellipse)

Machine: jack (`jack`). Start 2026-10-22 03:16 EDT, finish 05:12 EDT. **Wall time ≈ 1 h 56 min.**
All work was done inline; no sub-agents were used. Every `lake build`/`lake env lean` ran under `flock ~/l15jack.lock`. Library files were not edited. There was no `lake update` and no cache download.

## Inputs and fresh clones
| repo | pinned commit (paper `\commitD`/`\commitM`) | clone | Mathlib | gate |
|---|---|---|---|---|
| dandelin | 205e4807a71d05898967d870e4528fb97d78b26d | `~/l15Conics_dandelin` | 0df444a (symlink `~/barbier/.lake/packages`) | `PASS (85 declarations, standard axioms only)` |
| marden | bd2cd3c9870905a04d38d079be4d83c824cbf9db | `~/l15Conics_marden` | 0df444a (same symlink) | `PASS (18 declarations, standard axioms only)` |

Gate logs: `~/l15Conics_gate_{dandelin,marden}.log`.
- Paper text inconsistency, already noted in L14: the Availability paragraph says `a366dcc`, but every link macro uses `205e480`. I used `205e480`.
- Writer file `/tmp/blindConics/Classical.lean` is identical to `jack:~/reformal/PaperConicsClassical.lean` (md5 `4361ec20…a13b`, same as recorded in the writer's report).

## Method
- Each scratch file copies the writer's definitions **verbatim**. Each `classical_X` statement is packaged as `def classical_X : Prop := ∀ binders, statement`; this is mechanical, and the binders and body are unchanged.
- The Marden scratch re-proves the five L14 bridge lemmas (collinearity ↔ Im, midpoint, centroid, focal sum, line parametrisation) under the name `Marden.l15_*`. This is copied text, proved against the *published* library only; the L14 library files were not used.

## Results
| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| Conics1_a (β>α: exactly two Dandelin spheres, centres inside the same nappe, opposite sides of P) | **E** | `cov_Conics1_a` | — | From `dandelin_exists`, `one_nappe`, `ellipse_nonempty`. **NEW:** the writer's "Dandelin sphere" is *any* sphere tangent to every generator, not just an axis sphere. I proved in ℝ³ that these are exactly the axis spheres `(V+dû, \|d\| sin α)` (`l15_tangent_cone_iff`). The paper only gets uniqueness among axis spheres. |
| Conics1_b (XF₁+XF₂ = k = generator segment between C₁, C₂ = major axis) | **E** | `cov_Conics1_b` | — | Focal sum from `dandelin_exists`. **NEW:** generator-segment length `\|d₁−d₂\| cos α` for every generator (`l15_gen_segment`); k = diameter of the section via `IsGreatest` (`l15_isGreatest`); contact circle C identified as sphere ∩ cone. The paper states none of these three. |
| Conics2_a (β<α: exactly two spheres, one in each nappe) | **E** | `cov_Conics2_a` | — | From `dandelin_hyperbola` (`d₂<0<d₁`) plus the classification above. |
| Conics2_b (\|XF₁−XF₂\| = k = generator segment = least distance between branches) | **E** | `cov_Conics2_b` | — | From `dandelin_hyperbola` (`cone2` iff), `hyp_upper`/`hyp_lower`, `hyp_both_nappes`. **NEW:** the `IsLeast` transverse-axis clause, with the two vertices constructed on the focal line and branches told apart by the sign of ⟪X−V,u⟫; also the generator-segment clause. |
| Conics3_obligation (P ⊓ affineSpan C is a line) | **E** (obligation **proved**) | `cov_Conics3_obligation` | — | **NEW:** `affineSpan C` = axis plane `⟪Y−V,û⟫ = d cos²α` (`l15_span_circle`, built from two antipodal circle points); P ⊓ it = repo `directrix` (`l15_directrix_eq`); the line is explicit via `decomp_of_finrank_le_three`. |
| Conics3_a (XF = (cos β/cos α)·dist(X, P ⊓ P_C)) | **E** | `cov_Conics3_a` | — | `mem_cone2_iff_focal_directrix` + `tangent_of_proj`; bridge `ecc ⟪û,n⟫ cos α = cos β / cos α` from `cos β = √(1−⟪û,n⟫²)` (`l15_planeAxisAngle`). |
| Conics3_parabola_unique (β=α ⇒ ∃! Dandelin sphere) | **E** | `cov_Conics3_parabola_unique` | — | Like `directrix_parabola`, but uniqueness is over *all* writer Dandelin spheres (via the classification), not only axis spheres. |
| Conics3_b (e<1 / e=1 with P∩K = {XF = dist(X,d)} / e>1) | **E** | `cov_Conics3_b` | — | Inequalities from strict monotonicity of cos. The parabola set equality uses Conics3_a plus `directrix_converse` (repo). |
| Conics3_c (planar converse: {XF = e·dist(X,d)} is an ellipse/parabola/hyperbola in standard form with focus F, directrix d) | **O** | — (not proved) | entire statement | The paper's converse (Thm dirconv) lives on the cone, not in an abstract plane `E2` with `E2 ≃ᵃⁱ[ℝ] E2` normal forms. I checked the statement as written by hand: it is **true** (e = c/a, directrix x = a²/c; both hyperbola branches use the same focus–directrix pair). Building the isometry φ was too costly for the time slot. |
| Conics4_a (∃! Steiner inellipse) | **E** (+ NEW proof) | `cov_Conics4_a` | — | Existence from `marden` + `nondeg_of_midpoints`; uniqueness from `steiner_unique`. **NEW:** (i) the writer's `E ∩ line = {midpoint}` gives the repo's strict tangency `∀ t≠0, 2A < focalSum` by an IVT argument (`l15_strict_of_inter`); (ii) the Marden ellipse **lies in the closed triangle** (half-plane/convexity argument, `l15_marden_steiner`). The repo/paper never states (ii). |
| Conics4_b (centre (a+b+c)/3; area = π/(3√3)·area; strict maximality among inscribed ellipses) | **N** | `cov_Conics4_b_part` (centre clause) | area formula, max-area clause | Centre of symmetry follows from foci = Marden foci and Vieta. Area and maximal area are **out of the paper's scope**: it claims neither, and the repo has no measure theory. Under my reading both are true (affine image of the incircle in an equilateral triangle), so this is **paper narrower**, not a false statement. |
| Conics5 (roots p′ = {f₁,f₂} as multiset; Vieta) | **E** | `cov_Conics5` | — | `steiner_unique` + `vieta` + `roots_C_mul`/`roots_mul`. |
| Conics5_double_root (double root ⇒ circle centred there; double root ⇔ equilateral) | **E**/**O** | `cov_Conics5_double_root` | — | The circle part is from `steiner_unique`. **NEW / out of scope:** discriminant `(z₁−z₂)² = 4/9 (u²−uv+v²)` and `u²−uv+v²=0 ⇔ \|u\|=\|v−u\|=\|v\|` (`l15_equilateral_iff`). |

Summary: 11 E (Conics5_double_root counted as E, though its equilateral half is out of scope), 1 N (4_b: area and max-area missing), 1 O not proved (3_c). **No D:** no writer statement turned out false, and no repo theorem contradicts a classical statement.

## NEW PROOFS (comparer-side, scratch only)
- `l15_tangent_cone_iff`: in ℝ³, a sphere of positive radius meets every generator in exactly one point **iff** it is an axis sphere `(V + dû, |d| sin α)` with d ≠ 0. The proof uses three generators in directions k û ± s f and k û + s g. This strengthens the paper, whose Dandelin uniqueness is only among axis spheres.
- `l15_plane_sphere` / `_conv`, `l15_line_sphere`: singleton-intersection tangency ↔ distance condition (plane and line).
- `l15_plane_normal`, `l15_planeAxisAngle`: the writer's `planeAxisAngle` satisfies `cos β = √(1−⟪û,n⟫²)` and lies in [0, π/2].
- `l15_cone_eq`: the writer's angle cone equals the repo's `cone2 V û (cos α)`.
- `l15_span_circle`, `l15_directrix_eq`, `cov_Conics3_obligation`: affine span of the contact circle, and the directrix line.
- `l15_gen_segment`, `l15_isGreatest`, the IsLeast part of `cov_Conics2_b`: generator segments, major axis, transverse axis.
- `l15_strict_of_inter`: "E ∩ line = {m}" ⇒ strict focal tangency (IVT on the focal sum along the line).
- `l15_halfplane`, `l15_mem_hull`, `l15_marden_steiner`: the Marden ellipse lies in the closed triangle.
- `l15_equilateral_iff`, the discriminant step: double critical point ⇔ equilateral.

## Obligations
- `classical_Conics3_obligation` (directrix is a line): **proved** (`cov_Conics3_obligation`), not assumed.
- No other construction obligations. No theorem carries any extra hypothesis: every `cov_` theorem proves the writer's `Prop` exactly as written.

## Compile, forbidden grep, axioms
- `lake env lean scratch/L15_compare.lean`: **rc=0** in both repos, with 0 errors; only linter/deprecation warnings. Outputs are in `~/l15Conics_out_{marden,dandelin}.txt`.
- Forbidden grep (`sorry|admit|native_decide|axiom`) over both scratch files: **0 hits**.
- `#print axioms`: every one of the 12 `cov_` theorems reports `[propext, Classical.choice, Quot.sound]`:
  - `cov_Conics1_a`, `cov_Conics1_b`
  - `cov_Conics2_a`, `cov_Conics2_b`
  - `cov_Conics3_obligation`, `cov_Conics3_a`, `cov_Conics3_b`, `cov_Conics3_parabola_unique`
  - `cov_Conics4_a`, `cov_Conics4_b_part`
  - `cov_Conics5`, `cov_Conics5_double_root`

## Library hashes (before = after; `find … | sort | xargs sha256sum | sha256sum`, scratch excluded)
- dandelin: `7df3f521c53cec99e80e582e03139b6efff185721efe81aaa0c35a425e374294`, unchanged. `git status` shows only `?? scratch/L15_compare.lean`.
- marden: `1786070c5adae94a4ea1e66534a147e140394e595bef91208ad3f9b69320f5aa`, unchanged. `git status` shows only `?? scratch/L15_compare.lean`.

## Scratch paths
- jack: `~/l15Conics_marden/scratch/L15_compare.lean` (658 lines, sha256 `761096bd…ef0`) and `~/l15Conics_dandelin/scratch/L15_compare.lean` (1558 lines, sha256 `da684526…164`).
- Local copies: `<ws>/AFM/L14L15/Conics/L15_scratch/L15_compare_{marden,dandelin}.lean`. Build pieces are in `/tmp/l15c/`.

## Remarks on the writer's choices
- Reading AMBIGUOUS 1/2 via centres (`InsideNappe` of the centres) is fine: for an axis sphere the centre lies on the axis, so it is inside a nappe. The closed-ball reading would also hold (`cone_outside_sphere`) but was not formalised.
- `IsSteinerInellipse` asks for "lies in the closed triangle". The paper never claims this, and it needed a new proof.
- In Conics2_b, "branch" is read via the sign of ⟪X−V,u⟫. This matches the repo's nappe split.
