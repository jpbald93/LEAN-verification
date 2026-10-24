# L14_REPORT — Paper F, Part A (inscribed parabola), repo `~/lean/l14_parabola`

Layer 14: for each main theorem, a statement **whose type mentions only Mathlib** (`l14_*`), proved
from the library theorem through bridges (`l14b_*`), and a **concrete witness** (`l14w_*`) proving
that every hypothesis holds and that the conclusion is non-degenerate.
New file: `QuadMiquel/L14Parabola.lean` (one `import` line appended to `QuadMiquel.lean`; the
`REQUIRED` line of `gate.sh` extended; nothing else changed).

## Mathlib-only configuration (raw data)
* Lines: `line[ℝ, pᵢ, qᵢ]` with `pᵢ ≠ qᵢ` (i = 1..4).
* General position: the six `¬ line[ℝ,pᵢ,qᵢ].Parallel line[ℝ,pⱼ,qⱼ]`, and the four
  `¬ ∃ z, z ∈ Lᵢ ∧ z ∈ Lⱼ ∧ z ∈ Lₖ`.
* Vertices: arbitrary points `aᵢⱼ` with `aᵢⱼ ∈ Lᵢ ∧ aᵢⱼ ∈ Lⱼ` (the bridge `l14b_meet` proves each
  is the unique such point).
* Triangles: arbitrary `Tₖ : Affine.Triangle ℝ ℂ` with `T₁.points = ![a₂₃,a₂₄,a₃₄]`, `T₂ = ![a₁₃,a₁₄,a₃₄]`,
  `T₃ = ![a₁₂,a₁₄,a₂₄]`, `T₄ = ![a₁₂,a₁₃,a₂₃]` (`l14_triangles_exist` proves they exist, i.e.
  affine independence holds).
* Miquel point: **any** `M` with `M ∈ T₁.circumsphere ∧ … ∧ M ∈ T₄.circumsphere` (no formula);
  `l14_miquel_existsUnique` proves `∃! M`.
* Directrix: `S := affineSpan ℝ {T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter}`;
  `l14_directrix_finrank` proves `Module.finrank ℝ S.direction = 1` (a genuine line, also when
  `H₃ = H₄`).
* Reflection: `EuclideanGeometry.reflection line[ℝ,p,q] M`; foot/projection:
  `EuclideanGeometry.orthogonalProjection`.
* Parabola: `{z | dist z M = Metric.infDist z S}`; tangent: `∃! z, z ∈ L ∧ dist z M = infDist z S`.
* Vertex: stated as a property — `∃! V` on the parabola with `infDist V S ≤ infDist z S` for every
  `z` on the parabola (`l14_vertex_closest`); `l14_vertex*` identify it as
  `midpoint ℝ M (orthogonalProjection S M)`.

## Table
| main theorem | l14_ (Mathlib-only) | QuadMiquel-free type verified | l14w_ witness | distinctness proved | notes |
|---|---|---|---|---|---|
| reflections_collinear | `l14_reflections_collinear` ✔ | ✔ | `l14w_reflections_collinear` ✔; perpendicular case `l14w_reflections_perp` ✔ | 4 reflections pairwise distinct (both configs) | perp. witness has `H₃ = H₄`, `H₁ ≠ H₃`, `finrank S = 1` |
| reflPt_mem_orthoLine | `l14_reflPt_mem_orthoLine` ✔ | ✔ | `l14w_reflPt_mem_orthoLine` ✔ | `H₁ ≠ H₂`, `finrank S.direction = 1`, 4 reflections distinct | |
| miquel_not_mem_orthoLine | `l14_miquel_not_mem_orthoLine` ✔ | ✔ | `l14w_miquel_not_mem_orthoLine` ✔ | `finrank = 1`, `M ∉ S`, `0 < infDist M S` | |
| parabola_tangent (+₁–₄) | `l14_parabola_tangent`, `l14_parabola_tangent₁..₄` ✔ | ✔ | `l14w_parabola_tangent` ✔ | explicit tangency points `1, -1/2+i/2, -1/2+9i/2, 7+2i` on the lines and on the parabola, pairwise distinct; `M ∉ S` | |
| tanPt_all | `l14_tanPt_all` ✔ (∃ z on L, on parabola, unique, `proj_S z = reflection_L M`) | ✔ | `l14w_tanPt_all` ✔ | projections = reflections; tangency points distinct; reflections distinct | contact point characterised by a property, not by `perpMeet` |
| vertex_onParabola | `l14_vertex_onParabola` ✔ | ✔ | `l14w_vertex` ✔ | `V = -1/2+i/2`, `V ≠ M`, `V ≠ proj_S M`, `infDist M S > 0` | V := `midpoint ℝ M (orthogonalProjection S M)` |
| dist_vertex | `l14_dist_vertex` ✔ | ✔ | `l14w_vertex` ✔ | as above | |
| vertex_closest | `l14_vertex_closest` ✔ (`∃!` nearest point) | ✔ | `l14w_vertex` ✔ | as above | **strengthened**: uniqueness of the nearest point is new (bridge `l14b_nearest_unique`) |
| newton_perp_orthoLine | `l14_newton_perp_orthoLine` ✔ | ✔ | `l14w_newton_perp_orthoLine` ✔ | `N₂ ≠ N₁`, `N₃ ≠ N₁`, `H₁ ≠ H₂`, `finrank S = 1` | midpoints via `midpoint ℝ`, inner via `inner ℝ` |
| lambert | `l14_lambert` ✔ (+ `l14_miquel_existsUnique`) | ✔ | `l14w_lambert` ✔ | `M` ≠ all six vertices; 4 tangency points distinct | |
| (aux) | `l14_triangles_exist`, `l14_directrix_finrank`, `l14_vertex` | ✔ | covered by `l14wbA_master` | | |

Witness configurations (checked in Python first, then in Lean with `norm_num` on coordinates):
* general: `L₁ = line[0,1]`, `L₂ = line[1-i, -2+2i]`, `L₃ = line[-1+3i, -2]`, `L₄ = line[-1-2i, 3]`;
  no two lines perpendicular; vertices `0, -2, 3, -3/2+3i/2, 1-i, -3-3i`; `M = i`;
  `H = (-1/2-i/2, -3+2i, 1-2i, -3/2+i/2)` (four distinct); reflections `-i, -1, -3+2i, 2-3i`.
  `l14wbA_master` proves all 20 hypotheses (6 non-parallel, 4 non-concurrent, 4 `p ≠ q`, 6 vertex
  memberships), constructs the triangles, proves `M` on the four circumspheres, and computes every
  object through Mathlib (`orthocenter`, `reflection`, `orthogonalProjection`).
* perpendicular case: `L₁ = line[0,1] ⟂ L₂ = line[0,i]`, `L₃ = line[-i, -1-2i]`, `L₄ = line[-2+3i, 2+i]`;
  `M = 1-i`, `H₃ = H₄ = 0`, reflections `1+i, -1-i, 0, 3+3i` (`l14wbP_master`, `l14w_reflections_perp`).

## New bridges (all in `QuadMiquel/L14Parabola.lean`)
`l14b_carrier`, `l14b_mem`, `l14b_mem_iff` (Line.carrier ↔ `line[ℝ,p,q]`); `l14b_genPos` (Mathlib
general position ⇒ `GenPos`); `l14b_meet` (a point of `L ∩ M` is `meet`); `l14b_setup` (whole
configuration ⇒ `GenPos` + six `meet` equalities); `l14b_tri`, `l14b_orthocenter`,
`l14b_circumcenter`, `l14b_mem_circumsphere`, `l14b_setupT` (arbitrary Mathlib triangle with given
points = library triangle; orthocenter = `ortho`; circumsphere = library sphere); `l14b_miquel`
(any point on the four circumspheres is `miquelPt` — via `miquelPt_unique`); `l14b_miquel_mem`;
`l14b_proj` (orthogonal projection onto `line[h₀,h₀+W]` characterised by membership + orthogonality);
`l14b_reflection` (`EuclideanGeometry.reflection line[p,q] = reflPt`); `l14b_midpoint`;
`l14b_finrank` (orthoLine has 1-dimensional direction); `l14b_tanPt_proj` (projection of the contact
point is the reflection); `l14b_vertex_eq`, `l14b_vertex`; `l14b_tangent_iff`;
`l14b_nearest_unique` (new geometric lemma: a parabola point within `infDist M S / 2` of `S` is the
vertex); `l14b_parallel_iff`, `l14b_noconc` (numeric criteria used by the witnesses);
`l14b_transfer` (all Mathlib objects = local ones, for the witnesses).

## FINDINGS
* **No Mathlib-only statement turned out false or needed an extra hypothesis.** All 11 main
  theorems (+ ₁–₄) were restated with the paper's hypotheses only (four lines in general position).
* The Mathlib-only statements are in places *stronger* than the library ones: the Miquel point and
  the vertex are characterised by their defining properties (`∃!`), and `l14_tanPt_all` characterises
  the contact point as the unique parabola point on `L` (no formula).
* Local `meet`/`circ`/`ortho`/`foot`/`reflPt` agree with Mathlib on every configuration
  satisfying the hypotheses (Lean bridges above; Python: 300 random rational configurations). The
  degenerate-case differences (e.g. `meet` of parallel lines is a junk value) are excluded by the
  hypotheses, so they are not reachable in any `l14_` statement.
* Perpendicular case (`L₁ ⟂ L₂`, `H₃ = H₄`): the Mathlib directrix `affineSpan {H₁..H₄}` is still a
  line (`finrank = 1`, proved in general by `l14_directrix_finrank`, and on the explicit witness).
* No theorem was skipped; no local notion had to be kept in a statement.

## Mechanical type check (no `QuadMiquel.*` constant in any `l14_` / `l14w_` statement)
Scratch file `scratch/l14_typecheck.lean` (set_option allowed only there): for every `l14_*` and
`l14w_*` theorem it (1) prints `#check @QuadMiquel.<name>` with `pp.fullNames true`,
`pp.notation false`, and (2) walks the elaborated type with `Expr.getUsedConstants` and lists every
constant in namespace `QuadMiquel`. Output `scratch/l14_typecheck.out` (4187 lines, 0 errors):
```
TYPECHECK QuadMiquel.l14_triangles_exist: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_newton_perp_orthoLine: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_directrix_finrank: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_miquel_existsUnique: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_lambert: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_reflections_collinear: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_reflPt_mem_orthoLine: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_miquel_not_mem_orthoLine: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_parabola_tangent: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_parabola_tangent₁: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_parabola_tangent₂: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_parabola_tangent₃: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_parabola_tangent₄: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_tanPt_all: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_vertex: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_vertex_onParabola: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_dist_vertex: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_vertex_closest: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_reflections_collinear: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_reflPt_mem_orthoLine: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_miquel_not_mem_orthoLine: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_parabola_tangent: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_tanPt_all: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_vertex: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_newton_perp_orthoLine: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_lambert: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_reflections_perp: QuadMiquel constants in type = []
```
`grep "QuadMiquel\."` over the printed `#check` types, after dropping each theorem's own name at the
head of its line: **0** occurrences.
(The `l14b_*` bridges deliberately mention local notions; they are not Mathlib-only statements.)

## Gate (`~/lean/jl gate`)
```
'QuadMiquel.l14b_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.l14b_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.l14b_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
… (58 lines for l14 declarations, all `[propext, Classical.choice, Quot.sound]`) …
'QuadMiquel.l14wbP_master' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (168 declarations, standard axioms only)
```

## Tamper (`~/lean/jl tamper`, rerun after the final REQUIRED fix)
```
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: QuadMiquel.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```

## Hashes of pre-existing files (sha256, before = copy taken at the start; after = at the end)
| file | before | after | status |
|---|---|---|---|
| `QuadMiquel/Algebra.lean` | `95b548bc2ee7b7c8…` | `95b548bc2ee7b7c8…` | unchanged |
| `QuadMiquel/Basic.lean` | `f7b4da7d2abf6c1f…` | `f7b4da7d2abf6c1f…` | unchanged |
| `QuadMiquel/Bridge.lean` | `fb6f3e39230d5279…` | `fb6f3e39230d5279…` | unchanged |
| `QuadMiquel/Frame.lean` | `1e7cbfc90348e688…` | `1e7cbfc90348e688…` | unchanged |
| `QuadMiquel/Miquel.lean` | `5ce67f6891f4ec1c…` | `5ce67f6891f4ec1c…` | unchanged |
| `QuadMiquel/Parabola.lean` | `bd38d47896239808…` | `bd38d47896239808…` | unchanged |
| `QuadMiquel/ParabolaPoints.lean` | `58a18c5a69370c72…` | `58a18c5a69370c72…` | unchanged |
| `QuadMiquel/Parallel.lean` | `ea33070625a61685…` | `ea33070625a61685…` | unchanged |
| `QuadMiquel/Simson.lean` | `69b49c142ec7435e…` | `69b49c142ec7435e…` | unchanged |
| `QuadMiquel.lean` | `82456dcf3e1ee7a8…` | `ae6ec61b1f4796ea…` | CHANGED (intended: one appended import) |
| `gate.sh` | `3a6ed8a281a0d899…` | `1737391c3261fd7e…` | CHANGED (intended: REQUIRED line only) |
| `tests/tamper.sh` | `5da507d51bdc4b18…` | `5da507d51bdc4b18…` | unchanged |

Full hashes are in `scratch/l14_sha_before.txt` and `scratch/l14_sha_after.txt`. The original repo
(`~/lean/quadparabola_ext`) was checked at the end to be byte-identical to the before-hashes.
`QuadMiquel.lean` differs from the original only by the appended import line; `gate.sh` only on the
`REQUIRED=` line (no names removed).

## REQUIRED names added (58)
`QuadMiquel.l14b_carrier` `QuadMiquel.l14b_mem` `QuadMiquel.l14b_mem_iff` `QuadMiquel.l14b_genPos` `QuadMiquel.l14b_meet` `QuadMiquel.l14b_setup` `QuadMiquel.l14b_tri` `QuadMiquel.l14b_orthocenter` `QuadMiquel.l14b_circumcenter` `QuadMiquel.l14b_mem_circumsphere` `QuadMiquel.l14b_setupT` `QuadMiquel.l14b_miquel` `QuadMiquel.l14b_miquel_mem` `QuadMiquel.l14b_proj` `QuadMiquel.l14b_reflection` `QuadMiquel.l14b_midpoint` `QuadMiquel.l14b_finrank` `QuadMiquel.l14b_tanPt_proj` `QuadMiquel.l14b_vertex_eq` `QuadMiquel.l14b_vertex` `QuadMiquel.l14b_tangent_iff` `QuadMiquel.l14b_nearest_unique` `QuadMiquel.l14b_parallel_iff` `QuadMiquel.l14b_noconc` `QuadMiquel.l14_triangles_exist` `QuadMiquel.l14_newton_perp_orthoLine` `QuadMiquel.l14_directrix_finrank` `QuadMiquel.l14_miquel_existsUnique` `QuadMiquel.l14_lambert` `QuadMiquel.l14_reflections_collinear` `QuadMiquel.l14_reflPt_mem_orthoLine` `QuadMiquel.l14_miquel_not_mem_orthoLine` `QuadMiquel.l14_parabola_tangent` `QuadMiquel.l14_parabola_tangent₁` `QuadMiquel.l14_parabola_tangent₂` `QuadMiquel.l14_parabola_tangent₃` `QuadMiquel.l14_parabola_tangent₄` `QuadMiquel.l14_tanPt_all` `QuadMiquel.l14_vertex` `QuadMiquel.l14_vertex_onParabola` `QuadMiquel.l14_dist_vertex` `QuadMiquel.l14_vertex_closest` `QuadMiquel.l14b_transfer` `QuadMiquel.l14wbA_base` `QuadMiquel.l14wbA_vals` `QuadMiquel.l14wbA_master` `QuadMiquel.l14w_reflections_collinear` `QuadMiquel.l14w_reflPt_mem_orthoLine` `QuadMiquel.l14w_miquel_not_mem_orthoLine` `QuadMiquel.l14w_parabola_tangent` `QuadMiquel.l14w_tanPt_all` `QuadMiquel.l14w_vertex` `QuadMiquel.l14w_newton_perp_orthoLine` `QuadMiquel.l14w_lambert` `QuadMiquel.l14wbP_base` `QuadMiquel.l14wbP_vals` `QuadMiquel.l14wbP_master` `QuadMiquel.l14w_reflections_perp`

## Python pre-checks (`scratch/`)
`l14_check.py` (exact `Fraction` arithmetic over ℚ(i)) + `l14_pick*.py` (witness search);
output in `scratch/l14_python.out`.

## Note
A first gate run listed 52 names; the 6 witness helpers `l14wbA_base/_vals/_master`,
`l14wbP_base/_vals/_master` had been missed by the name pattern. They were added; gate (168, PASS)
and tamper were rerun on the final state, and the outputs above come from that run.
