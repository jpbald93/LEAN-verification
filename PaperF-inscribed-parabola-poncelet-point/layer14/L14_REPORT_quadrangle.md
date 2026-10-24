# L14_REPORT — Paper F, Part B (complete quadrangle), repo `~/lean/l14_quadrangle`

Layer 14: for each main theorem, a statement **whose type mentions only Mathlib** (`l14_*`), proved
from the library theorem through bridges (`l14b_*`), and a **concrete witness** (`l14w_*`) proving
that every hypothesis holds and that the conclusion is non-degenerate.
New file: `QuadMiquel/L14Quadrangle.lean` (one `import` line appended to `QuadMiquel.lean`; the
`REQUIRED` line of `gate.sh` extended; nothing else changed).

## Mathlib-only configuration (raw data)
* Points `a b c d : ℂ` with `¬ Collinear ℝ {a,b,c}`, `{a,b,d}`, `{a,c,d}`, `{b,c,d}`.
* Triangles: arbitrary `Tabc Tabd Tacd Tbcd : Affine.Triangle ℝ ℂ` with `Tabc.points = ![a,b,c]` etc.
  (`l14_triangles_exist` proves they exist).
* Non-orthocentric: `d ≠ Tabc.orthocenter` (Mathlib orthocentre).
* Poncelet point: **any** `P` on the four `Affine.Simplex.ninePointCircle`s (no formula);
  `l14_poncelet_on_ninepoint` proves `∃! P`.
* Feet: `(EuclideanGeometry.orthogonalProjection line[ℝ, x, y] z : ℂ)`; concyclic:
  `EuclideanGeometry.Cospherical`; diagonal points: arbitrary `x₁ ∈ line[ℝ,a,b] ∩ line[ℝ,c,d]`,
  `x₂ ∈ line[ℝ,a,c] ∩ line[ℝ,b,d]`, `x₃ ∈ line[ℝ,a,d] ∩ line[ℝ,b,c]`; non-parallel opposite sides via
  `AffineSubspace.Parallel`.
* S₄: stated for the *set* `{a,b,c,d}`: `P` is on the nine-point circle of **every** Mathlib triangle
  `T` with `Set.range T.points ⊆ {a,b,c,d}` (any labelling/order), and it is the only point with
  that property.

## Table
| main theorem | l14_ (Mathlib-only) | QuadMiquel-free type verified | l14w_ witness | distinctness proved | notes |
|---|---|---|---|---|---|
| poncelet_on_ninepoint | `l14_poncelet_on_ninepoint` ✔ (`∃! P` on the 4 nine-point circles) | ✔ | `l14w_poncelet_on_ninepoint` ✔ | the 4 nine-point circles are pairwise distinct (distinct centres); `P = 1-i` explicit | |
| ninepoint_concur | `l14_ninepoint_concur` ✔ | ✔ | `l14w_poncelet_on_ninepoint` ✔ | as above | |
| ninepoint_unique | `l14_ninepoint_unique` ✔ (3 circles meet in ≤ 1 point) | ✔ | `l14w_poncelet_on_ninepoint` ✔ | as above | |
| ponDen_eq_zero_iff | `l14_ponDen_eq_zero_iff` ✔: `(∃! P on the 4 circles) ↔ d ≠ Tabc.orthocenter` | ✔ | both directions: `l14w_poncelet_on_ninepoint` (≠) and `l14w_orthocentric` (=) ✔ | orthocentric: two distinct common points `2 ≠ 1/2+i` | the local polynomial `ponDen` has no Mathlib counterpart; restated by its geometric meaning (see FINDINGS) |
| orthocentric_ninePointCircle_eq | `l14_orthocentric_ninePointCircle_eq` ✔ | ✔ | `l14w_orthocentric` ✔ (paper's example `0, 4, 1+2i, 1+3i/2`) | the common circles contain 2 distinct points | |
| poncelet_on_pedal_d | `l14_poncelet_on_pedal_d` ✔ | ✔ | `l14w_poncelet_on_pedal_d` ✔ | feet `2i, -2, -3/2+3i/2` and `P` pairwise distinct | needs `¬ Cospherical {a,b,c,d}` exactly as the library |
| poncelet_on_pedal_c | `l14_poncelet_on_pedal_c` ✔ | ✔ | `l14w_poncelet_on_pedal_c` ✔ | 4 distinct | |
| poncelet_on_pedal_b | `l14_poncelet_on_pedal_b` ✔ | ✔ | `l14w_poncelet_on_pedal_b` ✔ | 4 distinct | |
| poncelet_on_pedal_a | `l14_poncelet_on_pedal_a` ✔ | ✔ | `l14w_poncelet_on_pedal_a` ✔ | 4 distinct | |
| poncelet_on_diagonal_circle | `l14_poncelet_on_diagonal_circle` ✔ | ✔ | `l14w_poncelet_on_diagonal_circle` ✔ | diagonal points `2i/3, -1/2+i/2, 2/3-4i/3` and `P` pairwise distinct; opposite sides non-parallel | diagonal points are *any* points of the intersections |
| poncelet_S4 | `l14_poncelet_S4` ✔ (property of the set) | ✔ | `l14w_poncelet_on_ninepoint` ✔ | | every Mathlib triangle with vertices in `{a,b,c,d}`, any order |

Witness configuration (Python-checked, then `norm_num`): `a = 0, b = -i, c = 2-2i, d = -1+2i` — no
two of the six joining segments perpendicular, `Tabc.orthocenter = -1-2i ≠ d`, not concyclic
(`d` is off the circumcircle centred at `3/2 - i/2`), opposite sides non-parallel; nine-point
centres `1/4-5i/4, 5/4+3i/4, -11/4-9i/4, -3/4-5i/4`; `P = 1-i`. Everything is in `l14wbQ_master`.
Orthocentric witness: the paper's `0, 4, 1+2i, 1+3i/2` (`l14w_orthocentric`).

## New bridges (all in `QuadMiquel/L14Quadrangle.lean`)
`l14b_cr_ne`, `l14b_QGen` (Mathlib non-collinearity ⇒ `QGen`); `l14b_tri`, `l14b_orthocenter`,
`l14b_mem_npc`, `l14b_npc`, `l14b_npc_center` (arbitrary Mathlib triangle = `tri`; orthocenter =
`ortho`; nine-point circle membership/centre); `l14b_foot` (Mathlib projection onto `line[p,q]` =
`foot · (lineThrough p q)`); `l14b_diag` (a point of `line[p,q] ∩ line[r,s]` = `diagPt`);
`l14b_ne_of_ncol`; `l14b_ninePointCircle_eq_of_range_eq` (new: equal vertex sets ⇒ equal Mathlib
nine-point circles; Mathlib has this for circumcenter/centroid but not ninePointCircle);
`l14b_range3`, `l14b_range_sub`, `l14b_tri_cases` (a triangle with vertices in `{a,b,c,d}` has the
vertex set of one of the four standard triangles); `l14b_cosph`; `l14b_parallel_iff`;
`l14b_transfer`, `l14b_poncelet_mem`, `l14b_poncelet_eq`, `l14b_P` (any common point is
`poncelet`); `l14b_mem_iff`, `l14b_ncol` (numeric criteria for the witnesses).

## FINDINGS
* **No Mathlib-only statement turned out false or needed an extra hypothesis** beyond those of the
  paper (`QGen` ⇔ four Mathlib non-collinearities; `d ≠ ortho` ⇔ `d ≠ Tabc.orthocenter`;
  non-cospherical for pedal circles; non-parallel opposite sides for the diagonal circle).
* `ponDen_eq_zero_iff` is about a local polynomial (`ponDen`) that has no Mathlib meaning; it could
  not be restated literally. It was restated by its geometric content:
  "the four Mathlib nine-point circles have a unique common point ⇔ `d ≠ Tabc.orthocenter`". The
  ⇐ direction is the Poncelet theorem; the ⇒ direction (new) uses that in the orthocentric case the
  four circles coincide and contain the distinct midpoints of `ab` and `ac`.
* `poncelet_S4` in the library is six equalities of the local formula under relabelling (the
  formula is undefined/junk in the orthocentric case, see `poncelet_swap_cd_orthocentric`). The
  Mathlib form is a statement about the set `{a,b,c,d}` (every triangle on it, any vertex order),
  which needs no relabelling hypotheses; it is proved under the same hypotheses
  (non-collinear triples, `d ≠ Tabc.orthocenter`). (Mathematical remark, not formalised here: `d ≠ orthocenter(abc)` is symmetric in
  the four points (orthocentricity is a property of the set), so no labelling is privileged.)
* No theorem was skipped; no local notion had to be kept in a statement.

## Mechanical type check (no `QuadMiquel.*` constant in any `l14_` / `l14w_` statement)
Scratch file `scratch/l14_typecheck.lean` (set_option allowed only there): for every `l14_*` and
`l14w_*` theorem it (1) prints `#check @QuadMiquel.<name>` with `pp.fullNames true`,
`pp.notation false`, and (2) walks the elaborated type with `Expr.getUsedConstants` and lists every
constant in namespace `QuadMiquel`. Output `scratch/l14_typecheck.out` (622 lines, 0 errors):
```
TYPECHECK QuadMiquel.l14_triangles_exist: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_ninepoint_concur: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_ninepoint_unique: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_poncelet_on_ninepoint: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_orthocentric_ninePointCircle_eq: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_ponDen_eq_zero_iff: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_poncelet_on_pedal_d: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_poncelet_on_pedal_c: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_poncelet_on_pedal_b: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_poncelet_on_pedal_a: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_poncelet_on_diagonal_circle: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14_poncelet_S4: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_poncelet_on_ninepoint: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_poncelet_on_pedal_d: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_poncelet_on_pedal_c: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_poncelet_on_pedal_b: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_poncelet_on_pedal_a: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_poncelet_on_diagonal_circle: QuadMiquel constants in type = []
TYPECHECK QuadMiquel.l14w_orthocentric: QuadMiquel constants in type = []
```
`grep "QuadMiquel\."` over the printed `#check` types, after dropping each theorem's own name at the
head of its line: **0** occurrences.
(The `l14b_*` bridges deliberately mention local notions; they are not Mathlib-only statements.)

## Gate (`~/lean/jl gate`)
```
'QuadMiquel.l14b_cr_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.l14b_QGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.l14b_tri' depends on axioms: [propext, Classical.choice, Quot.sound]
… (42 lines for l14 declarations, all `[propext, Classical.choice, Quot.sound]`) …
'QuadMiquel.l14w_orthocentric' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (148 declarations, standard axioms only)
```

## Tamper (`~/lean/jl tamper`)
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
| `QuadMiquel/Parallel.lean` | `ea33070625a61685…` | `ea33070625a61685…` | unchanged |
| `QuadMiquel/Quadrangle.lean` | `4116bc5913cb0e4d…` | `4116bc5913cb0e4d…` | unchanged |
| `QuadMiquel/QuadrangleSym.lean` | `471cf9b35bf444ef…` | `471cf9b35bf444ef…` | unchanged |
| `QuadMiquel/Simson.lean` | `69b49c142ec7435e…` | `69b49c142ec7435e…` | unchanged |
| `QuadMiquel.lean` | `e7e20c5ea5d30b00…` | `9c5d840b9f040ea3…` | CHANGED (intended: one appended import) |
| `gate.sh` | `ff54d84da2958597…` | `1b1ca7704a7c04a2…` | CHANGED (intended: REQUIRED line only) |
| `tests/tamper.sh` | `5da507d51bdc4b18…` | `5da507d51bdc4b18…` | unchanged |

Full hashes are in `scratch/l14_sha_before.txt` and `scratch/l14_sha_after.txt`. The original repo
(`~/lean/quadrangle_ext`) was checked at the end to be byte-identical to the before-hashes.
`QuadMiquel.lean` differs from the original only by the appended import line; `gate.sh` only on the
`REQUIRED=` line (no names removed).

## REQUIRED names added (42)
`QuadMiquel.l14b_cr_ne` `QuadMiquel.l14b_QGen` `QuadMiquel.l14b_tri` `QuadMiquel.l14b_orthocenter` `QuadMiquel.l14b_mem_npc` `QuadMiquel.l14b_npc` `QuadMiquel.l14b_foot` `QuadMiquel.l14b_diag` `QuadMiquel.l14b_ne_of_ncol` `QuadMiquel.l14b_ninePointCircle_eq_of_range_eq` `QuadMiquel.l14b_range3` `QuadMiquel.l14b_cosph` `QuadMiquel.l14b_parallel_iff` `QuadMiquel.l14b_range_sub` `QuadMiquel.l14b_tri_cases` `QuadMiquel.l14b_transfer` `QuadMiquel.l14_triangles_exist` `QuadMiquel.l14b_poncelet_mem` `QuadMiquel.l14b_poncelet_eq` `QuadMiquel.l14_ninepoint_concur` `QuadMiquel.l14_ninepoint_unique` `QuadMiquel.l14_poncelet_on_ninepoint` `QuadMiquel.l14_orthocentric_ninePointCircle_eq` `QuadMiquel.l14_ponDen_eq_zero_iff` `QuadMiquel.l14b_P` `QuadMiquel.l14_poncelet_on_pedal_d` `QuadMiquel.l14_poncelet_on_pedal_c` `QuadMiquel.l14_poncelet_on_pedal_b` `QuadMiquel.l14_poncelet_on_pedal_a` `QuadMiquel.l14_poncelet_on_diagonal_circle` `QuadMiquel.l14_poncelet_S4` `QuadMiquel.l14b_mem_iff` `QuadMiquel.l14b_ncol` `QuadMiquel.l14b_npc_center` `QuadMiquel.l14wbQ_master` `QuadMiquel.l14w_poncelet_on_ninepoint` `QuadMiquel.l14w_poncelet_on_pedal_d` `QuadMiquel.l14w_poncelet_on_pedal_c` `QuadMiquel.l14w_poncelet_on_pedal_b` `QuadMiquel.l14w_poncelet_on_pedal_a` `QuadMiquel.l14w_poncelet_on_diagonal_circle` `QuadMiquel.l14w_orthocentric`

## Python pre-checks (`scratch/`)
`l14_check.py` (exact `Fraction` arithmetic over ℚ(i)) + `l14_pick*.py` (witness search);
output in `scratch/l14_python.out`.
