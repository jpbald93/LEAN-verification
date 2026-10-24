# L15_COMPARE_A — Paper F, Setting A (complete quadrilateral / inscribed parabola)

Repo: `john:~/lean/l15_parabola`. Classical source: `~/lean/PaperFClassical.lean`
(sha256 `afe16593f65ef05be32ba0cab87257fb82b0c76509eca6930fc2095d68441062`, prefix `afe16593f65ef05b` ✔).
Scratch file: `scratch/L15_compare.lean` (sha256 `95b58ca5f140b251…`, 1131 lines), output `scratch/L15_compare.out`.
Namespace `L15A`. Definitions (`Point` … `Quadrilateral.triangleVertices`, `Quadrilateral.triangle` … `IsInscribedFocusDirectrix`) are
copied **verbatim** (checked by script: both copied blocks are byte-identical substrings of the classical file). The 12
classical statements were also copied verbatim (script-checked) as `L15A.classical_*` and each is proved by
`exact cov_classical_* …`.

## Result: all 12 assigned statements are proved in full (8 E, 4 O-proved), with no extra hypotheses

| classical statement | E/N/D/O | Lean theorem(s) proving it | what is missing | note |
|---|---|---|---|---|
| C1 `∃! M, IsMiquelPoint Q M` | **E** | `cov_classical_C1` (from `l14_miquel_existsUnique`) | nothing | classical triangles have the same vertex *sets* as the l14 triangles (`l15_range_tv`); circumspheres compared via `circumsphere_unique_dist_eq` |
| C2 orthocentres on a genuine line | **E** | `cov_classical_C2` (`orthoLine_eq`, `simson_dir_ne`, `orthocentres_collinear'`) | nothing | the line is the repository `orthoLine` |
| C3 reflections of `M` lie on every orthocentre line, collinear | **E** | `cov_classical_C3` (`reflPt_mem_orthoLine`, `reflections_collinear`, `l14b_reflection`) | nothing | `l15_orthoLine_unique`: *any* `L` with `IsOrthocentreLine Q L` equals `orthoLine` (finrank 1 + ≤) |
| C4_a ∃ inscribed parabola, focus Miquel, directrix orthocentre line | **E** | `cov_classical_C4_a` (`l15_inscribed`, `l15_lines_not_parallel_axis`) | nothing | **KNOWN POINT settled** — see NEW PROOFS 1–2: the four lines are *not parallel to the axis*, so classical tangency holds in full |
| C4_b ∃! focus/directrix data | **E** | `cov_classical_C4_b` (existence `cov_classical_C4_b_part`; uniqueness via `cov_classical_C6_b` + `l15_inscribed_directrix`) | nothing | uniqueness is **not in the repository** (the paper's `lambert` docstring says it does not assert uniqueness); NEW PROOF here |
| C4_c `M ∉ L` | **E** | `cov_classical_C4_c` (`miquel_not_mem_orthoLine`) | nothing | |
| C5_a axis ⟂ directrix (any parabola) | **O** (proved) | `cov_classical_C5_a` | — | general parabola fact; repo has only `axis_perp` for its own parabola |
| C5_b Newton–Gauss line ∥ axis, for **any** inscribed parabola | **E** | `cov_classical_C5_b` (`newton_perp_cr` + `l15_inscribed_directrix`); `cov_classical_C5_b_part` (assuming the directrix is the orthocentre line) | nothing | repository proves Newton ⟂ orthoLine only for its own parabola; extension to every inscribed `P` uses NEW uniqueness |
| C6_a parabola tangent to the 3 side lines ⇒ focus on circumcircle (any triangle, any parabola) | **O** (proved, NEW PROOF) | `cov_classical_C6_a` (`l15_tangent_refl`, `l15_c6_alg`) | — | not claimed by the paper (it only treats its own parabola) |
| C6_b any inscribed parabola has focus = Miquel point | **E** | `cov_classical_C6_b` (from C6_a and `l15_side_eq`); weaker `cov_classical_C6_b_part` (repo's parabola only) | nothing | the repository alone only gives `_part`; the "every inscribed parabola" content is NEW |
| C7_a vertex on axis, on locus, midpoint, distances | **O/E** (proved) | `cov_classical_C7_a` | — | general parabola; repo's `vertex_*`/`l14_vertex` are the special case |
| C7_b vertex = unique nearest point to directrix | **O/E** (proved) | `cov_classical_C7_b` (uniqueness from repo's `l14b_nearest_unique`) | — | |

So: 8 E (C1, C2, C3, C4_a, C4_b, C4_c, C5_b, C6_b) and 4 O-proved (C5_a, C6_a, C7_a, C7_b). **No D.**
Strictly, what the *repository alone* proves is narrower for C4_b (no uniqueness), C5_b and C6_b (only for the repository's own
parabola) and for C4_a's tangency notion (no non-parallel-to-axis clause); all of these gaps were closed here by NEW PROOFS.

## NEW PROOFS (all in `scratch/L15_compare.lean`)
1. `l15_not_parallel_axis` — for any classical `Parabola`, a line `line[p,q]` with `⟪dir(directrix), q−p⟫ ≠ 0` is not
   parallel to the axis (the axis direction `F − foot F` is orthogonal to the directrix).
2. `l15_lines_not_parallel_axis` — **KNOWN POINT**: each of the four lines is not parallel to the axis of the
   repository's parabola. Follows from the repository's `line_not_perp` (`Re(conj W · L.d) ≠ 0`, the very denominator of
   `perpMeet`). `l15_inscribed : Inscribed Q Q.parabola` = full classical tangency (IsLine ∧ ¬∥axis ∧ ∃!).
   Settled: **yes, all four lines are non-parallel to the axis.**
3. `l15_tangent_refl` — classical tangency (∃! common point **and** not parallel to the axis) ⇒ the reflection of the
   focus in the line lies on the directrix. Proof: line parameter `t`, the locus condition is a real quadratic with
   leading coefficient `(d·W)² ≠ 0` (non-parallel), a unique root forces discriminant 0, and the discriminant factors as
   `4|W|²·cr(W,F−h)·cr(W,R−h)` (factorisation checked in sympy, then in Lean by `linear_combination`); `F ∉` directrix kills
   the first factor. **The ¬∥axis clause is essential**: a line parallel to the axis also has exactly one common point but
   the reflection is off the directrix — under the repository's weaker `Tangent` (∃! only) the step fails, and C6_a would be false (informal remark; no Lean counterexample was built).
4. `cov_classical_C6_a` — the three reflections lie on the directrix, hence are collinear; the identity
   `n₀n₁n₂·cross(R₁−R₀,R₂−R₀) = −4·D²·Π(F)` (`l15_c6_alg`, `field_simp; ring`; Π = D·power of F w.r.t. circumcircle)
   gives F on the circumcircle; transferred to Mathlib's circumsphere via the repo's `circ_eq_circumcenter`/`l14b_circumcenter`.
5. `l15_inscribed_directrix` — for every inscribed parabola, directrix = `orthoLine` (two distinct reflections of the
   Miquel point lie on both lines; distinctness from `miquelPt_ne_vertices` + `eq_meet_of_foot_eq`).
6. `cov_classical_C4_b` (uniqueness), `cov_classical_C5_b`, `cov_classical_C6_b` for every inscribed parabola.
7. General parabola facts: `cov_classical_C5_a`, `cov_classical_C7_a`, `cov_classical_C7_b`.

## Construction obligations
* `quadrilateral_triangle_independent` — **PROVED** (verbatim statement, `L15A.quadrilateral_triangle_independent`) from
  no-parallel / no-three-concurrent via `l14_triangles_exist` (the classical `Q.meet` = Mathlib `Classical.epsilon`
  intersection is shown to be the unique common point, `l15_meet_spec`, `l15_meet_eq`). Not a hypothesis, not a sorry.
* `diagonal_triangle_independent` — Setting B only; not used, not copied.

## Compile / checks
* `cd ~/lean/l15_parabola && ~/lean/jl lake env lean scratch/L15_compare.lean` → **exit 0**, no errors, no warnings
  (output: only the `#print axioms` lines).
* Forbidden-token grep `grep -nwE "sorry|admit|native_decide|axiom" scratch/L15_compare.lean` → no matches (exit 1);
  no `sorryAx` in output.
* `#print axioms`: every one of `cov_classical_{C1,C2,C3,C4_a,C4_b,C4_c,C5_a,C5_b,C6_a,C6_b,C7_a,C7_b}`, the verbatim
  `classical_*` (12), `quadrilateral_triangle_independent`, `cov_classical_C4_b_part`, `cov_classical_C5_b_part`,
  `cov_classical_C6_b_part`, `l15_lines_not_parallel_axis`, `l15_inscribed`, `l15_tangent_refl`,
  `l15_inscribed_directrix`, `l15_not_parallel_axis` → `[propext, Classical.choice, Quot.sound]`.
* Library hash (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`):
  before `33aaf8530a5152fa7ce5de5141156c5794984b9764bd1a40764a2d2d4b1f55af`, after
  `33aaf8530a5152fa7ce5de5141156c5794984b9764bd1a40764a2d2d4b1f55af` — **unchanged**. No library file edited; no
  `lake update` / cache get.

## Scratch paths
* `john:~/lean/l15_parabola/scratch/L15_compare.lean` (all proofs)
* `john:~/lean/l15_parabola/scratch/L15_compare.out` (compiler output / axioms)
* `john:~/lean/l15_parabola/L15_COMPARE_A.md` (this report)
