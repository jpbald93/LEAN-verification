# Paper E Layer 15 — Classical-source statement reconstruction

## Deliverables and status

- Local Lean file: `<oc>/tmp/pilotE/l15w/Classical.lean`.
- Identical remote file: `jack:~/reformal/PaperEClassical.lean`.
- Final compiler output: `<oc>/tmp/pilotE/l15w/COMPILE.log`.
- Final compile: **exit 0; 14 `declaration uses 'sorry'` warnings; 0 errors; no other messages**.
- Both files have SHA-256 `8e1e634a8ee183990c7d556a8a0fd2a756eef40eeb31f1ddf92ee35070b59c53`, independently checked after the final compile.
- All 14 theorem declarations end with `:= by sorry`: 12 classical-item statements and 2 construction obligations. These are type-checked statements, not proved theorems.

## Statement list

Names below are in namespace `ClassicalQuadrilateral`.

| Name | Item | Gloss |
|---|---|---|
| `classical_E1_a` | E1 | Three diagonal midpoints are `Collinear ℝ`. |
| `classical_E1_b` | E1 | At least two diagonal midpoints differ. |
| `classical_E2_a` | E2 | Four Mathlib triangle orthocentres are collinear. |
| `classical_E2_b` | E2 | At least two orthocentres differ. |
| `classical_E3_a` | E3 | Each orthocentre has equal power with respect to every pair of the three diameter circles. |
| `classical_E3_b` | E3 | A genuine affine line contains every orthocentre and equals the entire equal-power locus of every distinct pair of diagonal circles. |
| `classical_E4_a` | E4 | Genuine midpoint and orthocentre carrier lines exist and have orthogonal direction spaces. |
| `classical_E5_a` | E5 | There exists a point belonging to all four triangle circumcircles. |
| `classical_E6_a` | E6 | For any point satisfying that common-circle property, it and the four circumcentres are `EuclideanGeometry.Cospherical`. |
| `classical_E7_a` | E7 | For any Miquel point, its four Mathlib perpendicular projections are collinear. |
| `classical_E7_b` | E7 / line noncollapse | For any plane point, at least two of its four perpendicular feet differ; no Miquel hypothesis is needed for this auxiliary assertion. |
| `classical_E8_a` | E8 | For any Miquel point, genuine Simson and orthocentre carrier lines exist and are `AffineSubspace.Parallel`. |

E4 and E8 assert existence of their carrier lines rather than imposing carrier existence as a hypothesis. Noncollapse in E1(b), E2(b), and E7(b) makes those carriers unambiguous.

## Definitions and justification

All definitions below were written for this reconstruction; wrappers use the indicated Mathlib notions rather than alternative geometric formulas.

- `IsLine`: an affine subspace equal to `line[ℝ, a, b]` for two distinct points. Excludes singleton or whole-plane carriers.
- `Configuration`: four pairs of distinct anchor points, pairwise nonparallel represented lines, and no point on any triple of differently labelled lines. The anchors only represent arbitrary lines; they are not extra geometric restrictions.
- `Configuration.carrier`: each anchor pair's Mathlib affine line.
- `Configuration.vertex`: the unique common point of two differently labelled lines, chosen from the construction obligation. No intersection coordinate formula is used.
- `Configuration.diagonalEndpoints`: the three opposite pairs `(01,23)`, `(02,13)`, `(03,12)`.
- `Configuration.diagonalMidpoint`: Mathlib `midpoint ℝ` of each pair.
- `Configuration.triangleVertices`: triangle `i` consists of the three intersections of the three lines other than `i`.
- `Configuration.triangle`: Mathlib `Affine.Triangle ℝ ℂ`, built from these vertices and the affine-independence obligation.
- `Configuration.orthocenter`: wrapper around `Affine.Triangle.orthocenter`.
- `Configuration.circumcircle`: wrapper around `Affine.Simplex.circumsphere`.
- `Configuration.circumcenter`: that circumsphere's `.center`.
- `Configuration.diameterCircle`: Mathlib `EuclideanGeometry.Sphere ℂ` with the diagonal midpoint as center and half the endpoint distance as radius.
- `Configuration.IsMiquelPoint`: membership in every one of the four circumcircles. E5 quantifies existentially over this property; E6–E8 apply to any point satisfying it. No formula or selected Miquel-point constant is introduced.
- `Configuration.foot`: Mathlib `EuclideanGeometry.orthogonalProjection`, converted from its subtype-valued result to a complex point. The line's `Nonempty` instance is obtained by unfolding `carrier` and using instance inference. No homemade projection formula or additional projection hypothesis is needed.
- `power`: `dist p C.center ^ 2 - C.radius ^ 2`, the signed circle power requested in the brief.
- `radicalLocus`: the set of all points with equal power for two circles; the definition does not assume the set is a line.
- `Perpendicular`: every vector in one affine carrier's direction space has zero real inner product with every vector in the other. All theorem uses also assert that both carriers are genuine lines.

The genuinely custom geometric definitions are marked `OWN DEFINITION` in the Lean source. Direct Mathlib wrappers are identified by comments. The geometry is the real Euclidean affine plane on `ℂ` throughout.

## Ambiguities and extra hypotheses

There are exactly two `AMBIGUOUS` marks:

1. E5: “one common point” could mean unique existence (`∃!`). The formalization asserts existence (`∃`), the literal common-point statement. The later statements hold for every point with the defining property. Uniqueness is not asserted or assumed.
2. E8: “parallel” uses Mathlib affine-subspace parallelism, allowing coincident lines. Strict parallelism would additionally require distinctness; it is not asserted or assumed.

There are **no `EXTRA HYPOTHESIS` marks and no added geometric hypotheses**. General position is encoded in `Configuration`; E6–E8 merely identify the point under discussion by its defining incidence property. Construction results are theorem obligations, not fields supplying additional assumptions.

## Construction obligations

- `Configuration.vertex_exists_unique`: distinct nonparallel lines in this plane intersect in a unique point. Needed to define vertices by their incidence property.
- `Configuration.triangle_independent`: each omitted-line vertex triple is `AffineIndependent ℝ`. Needed to construct Mathlib triangles and therefore their orthocentres and circumcircles.

Both are separately declared with `:= by sorry`. E7(b) is a supplementary noncollapse statement for the line named in E8, not an additional hypothesis or a prerequisite for well-formedness.

## Compiler record

Four compilation iterations were completed on jack using the prescribed Mathlib environment and `timeout 900 lake env lean PaperEClassical.lean`, with `yieldMs: 600000` on each compile call. Initial errors concerned computability, the projection's nonempty instance/subtype coercion, and closing the noncomputable section. These were corrected without reading Mathlib source or probing other files. The final run produced exactly 14 sorry warnings and zero errors. No compile is still running. No `lake update` or cache retrieval was performed.

## Files read and blindness disclosure

Explicitly read:

1. `<ws>/AFM/PaperE/layer15/writer_brief.txt` — the mathematical brief.
2. `<ws>/skills/afm-blind-reformalization/SKILL.md` — procedural skill instructions, read because the higher-priority environment mandates reading an applicable skill. **This is an exception to the requested brief-only read boundary and must not be concealed.** It contains procedural instructions, not the Paper E mathematics or its source formalization.
3. `<oc>/tmp/pilotE/l15w/Classical.lean` — my own output, read for revisions and local checksum.
4. `jack:~/reformal/PaperEClassical.lean` — my own remote output, read by the compiler and the final checksum command.
5. `<oc>/tmp/pilotE/l15w/COMPILE.log` — compiler output of my own file.

Earlier compiler diagnostics were read directly as tool output. The report itself was written, not read from a pre-existing source. The compiler necessarily resolves `import Mathlib`; no library source was opened or inspected by the agent. System/developer-injected workspace context was already present, not separately opened.

No other AFM file, paper, original project formalization, repository source, or external mathematical material was read. No web search and no subagent spawning occurred. The mathematical statements were reconstructed from the brief alone, but the procedural skill read means the strict file-access condition was not fully met.
