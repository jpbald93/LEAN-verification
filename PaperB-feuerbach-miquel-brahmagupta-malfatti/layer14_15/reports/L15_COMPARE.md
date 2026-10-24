# PAPER B — LAYER 15 CLASSICAL COMPARER (final)
Machine: jack (jack). All work inline, no sub-agents. Every `lake env lean` and gate run was wrapped in `flock ~/l15jack.lock`.
Wall time: 02:32 → 03:16 EDT, 2026-10-22 (≈45 min).

## Sources
| repo | pinned commit (paper §Availability) | fresh clone | Mathlib rev | packages |
|---|---|---|---|---|
| feuerbach | 2bf41901548aed8b0e43d2f1bd10bb1a1d54ebf8 | ~/l15B_feuerbach (HEAD = pin) | 0df444a360eaa60ab8c11dca51a86af692955474 | symlink ~/barbier/.lake/packages |
| miquel | 401de13c0c4e51f67f87f7252f147048084c4a01 | ~/l15B_miquel | 0df444a3… | symlink |
| brahmagupta | c5c3ce014dc450ca212df76fade8948aa45421e0 | ~/l15B_brahmagupta | 0df444a3… | symlink |
| malfatti | d39519346e71c9af8c349490a4dac5388de4d8f2 | ~/l15B_malfatti | 0df444a3… | symlink |

Gate (`./gate.sh`, fresh clones; logs ~/l15B_gate_<repo>.log):
- feuerbach: `PASS (46 declarations, standard axioms only)`, rc=0
- brahmagupta: `PASS (30 declarations, standard axioms only)`, rc=0
- malfatti: `PASS (77 declarations, standard axioms only)`, rc=0
- miquel: `PASS (84 declarations, standard axioms only)`, rc=0

Writer inputs: /tmp/blindB/Classical.lean (19 statements), /tmp/blindB/CLASSICAL_REPORT.md, /tmp/blindB/classical_statements.txt.
Scratch files: the writer's definitions and statements are copied verbatim, each packaged as `def classical_X : Prop := ∀ …, <statement>`.

## Classification table
| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| B1_a | **E** | `cov_B1_a` | — | = `Feuerbach.isIntTangent_insphere_ninePointCircle` |
| B1_a_dist | **E** | `cov_B1_a_dist` | — | = `Feuerbach.dist_ninePointCircle_center_incenter` |
| B1_b_obligation | **E** (Mathlib) | `cov_B1_b_obligation` | — | Mathlib `Affine.Simplex.excenterExists_singleton`; no repository theorem needed |
| B1_b | **E** | `cov_B1_b` | — | `Feuerbach.isExtTangent_exsphere_ninePointCircle` + `IsExtTangent.symm` (the writer puts the arguments in the opposite order) |
| B1_b_dist | **E** | `cov_B1_b_dist` | — | = `Feuerbach.dist_ninePointCircle_center_excenter` |
| B1_remark_equilateral | **O → E (NEW PROOF)** | `cov_B1_remark_equilateral` | — | The paper does not state it. Proved via the new lemma `l15_equilateral_iff` (equilateral ↔ R = 2r), using the repository's Euler formula, tangent lengths re-derived from Mathlib, and `eq_circumcenter_of_dist_eq` |
| B1_remark_unique | **O → E (NEW PROOF)** | `cov_B1_remark_unique` | — | The paper does not state it. When the triangle is not equilateral, NI = R/2 − r > 0, so the tangency point is fixed by I = lineMap N p (NI/(R/2)) |
| B2_a | **E** | `cov_B2_a` | — | Open sides are a special case of B2_b |
| B2_b | **E** | `cov_B2_b` | — | `Miquel.miquel_concyclic` transported from E2 to ℂ by the Mathlib isometry `Complex.orthonormalBasisOneI.repr.symm`; membership in a side line gives the repository's `n,t,u` parameters; distinctness from the vertices gives `n,t,u ∉ {0,1}`; the repository's centres give `Cospherical` |
| B2_obligation | **E (NEW PROOF from repo pieces)** | `cov_B2_obligation` | — | `Miquel.bridge` (al1/al2/al3 factorisations) + `Miquel.Dp_eq_zero_iff_collinear`. The paper states non-collinearity only in prose; it is used inside `miquel_concyclic` but not exported |
| B3_obligation | **E** (Mathlib) | `cov_B3_obligation` | — | A finite convex hull is compact, so its measure is finite |
| B3_a | **N** | `cov_B3_a_part` (shoelace area), `cov_B3_a_of_bridge` | `AreaBridge`: on `IsConvexQuad`, Lebesgue measure of `convexHull {A,B,C,D}` = `Brahmagupta.area` (shoelace) | The paper is narrower: it says itself (§limits) that its K is the shoelace value, not identified with Lebesgue measure. Same hypotheses otherwise (Cospherical + crossing diagonals by Sbtw) |
| B3_b | **N** | `cov_B3_b_part`, `cov_B3_b_of_bridge` | `AreaBridge` | from `Brahmagupta.brahmagupta_sq` + `ring` |
| B3_remark_bretschneider | **O/N (NEW PROOF for shoelace area)** | `cov_B3_remark_bretschneider_part`, `cov_B3_remark_bretschneider_of_bridge` | `AreaBridge` | The paper has only the diagonal form `sixteen_area_sq`. New: the angle form with cos²((∠DAB+∠BCD)/2), for every `IsConvexQuad`. Key step: the convexity hypothesis gives `c1·c2 = l(1−l)k² ≥ 0` for the cross products at A and C (a `linear_combination` certificate) |
| B3_remark_cyclic_iff | **D** (writer mis-stated; FALSE as written) | `cov_B3_remark_cyclic_iff_false : ¬ classical_B3_remark_cyclic_iff`; `cov_B3_remark_cyclic_iff_part` (⇒ direction, NEW PROOF) | the writer's `IsConvexQuad` lets the four points be collinear | Counterexample: A=(0,0), B=(2,0), C=(1,0), D=(1/4,0), X=(1/2,0). Sbtw A X C and Sbtw B X D hold, ∠DAB = 0, ∠BCD = π, so the sum is π, but three distinct collinear points are not cospherical. The textbook assumes a genuine (non-degenerate) quadrilateral. Proved: cyclic ∧ consecutive vertices distinct ⇒ ∠A+∠C = π (Bretschneider + `brahmagupta_sq` + `injOn_cos`). The ⇐ direction under non-collinearity was not attempted |
| B4_a | **E (with NEW PROOF of containment)** | `cov_B4_a` | — | `malfattiCircle`, radius_pos, tangent_side, isExtTangent come from the repository. Containment (closed disc ⊆ convexHull {A,B,C}) is the part the paper says it does not prove (§limits). Here it is NEW: `l15_closedBall_incenter_subset` (incircle disc ⊆ closedInterior, via `signedInfDist`), then `l15_malfatti_subset` (the Malfatti disc is the homothety image of the incircle disc from vertex i with ratio μ ∈ (0,1), by `ratio_pos`/`ratio_lt_one`, and the triangle is convex) |
| B4_a_unique | **O** (not proved) | — | the whole uniqueness argument | The paper explicitly does not claim uniqueness (§limits). Classically true; not cheap (needs: tangent to both sides and inside the triangle ⇒ centre on the bisector, then monotonicity in the three ratios). Left open |
| B4_b_obligation | **E** | `cov_B4_b_obligation` | — | s − a = tl(A) > 0 from `Malfatti.side_eq`, `Malfatti.tl_pos` |
| B4_b | **N** | `cov_B4_b_part` (∃ a Malfatti triple, writer's definition, whose radii satisfy the formula), `cov_B4_b_of_unique` (classical_B4_a_unique → classical_B4_b) | B4_a_unique | The writer quantifies over every Malfatti triple; the repository proves the formula for its own circles. Without uniqueness this is ∃ versus ∀ |

Totals over the 19 writer statements: E 12 (two of them through Mathlib only), N 3 (B3_a, B3_b, B4_b), O/N 1 (Bretschneider), D 1 (B3_remark_cyclic_iff), O 1 (B4_a_unique, unproved).

## NEW PROOFS (not in the repositories)
1. `l15_equilateral_iff`, `cov_B1_remark_equilateral`, `cov_B1_remark_unique`: the Feuerbach remark.
2. `cov_B2_obligation`: non-collinearity of the three Miquel triples (side-line version), for points of E2.
3. `l15_bretschneider_shoelace`: the angle form of Bretschneider's formula for convex quadrilaterals (shoelace area).
4. `cov_B3_remark_cyclic_iff_false` (counterexample) and `cov_B3_remark_cyclic_iff_part` (forward direction).
5. `l15_closedBall_incenter_subset`, `l15_malfatti_subset`: each Malfatti disc lies in the closed triangle. This closes the containment gap that the paper names in §limits.

## Construction obligations
- B1_b_obligation, B3_obligation: proved (from Mathlib).
- B2_obligation, B4_b_obligation: proved (from repository lemmas).
- Explicit hypotheses carried, never sorried: `AreaBridge` (B3_a, B3_b, Bretschneider) and `classical_B4_a_unique` (B4_b).

## Compile and checks
Final runs: `flock ~/l15jack.lock lake env lean scratch/L15_compare.lean` in each clone; outputs in ~/l15B_final_<repo>.out.
| repo | rc | errors | `declaration uses sorry` |
|---|---|---|---|
| feuerbach | 0 | 0 | 0 |
| miquel | 0 | 0 | 0 |
| brahmagupta | 0 | 0 | 0 |
| malfatti | 0 | 0 | 0 |
Only linter warnings remain (unused binder names in the verbatim statements, style lints).

Forbidden grep (`sorry|admit|native_decide|axiom`) over each scratch/L15_compare.lean: 0 matches in all four.

`#print axioms`: every printed theorem depends on `[propext, Classical.choice, Quot.sound]`:
cov_B1_a, cov_B1_a_dist, cov_B1_b_obligation, cov_B1_b, cov_B1_b_dist, cov_B1_remark_equilateral, cov_B1_remark_unique; cov_B2_a, cov_B2_b, cov_B2_obligation; cov_B3_obligation, cov_B3_a_part, cov_B3_b_part, cov_B3_a_of_bridge, cov_B3_b_of_bridge, cov_B3_remark_bretschneider_part, cov_B3_remark_bretschneider_of_bridge, cov_B3_remark_cyclic_iff_false, cov_B3_remark_cyclic_iff_part; l15_closedBall_incenter_subset, cov_B4_a, cov_B4_b_obligation, cov_B4_b_part, cov_B4_b_of_unique.

## Library hashes (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs sha256sum | sha256sum`)
| repo | before | after |
|---|---|---|
| feuerbach | b73ebe8cdf97f6c41e5525ed42d420c51c2a5d9eed712f89f1319b4a9fe25338 | identical |
| miquel | 9f4ef99d9b28ac21c5a4ecff595e4908532f869e2d2c71ea6266b9a66f54d9d7 | identical |
| brahmagupta | 3fb979d8d5e5d0eb03da113a93fe33ea7e62c379dcad92f64e71ad633ad63aa7 | identical |
| malfatti | eb2c2794c7461e8b1c3c016217d73dd4fed64e77635ba58416447f059dda5d5d | identical |
`git status` in each clone shows only `?? scratch/`. No library file was edited, and there was no lake update or cache get.

## Scratch paths (sha256)
- jack:~/l15B_feuerbach/scratch/L15_compare.lean — d305e84cd549dfb1832c8f604ed344a264a15eee873331e49f54394da822f877
- jack:~/l15B_miquel/scratch/L15_compare.lean — aef82a75b82a70d7413a1813649d461abd689e98ada6c626ebbb6330cf35cf48
- jack:~/l15B_brahmagupta/scratch/L15_compare.lean — fe973da0d64a6691e215fd2f663cb7b8c0fc15b49c9b3de9267217b3aa3a0520
- jack:~/l15B_malfatti/scratch/L15_compare.lean — 4182d3588f58ede263fcdb8d783b9ddd7a50113c6f5e726d96ef73fb966a6ffc
- Local copies (same hashes): <ws>/AFM/L14L15/B/L15_scratch/<repo>_L15_compare.lean

## Remarks on the writer versus the paper
- The writer adds no hypotheses that the repositories lack. Where the repositories are more general (Feuerbach in any inner-product space; Miquel needing only non-degeneracy), the writer's statements are special cases.
- Real gaps between the paper and the classical statements: (i) Brahmagupta's area is the shoelace value, not Lebesgue measure; (ii) Malfatti uniqueness is not proved, so the radius formula is ∃ rather than ∀. Containment (iii), which the paper lists as unproved, is now closed in the scratch.
- B3_remark_cyclic_iff is a writer error: the writer's own definition of convexity admits degenerate collinear configurations.
