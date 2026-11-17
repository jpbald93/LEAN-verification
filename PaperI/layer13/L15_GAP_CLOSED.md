# L15 addendum — Bretschneider (Q1) and Brahmagupta (Q2) gap closed (2026-11-09)

The L15 comparison recorded Q1/Q2 as narrower because the classical statements use the Lebesgue
measure of the convex hull while the library's `quadArea` is the three-term formula. That gap is now
proved, not merely noted:

- `~/l13_quad/scratch/area_bridge.lean` (jack, sha256 prefix `f213ef2737be22b1`), compiles rc=0, no
  `sorry`/`admit`/`axiom`/`native_decide`, standard axioms only.
- `Quadrilaterals.AreaBridge.volume_convexHull_triangle`: for all A B C,
  `(volume (convexHull ℝ {A,B,C})).toReal = triArea A B C` (degenerate included).
- `Quadrilaterals.AreaBridge.volume_convexHull_quad`: under `ConvexQuad`,
  `(volume (convexHull ℝ {A,B,C,D})).toReal = quadArea A B C D`.
- `L15Q.classical_Q1`, `L15Q.classical_Q2`: the verbatim classical statements, now proved from the
  library theorems plus the bridge.
- Scope: points in `V` / `EuclideanSpace ℝ (Fin 2)` (Lebesgue measure lives on `V`); the general
  torsor version was not attempted and is not needed for the classical statements.
- Proof route: parallelogram = |u×v|; triangle = half of it (mirror pieces overlap in a line, measure
  zero); quadrilateral = two triangles across the diagonal frame (`convex_frame`, `IsFrame.pos`),
  overlapping only in the line AC.
