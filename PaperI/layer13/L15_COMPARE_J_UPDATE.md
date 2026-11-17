# L15_COMPARE_J — update: Q1 (Bretschneider) and Q2 (Brahmagupta) now **E (covered)**

Date: 2026-11-09 (UTC), machine jack (gmktec, `jackagent@100.72.132.55`), toolchain leanprover/lean4:v4.33.1.

## Verdict change

| Item | Before | Now | Proved as |
|------|--------|-----|-----------|
| Q1 Bretschneider | N (narrower) | **E (covered)** | `L15Q.classical_Q1` (verbatim classical statement) |
| Q2 Brahmagupta   | N (narrower) | **E (covered)** | `L15Q.classical_Q2` (verbatim classical statement) |

The N verdict was due solely to the missing identity
`(volume (convexHull ℝ {A,B,C,D})).toReal = Quadrilaterals.quadArea A B C D`. Lemma used to close it:
**`Quadrilaterals.AreaBridge.volume_convexHull_quad`** (built on
`Quadrilaterals.AreaBridge.volume_convexHull_triangle`), wrapped in the classical vocabulary as
`L15Q.classicalQuadArea_eq : ClassicalConvexQuad A B C D → ClassicalQuadArea A B C D = quadArea A B C D`.
`classical_Q1` = `classicalQuadArea_eq` + `Quadrilaterals.bretschneider`;
`classical_Q2` = `classicalQuadArea_eq` + `Quadrilaterals.brahmagupta` (+ `bretschneider` for the sign of the radicand).
The theorem statements are the verbatim texts that were block-commented as "NARROWER" in `L15_compare.lean`; no hypothesis was added.
Q3–Q8 are unchanged.

## Evidence file

`~/l13_quad/scratch/L15_compare_ext.lean` = copy of `~/l14i_quad/scratch/L15_compare.lean` with
(1) namespace `Quadrilaterals.AreaBridge` from `~/l13_quad/scratch/area_bridge.lean` spliced in verbatim
(own `noncomputable section AreaBridgeSplice` so its `open`s do not leak), (2) `L15Q.classicalQuadArea_eq`
added, (3) the commented Q1/Q2 blocks replaced by the proved `classical_Q1` / `classical_Q2` from
`area_bridge.lean`, (4) `#print axioms` added for the five new theorems. The duplicate `L15Q`
defs in `area_bridge.lean` (`ClassicalConvexQuad`, `ClassicalQuadArea`, `instFactE2`) were not copied, since
`L15_compare.lean` already declares them identically.

sha256(`L15_compare_ext.lean`) = `0a45507ecfb7d2db718b2a3fb341d50c54617a83499fd7671bf748ae6da7c9cf`

Original untouched: sha256(`~/l14i_quad/scratch/L15_compare.lean`) =
`c16c05f7812f4ac09db934756e4416f62ba94fd009c84dfcc205d3bcb452f7d4` (same as before; also the same as
the copy in `~/l13_quad/scratch/`).

## Compile result

```
flock ~/pi.lock bash -c "cd ~/l13_quad && PATH=$HOME/.elan/bin:$PATH lake env lean scratch/L15_compare_ext.lean"
EXIT=0   (no errors, no warnings; ~5 s wall)
```
All 26 `#print axioms` lines report `[propext, Classical.choice, Quot.sound]`, including
`volume_convexHull_triangle`, `volume_convexHull_quad`, `classicalQuadArea_eq`, `classical_Q1`, `classical_Q2`.
`grep -nE "sorry|admit|native_decide"` → no matches; no `axiom` declarations (the only occurrences of
the word are the `#print axioms` lines). Full log: `~/l13_quad/scratch/L15_compare_ext_out.txt`.

## Caveat (unchanged from AREA_BRIDGE_REPORT.md)

The bridge is stated for a 2-dimensional inner-product *vector space* `V` (covers `E2`, which is what
the classical statements use), not a general affine torsor.
