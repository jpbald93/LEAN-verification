# L13_COMPARE_J — Paper I, quadrilaterals + circle systems (machine: jack)

Date 2026-11-09 (UTC). Toolchain leanprover/lean4:v4.33.1, Mathlib v4.33.1.
Blind file: `Blind.lean` (= `~/reformal/PaperIBlind.lean`). Real statements: `~/l13_quad` (HEAD 12a24a6;
the only change since feafb24 is the added `L14.lean` + import + gate.sh, all statements compared are
byte-identical to feafb24) and `~/l13_circles` (HEAD 2f036ed).

## Files (two, because the two libraries are separate Lake projects and cannot import each other)
- `jackagent@100.72.132.55:~/l13_quad/scratch/L13_compare.lean`  (namespace `L13JQ`, sha256 4c62539e…6c66)
- `jackagent@100.72.132.55:~/l13_circles/scratch/L13_compare.lean` (namespace `L13JC`, sha256 f1cc99dd…0130)
- compiler logs next to each: `scratch/L13_compare_out.txt`. Local copies: `L13_compare_quad.lean`, `L13_compare_circles.lean`.

Method: every blind statement is restated verbatim as a closed `def blindK_stmt : Prop` (blind `def`s copied
verbatim); every real statement is the goal `type_of% @Lib.name.{u,v}`. Proofs use only unfolding of library
*definitions*, repackaging, and Mathlib. Bridges I proved from Mathlib myself: blind cross product = library
`cross`/`areaForm` of `e.toBasis.orientation`; blind rotation = `Orientation.rotation`; blind same-side ↔
`AffineSubspace.SSameSide`; blind convexity ↔ `ConvexQuad`; convex ⇒ four sides non-degenerate; blind foot of
perpendicular ↔ `orthogonalProjection`; reflection = 2·projection − P; pencil-power identity; orthocenter =
A+B+C−2·circumcenter (from Mathlib's Monge point).

## Results

| pair | R→B | B→R | difference (REAL/ARTEFACT) | note |
|---|---|---|---|---|
| thm:bretschneider — blind_1 / `bretschneider` | ✅ `r1_to_b` | ✅ `b1_to_r` | none | `BlindQuadArea` = `quadArea`, semiperimeter equal by `ring` |
| thm:brahmagupta — blind_2 / `brahmagupta` | ✅ `r2_to_b` | ✅ `b2_to_r` | none | |
| thm:pitot — blind_3 / `pitot` | ✅ `r3_to_b` | ✅ `b3_to_r` | none | incircle bridge needs sides ≠, derived from convexity (own ~35-line affine lemma) |
| thm:pitot conv. — blind_4 / `pitot_converse` | ✅ `r4_to_b` | ✅ `b4_to_r` | none | |
| thm:euler4 — blind_5 / `euler_quadrilateral` | ✅ `r5_to_b` | ✅ `b5_to_r` | none | blind carries a (harmless) plane hypothesis, real carries `Fact` |
| thm:ptolemy2 — blind_6 / `ptolemy_second` | ✅ `r6_to_b` | ✅ `b6_to_r` | none | |
| thm:vanaubel — blind_7 ∧ blind_8 / `van_aubel` | ✅ `r78_to_b` | ✅ `b78_to_r` | none | blind uses an ONB `e`, real an `Orientation o`; B→R picks `o.finOrthonormalBasis`, R→B uses `e.toBasis.orientation`; the sign/rotation conventions coincide exactly |
| thm:newton — blind_9 / `newton_line` | ✅ `r9_to_b` | ✅ `b9_to_r` | none | |
| thm:fuss — blind_10 / `fuss` | ✅ `r10_to_b` | ✅ `b10_to_r` | none | |
| thm:radical — blind_43 / `radical_center_concurrent` | ✅ `r43_to_b` | ✅ `b43_to_r` | none | `BlindVectorRadicalAxis` = `radicalAxis` (norm vs dist) |
| thm:coaxal — blind_46 / `pencil_through_common_point` | ✅ `r46_to_b` | ✅ `b46_to_r` | none | blind: pencil power = 0; real: dist² to pencil centre = pencil radius²; linked by a pure inner-product identity |
| thm:johnson — blind_48 / `johnson_circle` | ✅ `r48_to_b` | ✅ `b48_to_r` | none | definitional |
| thm:johnson — blind_49 / `johnson_mem_circles` | ✅ `r49_to_b` | ◐ `b49_to_r_ips` | ARTEFACT | real is stated without `[InnerProductSpace ℝ V]` (any normed group, via `omit`); blind (and the prose, "in any V") is inner-product only. B→R proved for inner product spaces; the extra generality is invisible in prose |
| thm:johnson — blind_48 / `johnson_orthocenter_eq` (circumcentre part) | — | ✅ `b48_to_r_orthocenter_eq` | ARTEFACT | real is a Mathlib-`Affine.Triangle` repackaging (needs plane + affine independence), so it is weaker than blind_48/51 and cannot give them back; blind_48 ⇒ both conjuncts (circumcentre and orthocentre = H) |
| thm:johnson — blind_51 / `johnson_orthocenter` | ✅ `r51_to_b` | ✅ `b51_to_r` | none | blind writes ⟪H−A, C−B⟫, real ⟪A−H, B−C⟫: sign flips cancel |
| thm:johnson — `johnson_reflection`, `johnson_congruent` | ✗ | ✗ | REAL omission (blind side) | no blind statement for the point reflection in M or the congruence △O₁O₂O₃ ≅ △ABC (blind_48–51 cover circle, membership, second intersections, orthocentre only) — not attempted |
| thm:simson — blind_52 / `simson_det_eq_circumcircle_power` | ✅ `r52_to_b` | ✅ `b52_to_r` | none | blind feet given relationally (`BlindPerpendicularFoot`), real as `orthogonalProjection`; proved equivalent |
| thm:simson — blind_53 / `simson_wallace` | ✅ `r53_to_b` | ✅ `b53_to_r` | none | blind has extra A≠B≠C≠A hypotheses; they follow from non-collinearity |
| thm:steinerline — blind_55 / `steiner_line` | ✅ `r55_to_b` | ✅ `b55_to_r` | none | blind writes reflections as 2D−P |
| thm:steinerline — blind_55 / `steiner_line_orthocenter` | ✅ `r55_orthocenter_to_b` | ✅ `b55_to_r_orthocenter` | none | via Mathlib's Monge point: orthocenter = A+B+C−2·circumcenter |

Count: 17 rows with both directions proved (counting van Aubel once and the two Steiner pairs separately); 1 restricted
(blind_49, ARTEFACT); 1 one-direction (johnson_orthocenter_eq, ARTEFACT); 1 not attempted (johnson_reflection /
johnson_congruent: no blind counterpart). No pair shows a misreading of the prose.

## Gate
- Compile: `flock ~/pi.lock … lake env lean scratch/L13_compare.lean` → exit 0 in both repos, 0 errors, 0 warnings.
- `grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|\baxiom "` → no match in either file (grep exit 1).
- `#print axioms` on all 37 comparison theorems → `[propext, Classical.choice, Quot.sound]` only.
- Library-use audit (`#audit_lib`, in-file, walks every proof term of the namespace): `library theorems used: []`
  in both files. The only library constants that occur are compiler-generated pieces of definitions
  (`triArea._proof_1`, `quadSign._proof_1`, `squareCenter._proof_1`, `squareCenter.eq_1`, `cx._proof_1`), i.e.
  unfolding. The audit was checked against a test file: it does flag `CircleSystems.johnson_reflection` and
  `johnson_mem_circles` when they are used. A first version of the audit was vacuous (theorem bodies are not
  returned without `allowOpaque`); this was caught by that test and fixed before the final run.
- `git status --porcelain`: empty in `~/l13_quad` and `~/l13_circles`; `scratch/` is excluded via `.git/info/exclude`.

## Unattempted / out of scope
- `johnson_reflection`, `johnson_congruent`: no blind statement exists (see table).
- Blind statements under these labels that have no real pair in `pairs.txt`, so they were not compared: blind_11
  (Fuss positivity), blind_12 (counterexample), blind_13 (earlier variant), blind_40–42 (radical axis level set /
  direction / dimension), blind_44, 45, 47 (pencil member, radical axis of members, orthogonality), blind_50 (second
  intersections), blind_54 (complex foot formula). The library does have candidates for some of them
  (`radicalAxis_eq_inner`, `radicalAxis_eq_mk'`, `pencilPow_eq_powPt`, `pencil_radicalAxis`, `isOrthogonal_iff`),
  but they are not on my list.
