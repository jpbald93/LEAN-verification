# Paper I — job A (jack): Layer 10 bridges, gate/tamper, battery — REPORT (second run)

Host `jack` (`jackagent@100.72.132.55`). All Lean invocations ran under `flock ~/pi.lock`.
No `sorry` / `admit` / `axiom` / `native_decide` in anything added; no existing statement was touched.

## Pre-check (state left by attempt 1)

- `~/final_quad` @ 12a24a6, `~/final_circles` @ 2f036ed, both `git status --porcelain` empty.
- No `*/Bridge.lean` in either repo; `ls ~/leancheck/reports | grep final_` showed no `final_quad_*` / `final_circles_*` report.
- So I did NOT re-run the rsync. Step 1's diff check was already done in attempt 1 and still holds: `HEAD~1..HEAD` = the L14 file + one import line in the root file + the one-line `gate.sh` change, nothing else.

---

## paperi_quad → `~/final_quad`

- **Final commit:** `0c372061edd32cc7935cf1521d404dfbc3993ac5`
- `git log --oneline -3`:
  ```
  0c37206 Layer 10: definition bridges
  12a24a6 Layer 14: Mathlib-only restatements and witnesses
  feafb24 Prove Fuss's relation for bicentric quadrilaterals
  ```
- Author and committer are both `Josh Bald <jpbald93@gmail.com>`. The repo config was not changed and there is no Co-Authored-By trailer.
- **`-0` rule: HELD.** `git diff --numstat HEAD~1 HEAD`:
  ```
  1   0  Quadrilaterals.lean          (+ import Quadrilaterals.Bridge)
  174 0  Quadrilaterals/Bridge.lean
  1   0  gate.sh                      (+ REQUIRED="$REQUIRED <15 new names>")
  ```
  Removed lines: 0.
- **Gate PASS line:** `PASS (133 declarations, standard axioms only)` (it was 118 before; +15).
- **Tamper:** 11 of 11 rejected. The script prints one `ok … rejected` line per test (sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp2, falsehyp3, falsestmt, fusshyp, fussstmt) and then `ALL TAMPERING TESTS REJECTED`. The battery verdict line for it is `11/11 planted defects rejected, ALL TAMPERING TESTS REJECTED`.
- **git status:** `On branch master, nothing to commit, working tree clean`.
- **Battery report:** `/home/jackagent/leancheck/reports/final_quad_20261110_180030.md` (ran 18:00–19:22 UTC, WORKERS=8)

  | thms | mutants | rejected | survived | contr | sat |
  |---|---|---|---|---|---|
  | 118 | 273 | 272 (0 by timeout) | 1 | 0 | 35/118 certified (80 unresolved, 3 stmt-invalid) |

  Other verdict rows:
  - Gate: PASS (133).
  - Tamper: 11/11.
  - Baseline build: 10/10 files.
  - Ablation: 131 needed, 1 unused (`fuss_opposite (hr : 0 < r)`, already present before this layer).
  - Library linter: 0 warnings in 10 files.
  - Scratch linter: 0 warnings, but a nonzero exit on `scratch/P.lean` (already present before this layer).
  - Layer 9: 7 notions, 3 has-bridge, 4 NO-BRIDGE.

  The one survivor is `l14w_fuss` [lit0->1@185], the Layer-14 witness: `0 < r` mutated to `1 < r`. The witness has r = 24/7, so the mutated statement is still true and still proved. This is a benign survivor in an existential witness, not in a theorem or in Bridge.lean.
- **Bridge lemmas proved (15), `Quadrilaterals/Bridge.lean`:**
  - `cross_eq_det`: `cross b u v = b.toBasis.det ![u, v]`
  - `cross_eq_areaForm`: `cross b u v = b.toBasis.orientation.areaForm u v`
  - `abs_cross_eq_abs_areaForm`: `|cross b u v| = |o.areaForm u v|` for any orientation `o`
  - `cx_eq_repr`, `cy_eq_repr`: `cx b v = b.repr v 0`, `cy b v = b.repr v 1`
  - `triArea_eq_areaForm`: `triArea A B C = |ω(B−A, C−A)| / 2` (shoelace)
  - `quadArea_eq_areaForm`: `quadArea` is the sum of the two shoelace triangle areas
  - `ConvexQuad.quadArea_eq_areaForm`: for convex ABCD, `quadArea = |ω(C−A, D−B)| / 2`
  - `convexQuad_iff_sOppSide`: `ConvexQuad A B C D ↔ line[A,C].SOppSide B D ∧ line[B,D].SOppSide A C`
  - `ConvexQuad.quadSign_eq_sign`: for convex ABCD, `quadSign o … = Real.sign (ω(C−A, D−B))`
  - `cospherical_iff_concyclic`: in the plane, `Cospherical s ↔ Concyclic s`
  - `cospherical_four_iff_exists_sphere`: `Cospherical {A,B,C,D} ↔ ∃ s : Sphere P, A,B,C,D ∈ s`
  - `infDist_eq_iff_isTangent`: `infDist I line[X,Y] = r ↔ (⟨I,r⟩ : Sphere P).IsTangent line[X,Y]`
  - `isIncircle_iff_isTangent`: `IsIncircle` restated with `Sphere.IsTangent` on the four side lines
  - `tangential_iff_exists_sphere`: `Tangential ↔ ∃ s : Sphere P, …` (tangent to all four sides, centre inside)
- **Dropped as gaps:** none of the attempted candidates.
  - Not applicable: "`powPt` vs `dist X O ^ 2 − R ^ 2`". paperi_quad defines no `powPt`; the power appears only as a real variable `p` in `FussAlg`/`Fuss`.
  - Not targeted: `IsFrame`, `px`, `py`, `swapBasis`. These are proof-internal coordinate devices with no standard counterpart the paper leans on, so they remain NO-BRIDGE in layer 9 (see Deviations, item 3).
- **sha256 `Quadrilaterals/Bridge.lean`:** `e9b402bd43dbb129b61fe39c9780f9512d842295b0b7be5d239e046a287a992c`

---

## paperi_circles → `~/final_circles`

- **Final commit:** `6c714e57d5cf41a43838d2a0e380fdc028e9b15b`
- `git log --oneline -3`:
  ```
  6c714e5 Layer 10: definition bridges
  2f036ed Layer 14: Mathlib-only restatements and witnesses
  f3c7991 CircleSystems: power of a point, radical center, coaxal pencils, Johnson, Simson-Steiner
  ```
- Author and committer are both `Josh Bald <jpbald93@gmail.com>`, with no trailer.
- **`-0` rule: HELD.**
  ```
  1   0  CircleSystems.lean           (+ import CircleSystems.Bridge)
  115 0  CircleSystems/Bridge.lean
  1   0  gate.sh                      (+ REQUIRED="$REQUIRED <15 new names>")
  ```
  Removed lines: 0.
- **Gate PASS line:** `PASS (121 declarations, standard axioms only)` (it was 106 before; +15).
- **Tamper:** 9 of 9 rejected (sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp2, falsehyp3, falsestmt), then `ALL TAMPERING TESTS REJECTED`. The battery verdict line is `9/9 planted defects rejected, ALL TAMPERING TESTS REJECTED`.
- **git status:** `On branch master, nothing to commit, working tree clean`.
- **Battery report:** `/home/jackagent/leancheck/reports/final_circles_20261110_192246.md` (ran 19:22–20:14 UTC, WORKERS=8)

  | thms | mutants | rejected | survived | contr | sat |
  |---|---|---|---|---|---|
  | 110 | 298 | 292 (285 by error, 7 by timeout/heartbeat) | 6 | 0 | 47/110 certified (63 unresolved, 0 stmt-invalid) |

  Other verdict rows:
  - Gate: PASS (121).
  - Tamper: 9/9.
  - Baseline build: 7/7 files.
  - Ablation: 143 needed, 6 unused (the `_hF*`/`_hE*`/`_hD*` hypotheses of `steiner_alg_*`, the same as in the pre-existing paperi_circles report).
  - Linters: 0 warnings.
  - Layer 9: 11 notions, 4 has-bridge, 7 NO-BRIDGE.

  All 6 survivors are in Layer-14 witnesses (`l14w_*`), none in Bridge.lean or in a theorem:
  - `l14w_radical_center_concurrent` [lit2->3@114]
  - `l14w_isOrthogonal_iff` [lit0->1@34] and [lit0->1@43]
  - `l14w_johnson_circle` [lit0->1@81] and [lit2->3@183] (for both, the report says "own proof compiled; downstream errors at line 235")
  - `l14w_steiner_line` [lit2->3@141]

  These are literal changes inside concrete existential witnesses. They need hand classification but are expected to be benign, of the same kind as the quad survivor.
- **Bridge lemmas proved (15), `CircleSystems/Bridge.lean`:**
  - `powPt_eq_power`: `powPt P O R = (⟨O, R⟩ : Sphere V).power P`. This is `rfl`, which the brief allows because the two are literally the same expression `dist P O ^ 2 − R ^ 2`.
  - `powPt_eq_zero_iff_mem_sphere`: for `0 ≤ R`, `powPt P O R = 0 ↔ P ∈ ⟨O, R⟩`
  - `mul_dist_eq_abs_powPt`: the chord form `PX · PY = |powPt P O R|`, via `Sphere.mul_dist_eq_abs_power`
  - `mem_radicalAxis_iff_power`: `P ∈ radicalAxis … ↔ s₁.power P = s₂.power P`. This is `Iff.rfl`, again because the two are literally the same.
  - `sphere_inter_subset_radicalAxis`: `(s₁ : Set V) ∩ s₂ ⊆ radicalAxis s₁.center s₁.radius s₂.center s₂.radius`
  - `radicalAxis_eq_affineSubspace`: for `O₁ ≠ O₂` the radical axis is an `AffineSubspace` with direction `(ℝ ∙ (O₁ − O₂))ᗮ`
  - `pencilCenter_eq_lineMap`: `pencilCenter O₁ O₂ t = AffineMap.lineMap O₁ O₂ t`
  - `isOrthogonal_iff_angle`: `IsOrthogonal ↔ ∃ X ∈ both Spheres, ∠ O₁ X O₂ = π/2`
  - `reflection_eq_pointReflection`: `reflection line[X,Y] P = Equiv.pointReflection (orthogonalProjection … P) P`
  - `johnson_center_eq_pointReflection`: the Johnson centre `O₁+O₂+O₃−2H` is the point reflection of `H` in `M = (O₁+O₂+O₃−H)/2`
  - `johnson_center_eq_orthocenter`: for an `Affine.Triangle`, `A+B+C−2·circumcenter = Triangle.orthocenter`
  - `cx_eq_repr`, `cy_eq_repr`, `cross_eq_det`, `cross_eq_areaForm`: same as in quad
- **Dropped as gaps:** none. The brief's candidates (powPt, radical axis/coaxal, Johnson vs reflected centre, orthocentre/reflection vs Mathlib) are all covered.
  - Coaxal: there is no separate "coaxal" predicate in the repo. The pencil is tied to Mathlib through `pencilCenter_eq_lineMap`, and its radical axis through `mem_radicalAxis_iff_power` together with the existing `pencil_radicalAxis`.
  - Not separately bridged: `pencilPow`, `pencilRadSq`, `radConst`, `radBase`. These are auxiliary; `pencilPow` already has `pencilPow_eq_powPt`, and that now chains to `Sphere.power`.
- **sha256 `CircleSystems/Bridge.lean`:** `3e21b055d4b6640b582279c0477130a994b6eb4cacefe24b57979a4bc5d030b4`

---

## Deviations / notes

1. **How `gate.sh` was extended.** The brief says to add the names to `REQUIRED`. To keep `-0` lines, I did not edit the existing `REQUIRED="…"` line. Instead I added one line directly after it: `REQUIRED="$REQUIRED <names>"`. The gate expands this exactly as if the names were in the original list, which is why the counts rose by 15. `tests/tamper.sh`'s `wrap` test rewrites only the first `REQUIRED="`, so it still works, as the tamper results show.
2. **Bridge.lean imports** are `Quadrilaterals.Frame` + `Quadrilaterals.Bridges` for quad, and `CircleSystems.{Coaxal,Johnson,SimsonSteiner}` for circles. The root file got exactly one new import line in each repo.
3. **The layer-9 inventory counts did not move:** quad is still 3/7 has-bridge and circles still 4/11. The heuristic (`gapcheck.py`) only credits a lemma whose first declaration line names the notion and matches its name pattern. It also does not list the `Basic.lean` notions of quad at all (`ConvexQuad`, `IsIncircle`, `Tangential`, `triArea`, `quadArea`, `quadSign`). Several new bridges therefore exist but are not detected (for example `mem_radicalAxis_iff_power`, `isOrthogonal_iff_angle`, `pencilCenter_eq_lineMap`, and all the quad `Basic.lean` bridges).
   - What it did pick up: `cx_eq_repr` and `cy_eq_repr` in both repos, and `powPt_eq_power` in circles.
   - Remaining NO-BRIDGE rows: quad `IsFrame`, `px`, `py`, `swapBasis`; circles `pencilPow`, `pencilCenter`, `pencilRadSq`, `IsOrthogonal`, `radicalAxis`, `radConst`, `radBase`.
   - For the review, the authoritative list of bridges is the one above. Of the NO-BRIDGE rows, `pencilCenter`, `IsOrthogonal` and `radicalAxis` are real heuristic misses, since Bridge.lean bridges them. The others are the auxiliary or proof-internal defs listed in the per-repo "not targeted / not separately bridged" lines; I did not bridge those and record them as declared gaps.
4. **Battery:** run sequentially by one driver script (`~/final_battery.sh`, log `~/final_battery.log`), with `WORKERS=8` and each `runall.sh` under `flock ~/pi.lock`. Both runs finished with rc=0.
5. **Pre-existing items, not introduced by this layer:**
   - Quad: `fuss_opposite`'s unused `hr` and `scratch/P.lean`'s nonzero linter exit.
   - Circles: the six unused `steiner_alg_*` hypotheses.
6. **Time:** the bridge work for both repos took well under the 150-minute cap, so no partial-commit fallback was needed.

## Headline lines

- final_quad:
  - Gate: `PASS (133 declarations, standard axioms only)`
  - Tamper: 11 of 11 rejected
  - Battery: `/home/jackagent/leancheck/reports/final_quad_20261110_180030.md`
- final_circles:
  - Gate: `PASS (121 declarations, standard axioms only)`
  - Tamper: 9 of 9 rejected
  - Battery: `/home/jackagent/leancheck/reports/final_circles_20261110_192246.md`
