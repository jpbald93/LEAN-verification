# REPORT — Paper G, Group A: The Nagel line family

Repository: `paperg_nagel` on the arm64 machine (library `NagelLine`, Lean v4.33.1, Mathlib v4.33.1; git initialised, nothing committed).
Setting: `{V P} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]`, `t : Affine.Triangle ℝ P`.
No `Fact (finrank = 2)` needed anywhere. The only hypothesis of every main theorem is `t`.

## Definitions (NagelLine/Basic.lean)
- `Affine.Triangle.nagelPoint t := Finset.univ.affineCombination ℝ t.points fun i ↦ (semiperimeter t - side t i) / semiperimeter t` (Basic.lean:267)
- `Affine.Triangle.gergonnePoint t := Finset.univ.affineCombination ℝ t.points fun i ↦ (semiperimeter t - side t i)⁻¹ / ∑ j, (semiperimeter t - side t j)⁻¹` (Basic.lean:271)
- `Affine.Triangle.spiekerCenter t := t.medial.incenter` (Basic.lean:276)
- `NagelLine.sideA/B/C` (dist B C, dist C A, dist A B), `semiperimeter`, `side t i = ![a,b,c] i`.

## Main theorems — all PROVED, axioms: [propext, Classical.choice, Quot.sound] for each

| # | Lean statement | Proved | file:line |
|---|---|---|---|
| A1 | `theorem gergonnePoint_mem_cevian (t : Triangle ℝ P) : ∀ i, t.gergonnePoint ∈ line[ℝ, t.points i, t.touchpoint ∅ i]` | Y | NagelLine/Main.lean:290 |
| A1 cor | `theorem gergonne_cevians_concurrent (t : Triangle ℝ P) : ∃ X : P, ∀ i, X ∈ line[ℝ, t.points i, t.touchpoint ∅ i]` | Y | Main.lean:328 |
| A2 | `theorem nagelPoint_mem_cevian (t : Triangle ℝ P) : ∀ i, t.nagelPoint ∈ line[ℝ, t.points i, t.touchpoint {i} i]` | Y | Main.lean:334 |
| A2 cor | `theorem nagel_cevians_concurrent (t : Triangle ℝ P) : ∃ X : P, ∀ i, X ∈ line[ℝ, t.points i, t.touchpoint {i} i]` | Y | Main.lean:357 |
| A3(i) | `theorem nagelPoint_vsub_centroid (t : Triangle ℝ P) : t.nagelPoint -ᵥ Finset.univ.centroid ℝ t.points = (2 : ℝ) • (Finset.univ.centroid ℝ t.points -ᵥ t.incenter)` | Y | Main.lean:362 |
| A3(i) | `theorem collinear_incenter_centroid_nagelPoint (t : Triangle ℝ P) : Collinear ℝ {t.incenter, Finset.univ.centroid ℝ t.points, t.nagelPoint}` | Y | Main.lean:373 |
| A3(ii) | `theorem medial_incenter_eq_midpoint (t : Triangle ℝ P) : t.medial.incenter = midpoint ℝ t.incenter t.nagelPoint` (Mathlib's `Simplex.medial`) | Y | Main.lean:385 |
| A3(ii) | `theorem collinear_spiekerCenter_incenter_nagelPoint (t : Triangle ℝ P) : Collinear ℝ {t.spiekerCenter, t.incenter, t.nagelPoint}` | Y | Main.lean:408 |

All names are in namespace `NagelLine`.

## Bridge lemmas — all PROVED, axioms: [propext, Classical.choice, Quot.sound]
- `s_sub_a_pos/s_sub_b_pos/s_sub_c_pos : 0 < semiperimeter t - sideX t` (Basic.lean:189/194/202). Derived from `Simplex.height_pos` via the Heron identity `height0_sq…height2_sq` (Basic.lean:115/123/132) and `heron_factor` (Basic.lean:161).
- `incenter_weights : t.excenterWeights ∅ = fun i ↦ side t i / (2 * semiperimeter t)` (Basic.lean:219)
- `excenter_weights i : t.excenterWeights {i} = fun j ↦ (if j = i then -1 else 1) * side t j / (2 * (semiperimeter t - side t i))` (Basic.lean:238). So `excenter {i}` is the excentre opposite vertex i.
- `incenter_eq_affineCombination`, `excenter_singleton_eq_affineCombination` (Main.lean:68/75)
- Incircle contact points: `touchpoint_empty_zero : t.touchpoint ∅ 0 = lineMap (t.points 1) (t.points 2) ((semiperimeter t - sideB t) / sideA t)`, plus `_one` (C→A, (s−c)/b) and `_two` (A→B, (s−a)/c) (Main.lean:94/105/117)
- Excircle contact points: `touchpoint_singleton_zero : t.touchpoint {0} 0 = lineMap (t.points 1) (t.points 2) ((semiperimeter t - sideC t) / sideA t)`, plus `_one` ((s−a)/b) and `_two` ((s−b)/c) (Main.lean:129/141/155)
- `sbtw_touchpoint_singleton_zero/one/two : Sbtw ℝ B (t.touchpoint {0} 0) C` etc. (Main.lean:170/179/188). The excircle contact point is on the open segment, not its extension.
- `medial_sideA/B/C : sideX t.medial = sideX t / 2` (Main.lean:266–268)
- Also gated: `proj_eq_lineMap`, `height_sq_mul`, `projSpan0/1/2`, `height_eq`, `semiperimeter_pos`, `heronPoly`, `dblArea`.

## Open items
None. No `Open.lean` was needed. No `sorry`/`admit`/`native_decide`/`axiom`/`set_option` in the library.

## Gate
`PASS (48 declarations, standard axioms only)`. REQUIRED = the 8 main theorems, the 3 point
definitions plus the helper definitions, and every bridge lemma above.

## Tamper
`ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro → forbidden token; wrap → nonstandard axioms;
falsehyp → FAIL: build). falsehyp removes the binder `(t : Triangle ℝ P)` from `nagelPoint_vsub_centroid`.
Note: in an earlier version that binder was silently re-supplied by a section `variable`, and the
tamper suite correctly caught it as NOT OK. The main theorems were moved out of that section to fix this.

## Size
NagelLine/Basic.lean 285 lines, NagelLine/Main.lean 414 lines, root 2 lines: 701 lines total.

## Method
mpmath numeric scout (30 digits, max error 7e-27). Barycentric certificates; contact points via
`coe_orthogonalProjection_eq_iff_mem`; rational identities closed after the Ravi substitution with
`field_simp; ring` / `match_scalars`.
