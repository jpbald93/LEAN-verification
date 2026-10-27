# Paper G — Layer 14 report (Mathlib-only restatements + explicit witnesses)

Date: 2026-10-25. All work done on **the x86-64 machine** (x86_64 Linux, Lean v4.33.1, Mathlib v4.33.1). NagelLine also checked on **the arm64 machine** (arm64 macOS).
Artifacts: `AFM/PaperG/layer14/` (both L14 files, the `#check` scratch files and their pp.fullNames output, all gate and tamper logs).

## What changed (no existing statement was touched)

| repo | added | modified |
|---|---|---|
| the x86-64 machine `~/paperg_brocard` | `Brocard/L14.lean` (522 lines) | `Brocard.lean`: +`import Brocard.L14`; `gate.sh`: REQUIRED +21 names (16 `l14_` + 5 `l14w_`) |
| the x86-64 machine `~/paperg_nagel` (copy of the arm64 machine's repo, no `.lake`; packages symlinked to `~/barbier/.lake/packages`) | `NagelLine/L14.lean` (408 lines) | `NagelLine.lean`: +`import NagelLine.L14`; `gate.sh`: REQUIRED +14 names (9 `l14_` + 5 `l14w_`) |
| the arm64 machine `~/lean/paperg_nagel` | same `NagelLine/L14.lean` (scp from the x86-64 machine) | same `NagelLine.lean` and `gate.sh` (scp from the x86-64 machine) |

`diff` of each `gate.sh` against its pre-L14 copy: only the REQUIRED line changed. Basic/Main/Extensions md5s match between the x86-64 machine and the arm64 machine.

Method (as in Paper F): each `l14_` statement unfolds the library definitions into Mathlib terms, is proved directly from the library theorem (usually as a one-line term), and has an explicit witness in `EuclideanSpace ℝ (Fin 2)`. In the Brocard file, `nagelPoint`, `symmedianPoint` and the like are written as `Finset.univ.affineCombination ℝ t.points (explicit weights in dist …)`. In the NagelLine file, the Spieker centre becomes `t.medial.incenter` and the de Longchamps point becomes `(2:ℝ) • (O -ᵥ H) +ᵥ H`. The anticomplementary triangle becomes "any `T : Triangle` with `T.points i = homothety G (-2) (t.points i)`", and the witness shows such a `T` exists. Each `l14w_` theorem is stated as `∀ t, t.points = ![…] → …`, so its type also uses only Mathlib terms.

## Brocard (Groups B, D)

Witness triangle: A=(0,0), B=(4,0), C=(1,3). Here a²=18, b²=10, c²=16, O=(2,1), H=(1,1), G=(5/3,1), K=(14/11,12/11), Ω₁=(220/157,120/157), Ω₂=(232/157,216/157) and Δ=6.

| theorem | l14 name | witness / non-vacuity shown | findings |
|---|---|---|---|
| B1 symmedian angles | `l14_symmedian_angles` | `l14w_brocard`: K ≠ A, B, C, G (so the symmedian ≠ median) | none |
| B1 K interior | `l14_symmedianPoint_mem_interior` | `l14w_brocard` (K computed) | none |
| B2 K = centroid of pedal | `l14_symmedianPoint_eq_centroid_pedal` | `l14w_pedal` | none |
| B2 converse | `l14_eq_symmedianPoint_of_eq_centroid_pedal` | `l14w_pedal`: G is **not** the centroid of its own pedal triangle, so the property separates points | keeps the library hypothesis `[Fact (finrank ℝ V = 2)]` (a Mathlib notion); the witness gets an instance from `finrank_euclideanSpace_fin` |
| B3 Brocard points | `l14_brocardPoint₁_angles`, `l14_brocardPoint₂_angles` | `l14w_brocard`: Ω₁, Ω₂ ≠ any vertex, Ω₁ ≠ Ω₂ | none |
| B4 cot identities | `l14_cot_brocardAngle_eq_sum_cot`, `l14_cot_brocardAngle_eq_div_area` (area unfolded as `½·AB·AC·sin∠BAC`) | `l14w_brocardAngle`: Δ = 6, cot ω = 11/6 | none |
| B4 ω bound | `l14_brocardAngle_pos_le` | `l14w_brocardAngle`: 0 < ω **<** π/6 (strict, since the triangle is not equilateral) | none |
| D1 isogonal Brocard points | `l14_brocardPoints_isogonal`, `l14_dist_circumcenter_brocardPoint` | `l14w_brocard` (OΩ₁² = OΩ₂² = 65/157 numerically, Ω₁ ≠ Ω₂) | as in the library, "isogonal" means the three angle equalities |
| D2 Brocard circle | `l14_brocardCircle` (dist form + `Cospherical`), `l14_brocardCircle_right_angles`, `l14_brocardCircle_degenerate` (iff + equilateral ⇒ all = O) | `l14w_brocard`: O, K, Ω₁, Ω₂ pairwise distinct (K ≠ O), triangle not equilateral | the right-angle statement holds vacuously (by Mathlib's `angle` convention) only when Ω = O or K; the witness rules this out |
| D3 Lemoine circle | `l14_lemoineCircle` (six explicit `lineMap` points + membership on side and parallel through K + equal distances + `Cospherical`) | `l14w_lemoine`: the six points (13/22,39/22), (26/11,0), (37/22,51/22), (10/11,0), (32/11,12/11), (4/11,12/11) are pairwise distinct | none |
| D4 Droz-Farny | `l14_drozFarny` | `l14w_drozFarny`: H=(1,1), d₁=(1,2), d₂=(2,−1); all six non-parallel hypotheses and all 12 memberships proved; midpoints (10/3,2/3), (−2/7,−6/7), (7/4,0) pairwise distinct | keeps `[Fact (finrank ℝ V = 2)]` |

## NagelLine (Groups A, C)

Main witness: the 3-4-5 triangle A=(0,0), B=(4,0), C=(0,3), with a=5, b=3, c=4, s=6, I=(1,1), G=(4/3,1), N=(2,1), Gergonne point (8/11,9/11) and Spieker centre (3/2,1).

| theorem | l14 name | witness / non-vacuity shown | findings |
|---|---|---|---|
| A1 Gergonne cevians + concurrence | `l14_gergonne` | `l14w_nagel`: all six touchpoints computed; for i ≠ j, vertex j ∉ cevian i, so the three cevians are pairwise distinct lines | none |
| A2 Nagel cevians + concurrence | `l14_nagel` | `l14w_nagel`: same distinctness for the Nagel cevians; Ge ≠ N | none |
| A3 Nagel line | `l14_nagelLine` (N−G = 2(G−I), collinear) | `l14w_nagel`: I, G, N pairwise distinct | none |
| A4 Spieker | `l14_spieker` (`t.medial.incenter` = midpoint I N, collinear) | `l14w_nagel`: Spieker centre = (3/2,1) | none |
| C1 de Longchamps | `l14_deLongchamps` (midpoint, two collinearities, orthocentre of any homothety-(G,−2) image) | `l14w_deLongchamps` on (0,0),(4,0),(1,3): O=(2,1), H=(1,1), L=(3,1), with L ≠ O, H, G and O ≠ H; the anticomplementary T = (5,3),(−3,3),(3,−3) exists, satisfies the hypothesis, and has orthocentre L | the 3-4-5 triangle is right-angled (H = A); a scalene acute triangle was used instead |
| C2 medial Nagel | `l14_medial_nagel` | `l14w_medial_nagel`: value (1,1) = I, ≠ medial incentre (3/2,1) | none |
| C2 isotomic contacts | `l14_isotomic` | `l14w_nagel`: incircle touchpoint ≠ excircle touchpoint on every side | none |
| C3 N = anticomplementary incentre | `l14_nagel_anticomplementary` | `l14w_nagel_anticomplementary`: T = (4,3),(−4,3),(4,−3) exists, satisfies the hypothesis, and has incentre (2,1) ≠ I | none |
| C4 Spieker radical centre | `l14_spieker_radical` | `l14w_spieker_radical`: excentres (6,6), (−2,2), (3,−3) and exradii 6, 2, 3 (three distinct circles); the power of S is 37/4 for each | none |

## Findings

**No restatement turned out FALSE, and none needed a hypothesis the library theorem didn't already have.** Every `l14_` theorem follows directly from its library theorem with no extra hypotheses. The only hypotheses beyond the triangle are `[Fact (Module.finrank ℝ V = 2)]` (pedal converse, Droz-Farny), which the library statements already have, plus Droz-Farny's own geometric hypotheses. The witnesses show all of these can be satisfied.

Minor observations (not defects):
- The right-angle form of D2 (`∠ O Ω K = π/2`) is vacuous when Ω coincides with O or K (Mathlib's convention). The library states exactly when that happens (equilateral triangles), and the witness is non-equilateral.
- C1 witness: the 3-4-5 triangle would give H = A, a degenerate-looking case, so C1 uses (0,0),(4,0),(1,3).

## Gate / tamper results

| repo | machine | gate | tamper (`tests/tamper.sh`, 7 tests) |
|---|---|---|---|
| Brocard | the x86-64 machine x86_64 | `PASS (88 declarations, standard axioms only)` (was 67) | `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp2) |
| NagelLine | the x86-64 machine x86_64 | `PASS (91 declarations, standard axioms only)` (was 77) | `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp_ext) |
| NagelLine | the arm64 machine arm64 (`~/lean/jl gate` / `~/lean/jl tamper`) | `PASS (91 declarations, standard axioms only)` | `ALL TAMPERING TESTS REJECTED` |

Every new REQUIRED entry reports `[propext, Classical.choice, Quot.sound]`. Brocard was not run on the arm64 machine, because the task only asked for NagelLine there.

## Type check (pp.fullNames)

The scratch files `layer14/BTypes.lean` and `NTypes.lean` contain `set_option pp.fullNames true` (plus funBinderTypes and letVarTypes) and `#check @<Lib>.<name>` for every `l14_`/`l14w_` theorem. After removing each output's own header name (`@Brocard.l14_… :` / `@NagelLine.l14_… :`), I grepped for `Brocard\.|NagelLine\.`:

```
Brocard  : 21 types checked (16 l14_ + 5 l14w_), 0 errors, matches = 0
NagelLine: 14 types checked (9 l14_ + 5 l14w_),  0 errors, matches = 0
```

Full outputs: `layer14/brocard_l14_types_ppFullNames.txt` and `layer14/nagel_l14_types_ppFullNames.txt`. Sample (`Brocard.l14_brocardPoint₁_angles`):
```
∀ … (t : Affine.Triangle ℝ P), have A : P := t.points 0; … have a2 : ℝ := Dist.dist B C ^ 2; …
  have Ω : P := (Finset.affineCombination ℝ Finset.univ t.points) fun (i : Fin (2 + 1)) =>
      ![1 / b2, 1 / c2, 1 / a2] i / (1 / a2 + 1 / b2 + 1 / c2);
  EuclideanGeometry.angle Ω A B = EuclideanGeometry.angle Ω B C ∧ EuclideanGeometry.angle Ω B C = EuclideanGeometry.angle Ω C A
```
The first version of the witnesses mentioned the helper definition `Brocard.l14T` in their types, and the grep caught it. I restated them in the `∀ t, t.points = ![…] →` form, after which the grep is clean. The helper lemmas (`l14b_*`, `l14T*`) are internal, are not part of the check, and are not in REQUIRED.
