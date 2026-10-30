# Paper H — Layer 14 report (Mathlib-only restatements + explicit witnesses)

Date 2026-10-29. All work done inline: no subagents. Background processes were only the baseline gates and the `tests/tamper.sh` runs, all waited on.
Work copies: x86-64 machine `~/l14h_euler`, `~/l14h_fermat` (packages symlinked to `~/paperi_quad/.lake/packages`; every build/gate/tamper ran under `flock ~/ph.lock`), and arm64 machine `~/lean/l14h_mordell` (packages symlinked to `~/lean/paperi_arbelos/.lake/packages`). Toolchain v4.33.1 everywhere, matching the package donors. No `lake update` or `cache get` was run. The published clones in `~/ghreceipt` were not touched. **Nothing was pushed.**
Scratch (Python witness checks, generators, type-check outputs): `<work-dir>` (`check_euler.py`, `check_mordell.py`, `check_fermat.py`: exact `Fraction` / `ℚ(√3)` arithmetic, all pass).
Changes per repo: new `<Lib>/L14.lean`; one line `import <Lib>.L14` appended at the end of `<Lib>.lean`; in `gate.sh` only the REQUIRED line changed (git numstat 1/1). Commit stats: 3 files, +332/−1 (euler), +383/−1 (mordell), +383/−1 (fermat).

## Repo paperh_euler (x86-64 machine) — `EulerIneq/L14.lean`, base d1edd80 → commit **545a974df2663e30d735d9de43d62dd3a7c79c6b**

Local definitions unfolded: `area t` → `1/2 * dist A B * dist A C * Real.sin (∠ B A C)`; `semiperimeter t` → `(a + b + c)/2`. Circumcenter, circumradius, incenter, inradius, excenter, exradius, centroid and orthocenter are already Mathlib's `Affine.Simplex.*`.
Witness triangle `l14T` = (0,0),(4,0),(0,3) in `EuclideanSpace ℝ (Fin 2)`: a,b,c = 5,3,4, Δ = 6, s = 6, R = 5/2, r = 1, all proved in Lean.

| main theorem | l14_ done | Mathlib-only type verified | l14w_ witness | distinctness / strictness | notes |
|---|---|---|---|---|---|
| euler | l14_euler | yes | l14w_triangle | OI² = 5/4 ≠ 0 (I ≠ O) | no hypotheses |
| euler_inequality | l14_euler_inequality | yes | l14w_triangle | 2r = 2 < 5/2 = R (strict) | |
| euler_inequality_eq_iff | l14_euler_inequality_eq_iff | yes | l14w_triangle | non-equilateral, both sides false | |
| euler_excenter | l14_euler_excenter | yes | (no hypotheses) | — | |
| dist_circumcenter_centroid_sq | l14_… | yes | l14w_triangle | OG² = 25/36 | |
| dist_circumcenter_orthocenter_sq | l14_… | yes | l14w_triangle | OH² = 25/4 | |
| dist_incenter_centroid_sq | l14_… | yes | l14w_triangle | IG² = 1/9 | |
| fundamental_quartic | l14_… | yes | l14w_triangle | value −1 < 0 (strict) | |
| gerretsen | l14_gerretsen | yes | l14w_triangle | 35 < 36 < 38 (both strict) | |
| kooi | l14_kooi | yes | l14w_triangle | 36 < 605/16 (strict) | |
| kooi_le_gerretsen | l14_… | yes | l14w_triangle | 605/16 < 38 (strict) | |
| weitzenboeck (+_eq_iff) | l14_weitzenboeck, l14_weitzenboeck_eq_iff | yes | l14w_triangle | 24√3 < 50 (strict) | |
| hadwiger_finsler (+_eq_iff) | l14_hadwiger_finsler, l14_…_eq_iff | yes | l14w_triangle | 24√3 + 6 < 50 (strict) | |
| isoperimetric (+_eq_iff) | l14_isoperimetric, l14_…_eq_iff | yes | l14w_triangle | 72√3 < 144 (strict) | |
| leibniz_relation | l14_leibniz_relation | yes | (identity) | — | |
| leibniz_min (+_eq_iff) | l14_leibniz_min, l14_…_eq_iff | yes | l14w_leibniz | X = A ≠ centroid; 50/3 < 25 (strict) | |
| pedoe (+_eq_iff) | l14_pedoe, l14_pedoe_eq_iff | yes | l14w_pedoe | t = 3-4-5 and t′ = (0,0),(1,0),(0,1): not similar (proved ¬∃k); 48 < 50 (strict) | |
| ptolemy_inequality | l14_ptolemy_inequality | yes | l14w_ptolemy_inequality | (0,0),(4,0),(0,3),(4,3) in the non-cyclic order: 9 < 41 (strict) | |

Helpers: l14_dist_sq, l14_dist, l14_not_collinear, l14_ne, l14T, l14T', l14T_sides, l14T_area, l14T_inradius, l14T_circumradius, l14T'_sides, l14T'_area, l14_sqrt3_lt.
Gate: before `PASS (60 declarations, standard axioms only)` → after `PASS (100 declarations, standard axioms only)`.
Tamper: sorry, ax2line, evalfake, macro (forbidden token); wrap (nonstandard axioms); falsehyp, falsehyp2, falsehyp3, falsestmt (build) → **ALL TAMPERING TESTS REJECTED**.
REQUIRED added (40): EulerIneq.l14_euler EulerIneq.l14_euler_inequality EulerIneq.l14_euler_inequality_eq_iff EulerIneq.l14_euler_excenter EulerIneq.l14_dist_circumcenter_centroid_sq EulerIneq.l14_dist_circumcenter_orthocenter_sq EulerIneq.l14_dist_incenter_centroid_sq EulerIneq.l14_fundamental_quartic EulerIneq.l14_gerretsen EulerIneq.l14_kooi EulerIneq.l14_kooi_le_gerretsen EulerIneq.l14_weitzenboeck EulerIneq.l14_weitzenboeck_eq_iff EulerIneq.l14_hadwiger_finsler EulerIneq.l14_hadwiger_finsler_eq_iff EulerIneq.l14_isoperimetric EulerIneq.l14_isoperimetric_eq_iff EulerIneq.l14_leibniz_relation EulerIneq.l14_leibniz_min EulerIneq.l14_leibniz_min_eq_iff EulerIneq.l14_pedoe EulerIneq.l14_pedoe_eq_iff EulerIneq.l14_ptolemy_inequality EulerIneq.l14_dist_sq EulerIneq.l14_dist EulerIneq.l14_not_collinear EulerIneq.l14_ne EulerIneq.l14T EulerIneq.l14T' EulerIneq.l14T_sides EulerIneq.l14T_area EulerIneq.l14T_inradius EulerIneq.l14T_circumradius EulerIneq.l14T'_sides EulerIneq.l14T'_area EulerIneq.l14_sqrt3_lt EulerIneq.l14w_triangle EulerIneq.l14w_leibniz EulerIneq.l14w_pedoe EulerIneq.l14w_ptolemy_inequality 

## Repo paperh_mordell (arm64 machine) — `ErdosMordell/L14.lean`, base 01ddb52 → commit **c4bc4c4f2d07c996a04667cb1fc59ef6b42b0323**

Unfolded: the library's side-line distance `dist X (orthogonalProjection line[ℝ,Y,Z] X)` → `Metric.infDist X (line[ℝ,Y,Z] : Set P)`, via Mathlib's `dist_orthogonalProjection_eq_infDist`. The barycentric hypotheses become Mathlib's `t.closedInterior` (key lemmas, Erdős–Mordell) and `t.interior` (Barrow), via bridges `l14_of_mem_closedInterior` / `l14_of_mem_interior`.

| main theorem | l14_ done | Mathlib-only type verified | l14w_ witness | distinctness / strictness | notes |
|---|---|---|---|---|---|
| key_lemma_zero/one/two | l14_key_lemma_zero/one/two | yes | l14w_erdos_mordell | 3-4-5 triangle with X = (1,1) ∈ interior; all three strict (7 < 5√2, 9 < 3√10, 8 < 4√5) | side-line distances bounded by explicit feet (8/5,9/5), (0,1), (1,0) |
| erdos_mordell | l14_erdos_mordell | yes | l14w_erdos_mordell | 6 < √2+√10+√5 (strict); X ≠ each vertex | |
| erdos_mordell_eq_iff | l14_erdos_mordell_eq_iff | yes | l14w_erdos_mordell (RHS false) + l14w_erdos_mordell_eq (equality attained) | equilateral (0,0),(2,0),(1,√3) with X = centroid | equality needs √3 coordinates (no rational equilateral triangle) |
| barrow | l14_barrow | yes | l14w_barrow | A=(5,0), B=(−3,4), C=(−3,−4), X=(0,0) ∈ interior (weights 3/8, 5/16, 5/16); U=(−3,0), V=(1,−2), W=(1,2), pairwise distinct; bisector conditions proved; 6+4√5 < 15 (strict) | |
| fermat_min | l14_fermat_min | yes (verbatim) | l14w_fermat_min | F=0, A=2, B=(−1,√3), C=(−1,−√3), angles = 2π/3 proved; A,B,C pairwise distinct; at X=A: 6 < 4√3 (strict) | exact 2π/3 angles need √3 |
| fermat_exists | l14_fermat_exists | yes (verbatim) | l14w_fermat_torricelli | 3-4-5 angles < 2π/3 (inner products 0, 16, 9) | |
| fermat_torricelli | l14_fermat_torricelli | yes (verbatim) | l14w_fermat_torricelli | the Fermat point is ≠ every vertex | |

Gate: before `PASS (48 declarations, standard axioms only)` → after `PASS (76 declarations, standard axioms only)`.
Tamper: sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp_ext → **ALL TAMPERING TESTS REJECTED**.
REQUIRED added (28): ErdosMordell.l14_of_mem_closedInterior ErdosMordell.l14_of_mem_interior ErdosMordell.l14_key_lemma_zero ErdosMordell.l14_key_lemma_one ErdosMordell.l14_key_lemma_two ErdosMordell.l14_erdos_mordell ErdosMordell.l14_erdos_mordell_eq_iff ErdosMordell.l14_barrow ErdosMordell.l14_fermat_min ErdosMordell.l14_fermat_exists ErdosMordell.l14_fermat_torricelli ErdosMordell.l14_dist_sq ErdosMordell.l14_dist ErdosMordell.l14_not_collinear ErdosMordell.l14_ne ErdosMordell.l14_inner ErdosMordell.l14_mem_line ErdosMordell.l14_ac ErdosMordell.l14_angle_lt ErdosMordell.l14_angle_eq ErdosMordell.l14T ErdosMordell.l14T_sides ErdosMordell.l14T_incenter_mem ErdosMordell.l14w_erdos_mordell ErdosMordell.l14w_erdos_mordell_eq ErdosMordell.l14w_barrow ErdosMordell.l14w_fermat_min ErdosMordell.l14w_fermat_torricelli 

## Repo paperh_fermat (x86-64 machine) — `FermatNapoleon/L14.lean`, base f6660dc → commit **667a8774db29f9fcec1894bec6259392068fb469**

Unfolded: `triSign`, `outerApex`, `napoleonApex` and `napoleonCenter`. The apexes A′, B′, C′ are universally quantified points with hypotheses
`A' = ((1/2:ℝ) • (C -ᵥ B) - (σ * (√3/2)) • o.rightAngleRotation (C -ᵥ B)) +ᵥ B` (cyclically), where `σ = if 0 < o.areaForm (B -ᵥ A) (C -ᵥ A) then 1 else -1`. This is Mathlib's `o.rotation (-(σπ/3))` written via cos/sin; bridge `l14b_outerApex_eq`.
The Napoleon centres are `Finset.univ.centroid ℝ ![B, C, A']` (cyclically). The Ptolemy theorems were already Mathlib-only and are restated verbatim.
Witnesses are in ℂ with `Complex.orientation` (J z = I·z; checked symbolically in ℚ(√3) by `check_fermat.py`).

| main theorem | l14_ done | Mathlib-only type verified | l14w_ witness | distinctness / strictness | notes |
|---|---|---|---|---|---|
| ptolemy_eq_iff | l14_ptolemy_eq_iff | yes (verbatim) | l14w_ptolemy_cyclic, l14w_ptolemy_collinear | cyclic: rectangle 0, 4, 4+3i, 3i, pairwise distinct, cospherical (centre 2+3/2 i, r = 5/2), diagonals meet at the centre, **not collinear** (proved); 25 = 16+9. Collinear: 0,1,2,3 pairwise distinct; 4 = 1+3 | both disjuncts are realised |
| ptolemy_collinear | l14_ptolemy_collinear | yes (verbatim) | l14w_ptolemy_collinear | Sbtw 0 1 2, Sbtw 1 2 3 | |
| ptolemy_real | l14_ptolemy_real | yes (verbatim) | l14w_ptolemy_real | (0,1,2,3): both sides true; (0,1,3,2): both sides false | |
| apex_outward | l14_apex_outward | yes | l14w_napoleon (apexes computed) | A′ ≠ A, B′ ≠ B, C′ ≠ C | |
| napoleon_dist_eq | l14_napoleon_dist_eq | yes | l14w_napoleon | A′, B′, C′ pairwise distinct | |
| napoleon_concurrent | l14_napoleon_concurrent | yes | l14w_napoleon | F lies on all three lines | |
| napoleon_fermat | l14_napoleon_fermat | yes | l14w_napoleon | all angles < 2π/3 proved; F sees the sides at 2π/3; F ≠ every vertex | |
| napoleon_angle | l14_napoleon_angle | yes | l14w_napoleon (no extra hyps) | — | |
| napoleon | l14_napoleon | yes | l14w_napoleon | N₀ ≠ N₁ (Re 2+√3/2 vs −√3/2): the Napoleon triangle is non-degenerate | |

Witness: A=0, B=4, C=3i (σ = 1). A′ = (2+3√3/2) + (3/2+2√3)i, B′ = −3√3/2 + (3/2)i, C′ = 2 − 2√3 i. Each is proved equal to the explicit formula.
Bridges l14b_outerApex_eq and l14b_apexes deliberately mention the library definitions: they connect the library notions to the explicit formulas. They are not restatements. Other helpers: l14_angle_lt, l14_ne_of_angle, l14_dist_sq, l14_dist, l14_ne, l14_not_collinear, l14_sbtw, l14_centroid, l14T, l14T_sign.
Gate: before `PASS (47 declarations, standard axioms only)` → after `PASS (72 declarations, standard axioms only)`.
Tamper: sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp2, falsehyp3, falsestmt → **ALL TAMPERING TESTS REJECTED**.
REQUIRED added (25): FermatNapoleon.l14b_outerApex_eq FermatNapoleon.l14b_apexes FermatNapoleon.l14_apex_outward FermatNapoleon.l14_napoleon_dist_eq FermatNapoleon.l14_napoleon_concurrent FermatNapoleon.l14_napoleon_fermat FermatNapoleon.l14_napoleon FermatNapoleon.l14_napoleon_angle FermatNapoleon.l14_ptolemy_eq_iff FermatNapoleon.l14_ptolemy_collinear FermatNapoleon.l14_ptolemy_real FermatNapoleon.l14_angle_lt FermatNapoleon.l14_ne_of_angle FermatNapoleon.l14_dist_sq FermatNapoleon.l14_dist FermatNapoleon.l14_ne FermatNapoleon.l14_not_collinear FermatNapoleon.l14_sbtw FermatNapoleon.l14_centroid FermatNapoleon.l14T FermatNapoleon.l14T_sign FermatNapoleon.l14w_napoleon FermatNapoleon.l14w_ptolemy_cyclic FermatNapoleon.l14w_ptolemy_collinear FermatNapoleon.l14w_ptolemy_real 

## FINDINGS
- **No restatement turned out false, and none needed an extra hypothesis.** Every `l14_*` follows from the library theorem with the same hypotheses, with local definitions unfolded to their natural Mathlib meaning:
  - `area` = ½·AB·AC·sin A agrees with the usual area for every nondegenerate triangle.
  - The distance to a side line equals `Metric.infDist` (exact Mathlib lemma, no degenerate case, because Triangle forces Y ≠ Z).
  - The barycentric "closed triangle" / "strictly inside" hypotheses are definitionally Mathlib's `closedInterior` / `interior` (weights in Icc 0 1 / Ioo 0 1; given that the weights sum to 1, these match the library's 0 ≤ w / 0 < w).
  - The apex is exactly Mathlib's rotation by −σπ/3, and σ is total (a degenerate areaForm cannot occur for a Triangle).
- Observation: the equality cases `erdos_mordell_eq_iff` (equilateral), `fermat_min` (exact 2π/3 angles) and the Napoleon apexes cannot be realised with rational coordinates. Those witnesses use ℚ(√3) coordinates, which is the minimal extension. Everything else uses small integers.
- Observation (coverage): every hypothesis-bearing main theorem has a witness. For the `_eq_iff` theorems the witnesses show the RHS fails (non-equilateral, non-similar, X ≠ centroid). For Erdős–Mordell and Ptolemy, the equality side is also exhibited (l14w_erdos_mordell_eq, l14w_ptolemy_cyclic/collinear). For Euler, Weitzenböck, Hadwiger–Finsler, isoperimetric and Pedoe, no equality witness is given (it would need an equilateral triangle, √3).
- Cosmetic: the mordell and fermat L14 files trigger Lean *linter warnings* ("`tac1 <;> tac2` where `(tac1; tac2)` would suffice", "unused tactic"). These are not errors and the gate does not check them; I left them as they are.

## Mechanical type check (pp.fullNames true, pp.proofs false)
Scratch files `scratch/{euler,mordell,fermat}_types.lean` contain one `#check @NS.l14…` per theorem. The outputs are copied to `AFM/PaperH/L14_types_{euler,mordell,fermat}.out`. 0 errors in each. Per-declaration count of `EulerIneq.|ErdosMordell.|FermatNapoleon.` in the type body (the header `NS.name :` is excluded):
```
EulerIneq: blocks=32 hits_in_l14_and_l14w_types=0
ErdosMordell: blocks=25 hits_in_l14_and_l14w_types=0
  l14b_outerApex_eq (bridge): 1 hits
  l14b_apexes (bridge): 3 hits
FermatNapoleon: blocks=23 hits_in_l14_and_l14w_types=0
l14h_euler_types.out: raw grep -cE 'EulerIneq\.|ErdosMordell\.|FermatNapoleon\.' after stripping the '@NS.l14… :' headers = 0
l14h_fermat_types.out: raw grep -cE 'EulerIneq\.|ErdosMordell\.|FermatNapoleon\.' after stripping the '@NS.l14… :' headers = 3
l14h_mordell_types.out: raw grep -cE 'EulerIneq\.|ErdosMordell\.|FermatNapoleon\.' after stripping the '@NS.l14… :' headers = 0
```
So **0 hits in every l14_/l14w_ type**. The only hits (3 lines, 4 occurrences) are in the two Fermat bridge lemmas `l14b_outerApex_eq` / `l14b_apexes`, whose purpose is to relate the library definitions to the explicit formula.

## Gate / tamper lines
| repo | gate before | gate after | tamper |
|---|---|---|---|
| euler | PASS (60 declarations, standard axioms only) | PASS (100 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED (9/9) |
| mordell | PASS (48 declarations, standard axioms only) | PASS (76 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED (7/7) |
| fermat | PASS (47 declarations, standard axioms only) | PASS (72 declarations, standard axioms only) | ALL TAMPERING TESTS REJECTED (9/9) |
Forbidden-token grep over the three L14 files (sorry/admit/native_decide/axiom/#eval/set_option/macro/notation/run_cmd): no hits.

## Hashes (sha256 of every .lean, fresh clone → final)
Every pre-existing .lean is unchanged except the root `<Lib>.lean`, which gained exactly one import line (as allowed).
### euler (before)
```
0f92ec497d22bcd9458e22d135b76adc0a632af6b8a3feb1a70591413b003dc9  ./EulerIneq/Basic.lean
06ae8ae852bcd0f23f43c4e25d588a4f7036ef623f9f83d42526b278c270176f  ./EulerIneq/Bridges.lean
f23e16d925588266b912198a0059dbd1e4da25279397a585c763993ca1b4a2d2  ./EulerIneq/Extremal.lean
d876dcfc03293908a60e59008da45fcf8c57eb5ce2cdef6a56ee035988a7a745  ./EulerIneq/Kooi.lean
efbdbc482b2825f008eb9cf561b5058f49025156c373f0d3c6822e2631695814  ./EulerIneq.lean
c7cf76cfc673df2b49222fd0f2bc4b1d72cce9979ebe2c5ed4b30310edec0a23  ./EulerIneq/Main.lean
25c20ca01a1d7cf5e6699aa0a1e519c650d83273702e4f84c833eead9f8b58f3  ./EulerIneq/Pedoe.lean
5595a199cd66f8ace6f2cc43a32b2249ad129b44b8bd10d05414d94d0abb13c0  ./EulerIneq/Ptolemy.lean
```
### euler (after)
```
0f92ec497d22bcd9458e22d135b76adc0a632af6b8a3feb1a70591413b003dc9  ./EulerIneq/Basic.lean
06ae8ae852bcd0f23f43c4e25d588a4f7036ef623f9f83d42526b278c270176f  ./EulerIneq/Bridges.lean
f23e16d925588266b912198a0059dbd1e4da25279397a585c763993ca1b4a2d2  ./EulerIneq/Extremal.lean
d876dcfc03293908a60e59008da45fcf8c57eb5ce2cdef6a56ee035988a7a745  ./EulerIneq/Kooi.lean
d9844929bd157fbb83c2556a9ec91d32ef4841f9ef4a6955ccafc697a7855b3f  ./EulerIneq/L14.lean
8d3906c1cf8d7734c51aa05594584f5de31f26950ed353d4f0f1a48ad4d62273  ./EulerIneq.lean
c7cf76cfc673df2b49222fd0f2bc4b1d72cce9979ebe2c5ed4b30310edec0a23  ./EulerIneq/Main.lean
25c20ca01a1d7cf5e6699aa0a1e519c650d83273702e4f84c833eead9f8b58f3  ./EulerIneq/Pedoe.lean
5595a199cd66f8ace6f2cc43a32b2249ad129b44b8bd10d05414d94d0abb13c0  ./EulerIneq/Ptolemy.lean
```
### fermat (before)
```
0b6d1d27292b22e44014714306277781674996bf2e7ba4520eb703fe9be8be4b  ./FermatNapoleon/Basic.lean
59b961f0af113f1de335a755845febaa417df88846c86edcb961245d8f331dc0  ./FermatNapoleon/Bridges.lean
3cc488c0590cdabaf0bb98ab04c96b8bcc52ca10204d5e1bdcdf4226cedd01da  ./FermatNapoleon.lean
fca603ff9bb17e3fd2c513c92fc9cb79bb76a29d22b87510cf313e34fd9822ff  ./FermatNapoleon/Lemmas.lean
b6cf643c4c19233aac489108d5f5d51c2eaf7d23b42f2a9e167ecf7519713b86  ./FermatNapoleon/Main.lean
e671803652558f0e482b3c65a9aa8cfe4cf17be68099a249de6aaddbe5cd9b99  ./FermatNapoleon/Ptolemy.lean
```
### fermat (after)
```
0b6d1d27292b22e44014714306277781674996bf2e7ba4520eb703fe9be8be4b  ./FermatNapoleon/Basic.lean
59b961f0af113f1de335a755845febaa417df88846c86edcb961245d8f331dc0  ./FermatNapoleon/Bridges.lean
d5df743e16b3d250b1e69b4b7ba46fbe48044acdf5bd0c9ee57bb5fa61b247e5  ./FermatNapoleon/L14.lean
71b6055afaccd34f14c789c290a4a050d8b84d2f75a887918a053584750c79d3  ./FermatNapoleon.lean
fca603ff9bb17e3fd2c513c92fc9cb79bb76a29d22b87510cf313e34fd9822ff  ./FermatNapoleon/Lemmas.lean
b6cf643c4c19233aac489108d5f5d51c2eaf7d23b42f2a9e167ecf7519713b86  ./FermatNapoleon/Main.lean
e671803652558f0e482b3c65a9aa8cfe4cf17be68099a249de6aaddbe5cd9b99  ./FermatNapoleon/Ptolemy.lean
```
### mordell (before)
```
d0da90e41240c8ddb45ee6f0a8c80e1dbec2bb515d23c52b474a320e5ae44e3d  ./ErdosMordell.lean
fd21c2f54fa904cc7601561426a149bc2d8970db24858ca8f62643eb35a0c270  ./ErdosMordell/Barrow.lean
97438d9d9587def27ce488109bc6e5273050584b8179cbae11ea2b3917dc39a1  ./ErdosMordell/Basic.lean
d1e6e5e34cf646260242f7ab481d961ff45c54237292c8dd3f4483617bbaa6fa  ./ErdosMordell/Fermat.lean
d0b1fef442eaf628fdc35ad020295c31636a1c2aa021d0b63d91afe11e2afdb6  ./ErdosMordell/Mordell.lean
```
### mordell (after)
```
f801667836ff3d83d42fbe64012dee7317dc7342352b2d7f6439d633eb38b10d  ./ErdosMordell.lean
fd21c2f54fa904cc7601561426a149bc2d8970db24858ca8f62643eb35a0c270  ./ErdosMordell/Barrow.lean
97438d9d9587def27ce488109bc6e5273050584b8179cbae11ea2b3917dc39a1  ./ErdosMordell/Basic.lean
d1e6e5e34cf646260242f7ab481d961ff45c54237292c8dd3f4483617bbaa6fa  ./ErdosMordell/Fermat.lean
6d54c0a6e14509f6b0c0b4d16b2146028218a1bdeddacdf739878ac898c08faa  ./ErdosMordell/L14.lean
d0b1fef442eaf628fdc35ad020295c31636a1c2aa021d0b63d91afe11e2afdb6  ./ErdosMordell/Mordell.lean
```

## Commits (local only, author "Josh Bald <jpbald93@gmail.com>", message "Layer 14: Mathlib-only restatements and witnesses")
- paperh_euler (x86-64 machine ~/l14h_euler): 545a974df2663e30d735d9de43d62dd3a7c79c6b (parent d1edd8009962976316a698575a74bca5391d308c)
- paperh_mordell (arm64 machine ~/lean/l14h_mordell): c4bc4c4f2d07c996a04667cb1fc59ef6b42b0323 (parent 01ddb5294cab6c7196e59ffd4061aee3c2100866)
- paperh_fermat (x86-64 machine ~/l14h_fermat): 667a8774db29f9fcec1894bec6259392068fb469 (parent f6660dc9c9cfa84825003e943bde2fba3e316be2)
No push.

DONE L14
