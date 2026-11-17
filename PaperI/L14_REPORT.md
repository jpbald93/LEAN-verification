# Paper I — Layer 14 report (Mathlib-only restatements + explicit witnesses)

Date: 2026-10-30. Work copies only (originals untouched, verified clean: `git status` empty, HEAD unchanged):
jack `~/l14i_quad`, `~/l14i_circles`; john `~/lean/l14i_arbelos`, `~/lean/l14i_inversion`.
In each copy the changes are exactly: new `<Lib>/L14.lean`, one `import <Lib>.L14` line appended to the
root `<Lib>.lean`, and the new names appended to the `REQUIRED=` line of `gate.sh` (only that line changed).
No existing statement was changed. No sorry/admit/axiom/native_decide/#eval/set_option/macro/notation/run_cmd
in library files (the gate's forbidden-token scan passes on the L14 files). The `pp.fullNames` / constant-scan
check uses a scratch file outside the library (it needs `set_option`/`run_cmd`), so it is not gated.

Method for (A): each `l14_<name>` states the theorem with every local definition unfolded and is proved
by the library theorem itself (term-mode or `simpa only [invPt_eq_inversion]`), so the restated type is
definitionally the original. For (B): every witness was checked first in Python (`fractions`, sympy),
scripts in `/home/work/.openclaw/tmp/paperI/l14/py/`.

## FINDINGS
* **No restatement turned out false, and none needed an extra hypothesis.** All 50 `l14_` theorems are
  proved directly from the library theorems.
* Peaucellier–Lipkin: an integer search (all legs ≤ 200) found **no linkage with rational `a, b, R`**, for
  either the classical cell (`b² − a² = R²`) or the pivot-inside cell. The witnesses use irrational link
  lengths (`a = √10, b = √26, R = 4` and `a = √10, b = √2, R = √8`), with rational joint positions. This is
  a fact about the witnesses only; the theorems themselves are unaffected.
* Steiner porism: the witness is the concentric configuration (`S₁ = (0,1)`, `S₂ = (0,3)`, six unit
  circles). The hypotheses do not require non-concentric circles, so this is a valid witness, but it does
  not exercise the inversion reduction.
* Twin circles: the radii are rational (`2/3`), but the centres have irrational imaginary parts (`2√(2/3)`,
  `2√(4/3)`). This cannot be avoided for `a = 1, b = 2`.
* Fuss: **a rational, non-square bicentric kite** exists and is used: `A = −5, B = (−7+24i)/5, C = 5,
  D = (−7−24i)/5`, sides `6, 8, 8, 6`, `R = 5`, `r = 24/7`, `d = OI = 5/7`. Both sides of the conclusion
  equal `49/576`.
* Some statements have no witness because they have no non-trivial hypotheses: Euler's quadrilateral
  theorem, Van Aubel, `radicalAxis_eq_inner`, `pencilPow_eq_powPt`, `pencilCenter_mem_line`,
  `johnson_congruent`, `descartes_solve`. Others with only side conditions such as `R ≠ 0`, `P ≠ 0` or
  `O₁ ≠ O₂` also have no separate `l14w_`: `invPt_invPt`, `norm_sq_invPt`, `dist_sq_invPt`,
  `invPt_image_circle`, `collinear_invPt_of_concyclic`, `radicalAxis_eq_affine`, `steiner_line_orthocenter`,
  `inversion_leftS`, `inversion_pappusCircle`, the two `peaucellier_*_line` variants, `twin_right`. These
  are listed as "—" in the tables. The concrete inversion images in `l14w_ptolemy_iff_dist_add_dist_invPt`
  and `l14w_inversion_bigS` exercise Mathlib's `inversion` on explicit points.
* Presentation choices (they do not change the meaning): `ConvexQuad` is split into its two conjuncts as
  two hypotheses, and `IsIncircle` into nine. The cross product in the Simson determinant is written as
  `⟪b 0, u⟫⟪b 1, v⟫ − ⟪b 1, u⟫⟪b 0, v⟫` for an arbitrary Mathlib `OrthonormalBasis (Fin 2) ℝ V`. The
  library's `l14_pappus_chain` bundles `pappusCircle_zero`, the three tangencies and the height formula,
  with the chain circles written out explicitly. `l14_radicalAxis_eq_mk'` was renamed to
  `l14_radicalAxis_eq_affine` because the gate's name handling cannot cope with a trailing `'`.

## Quadrilaterals (jack `~/l14i_quad`)
| main theorem | l14_ | Mathlib-only verified | l14w_ witness | non-degeneracy | notes |
|---|---|---|---|---|---|
| bretschneider | l14_bretschneider | Y (local=[]) | l14w_bretschneider: tangential quad `−2−i, 1−i, 1+i, −1/2+i` (non-cyclic) | area `9/2`; correction term `cos²((B+D)/2) = 1/10 ≠ 0` (derived from the theorem) | quadArea/semiperimeter unfolded |
| brahmagupta | l14_brahmagupta | Y | l14w_brahmagupta: `−24−7i, −25i, 24+7i, −24+7i` on `|z|=25`, sides 30,40,48,14 | area `936 = √876096`; not a rectangle or kite | |
| pitot | l14_pitot | Y | l14w_pitot: same tangential quad, incircle `(0,1)`, sides 3,2,3/2,5/2 | not a rhombus (not even a kite); both sides `9/2` | infDist + SSameSide unfolded |
| pitot_converse | l14_pitot_converse | Y | l14w_pitot_converse | adjacent sides pairwise distinct | |
| euler_quadrilateral | l14_euler_quadrilateral | Y | — (no hypotheses) | | |
| ptolemy_second | l14_ptolemy_second | Y | l14w_ptolemy_second (cyclic quad above) | both sides `5/4`, diagonals 50 ≠ 40 | |
| van_aubel | l14_van_aubel | Y | — (no hypotheses) | | quadSign/squareCenter unfolded to `if`/`Orientation.rotation` |
| newton_line | l14_newton_line | Y | l14w_newton_line (tangential quad) | midpoints `−1/2`, `1/4`, incentre `0` pairwise distinct | |
| fuss | l14_fuss | Y | l14w_fuss: rational bicentric kite (see FINDINGS) | `d = 5/7 ≠ 0`, `AB ≠ BC` (not a square), `1/r² = 49/576` | |

## CircleSystems (jack `~/l14i_circles`)
| main theorem | l14_ | Mathlib-only verified | l14w_ witness | non-degeneracy | notes |
|---|---|---|---|---|---|
| power of a point / radical axis | l14_radicalAxis_eq_inner, l14_radicalAxis_eq_affine | Y | — | | powPt, radConst, radBase unfolded |
| radical centre | l14_radical_center_concurrent | Y | l14w_radical_center_concurrent: circles `(0,1),(4,1),(4i,3)` | the unique point is `2+i` (common power 4), proved as an iff | |
| coaxal pencils | l14_pencilPow_eq_powPt, l14_pencilCenter_mem_line, l14_pencil_radicalAxis | Y | l14w_pencil_radicalAxis (`s=0,t=1/2`) | axis contains `2`, not `0` | |
| orthogonal circles | l14_isOrthogonal_iff | Y | l14w_isOrthogonal_iff: `(0,3),(5,4)`, X=`(9+12i)/5` | radii 3, 4 > 0 | |
| Johnson | l14_johnson_circle, l14_johnson_orthocenter_eq, l14_johnson_congruent | Y | l14w_johnson_circle, l14w_johnson_orthocenter_eq: H=0, centres `3+4i, −3+4i, −5i`, R=5 | intersections `−3−i, 3−i, 8i` non-collinear; Johnson centre `3i` | |
| Simson determinant | l14_simson_det_eq_circumcircle_power | Y | l14w_simson_det_eq_circumcircle_power: triangle `5, 5i, −3−4i`, P=0 | RHS `1500 ≠ 0` | cross written with inner products against Mathlib basis |
| Simson–Wallace | l14_simson_wallace | Y | l14w_simson_wallace | P=`4−3i` on circle: feet `−2−i,3−i,6−i` collinear and distinct; P=0 off circle: feet non-collinear (both directions) | feet = Mathlib orthogonalProjection, computed explicitly |
| Steiner line | l14_steiner_line, l14_steiner_line_orthocenter | Y | l14w_steiner_line: P=`−5i` | four points `2+i, −6−3i, −2−i, 10+5i` pairwise distinct | reflections computed explicitly |

## Arbelos (john `~/lean/l14i_arbelos`), witness radii a=1, b=2
| main theorem | l14_ | Mathlib-only verified | l14w_ witness | non-degeneracy | notes |
|---|---|---|---|---|---|
| twin circles | l14_twin_left, l14_twin_right | Y | l14w_twin (both twins) | radius `2/3 > 0` | centres irrational (FINDINGS) |
| arbelos_area | l14_arbelos_area | Y | l14w_arbelos_area: D = `2+2√2 i` | area `= ofReal 2 · π ≠ 0` (via Mathlib `Complex.volume_ball`) | arbelosRegion, bigS/leftS/rightS, perpC (as `AffineSubspace.mk' (2a) (ℝ∙I)`) unfolded |
| pappus_chain (+ tangencies, circle 0) | l14_pappus_chain | Y | l14w_pappus_chain | circles 1, 2 = `(12/7+12/7 i, 6/7)`, `(12/19+24/19 i, 6/19)`, heights 1 and 2 diameters, externally tangent | famCircle/famDen written out |
| pappus_unique | l14_pappus_unique | Y | l14w_pappus_unique | all hypotheses incl. `c(n+2) ≠ c n` (radii) and `0 < (c 1).im`; c 1 explicit | |
| inversion picture | l14_inversion_bigS, l14_inversion_leftS, l14_inversion_pappusCircle | Y | l14w_inversion_bigS: B=6 ↦ 2 | | Mathlib `EuclideanGeometry.inversion`; invRadius = `2√(a(a+b))` written out |
| bankoff | l14_bankoff | Y | l14w_bankoff: s₀=`(12/7+12/7 i, 6/7)`, T₁=`18/13+12/13 i`, T₂=`12/5+6/5 i`, s=`(2+2/3 i, 2/3)` | C, T₁, T₂ pairwise distinct; radius `2/3 > 0` | IsExtTangentAt witnessed via Wbtw |
| steiner_porism | l14_steiner_porism | Y | l14w_steiner_porism: concentric six-chain | s₀ = `(√3+i, 1)` differs from every chain circle | IsSteinerChain unfolded; concentric (FINDINGS) |

## Inversion (john `~/lean/l14i_inversion`)
| main theorem | l14_ | Mathlib-only verified | l14w_ witness | non-degeneracy | notes |
|---|---|---|---|---|---|
| inversion properties | l14_invPt_invPt, l14_norm_sq_invPt, l14_dist_sq_invPt, l14_invPt_image_circle | Y | — (side conditions only) | | `invPt R` → Mathlib `inversion 0 R` |
| Ptolemy via inversion | l14_ptolemy_iff_dist_add_dist_invPt, l14_collinear_invPt_of_concyclic | Y | l14w_ptolemy_iff_dist_add_dist_invPt: R²=20, images `2+i, 2, 2−i` | three distinct collinear images; `1+1=2` | |
| Ptolemy inequality | l14_ptolemy_inequality | Y | l14w_ptolemy_inequality: `3, 4i, −3` | strict: 24 < 30 | |
| Ptolemy concyclic | l14_ptolemy_concyclic | Y | l14w_ptolemy_concyclic: `8+4i, 10, 8−4i` on `|z−5|=5` | both sides 80 ≠ 0 | |
| Peaucellier–Lipkin | l14_peaucellier, l14_peaucellier_classic, l14_peaucellier_line, l14_peaucellier_classic_line | Y | l14w_peaucellier_classic (P=2, Q=8, R=4), l14w_peaucellier (P=4, Q=−2, R=√8) | P ≠ Q, A ≠ B, ‖P‖‖Q‖ = R² > 0 | irrational link lengths (FINDINGS) |
| Descartes | l14_descartes | Y | l14w_descartes: curvatures (−1, 2, 2, 3) | both sides 36 | |
| Soddy | l14_soddy | Y | l14w_soddy: (−1, 2, 2, 3, 3) in ℝ³ | both sides 81 | |
| descartes_solve / vieta | l14_descartes_solve, l14_descartes_vieta | Y | l14w_descartes_vieta: k = 2,2,3 → 15, −1 | distinct roots | descartesForm unfolded |
| Apollonian integrality | l14_apollonian_integral | Y | l14w_apollonian_integral: (−1,2,2,3) → 15 | | descartesFormZ unfolded |

## Mechanical check (grep output)
For each `l14_` theorem: `#check @name` printed with `set_option pp.fullNames true`, plus a
`run_cmd` listing `ci.type.getUsedConstants` filtered by the library namespace prefix
(scratch file outside the library). `local=[]` means no constant from the library namespace occurs in the type.
Grepping the printed types for `<NS>.` finds only the theorem names in the `#check` header lines
(`@NS.l14_…` / `NS.l14_… :`); the count of other occurrences is 0 in all four repos.
```
CONSTS Quadrilaterals.l14_bretschneider: local=[] total=61
CONSTS Quadrilaterals.l14_brahmagupta: local=[] total=57
CONSTS Quadrilaterals.l14_pitot: local=[] total=51
CONSTS Quadrilaterals.l14_pitot_converse: local=[] total=51
CONSTS Quadrilaterals.l14_euler_quadrilateral: local=[] total=49
CONSTS Quadrilaterals.l14_ptolemy_second: local=[] total=47
CONSTS Quadrilaterals.l14_van_aubel: local=[] total=104
CONSTS Quadrilaterals.l14_newton_line: local=[] total=55
CONSTS Quadrilaterals.l14_fuss: local=[] total=65
CONSTS CircleSystems.l14_radicalAxis_eq_inner: local=[] total=36
CONSTS CircleSystems.l14_radicalAxis_eq_affine: local=[] total=74
CONSTS CircleSystems.l14_radical_center_concurrent: local=[] total=40
CONSTS CircleSystems.l14_pencilPow_eq_powPt: local=[] total=49
CONSTS CircleSystems.l14_pencilCenter_mem_line: local=[] total=49
CONSTS CircleSystems.l14_pencil_radicalAxis: local=[] total=52
CONSTS CircleSystems.l14_isOrthogonal_iff: local=[] total=40
CONSTS CircleSystems.l14_johnson_circle: local=[] total=44
CONSTS CircleSystems.l14_johnson_orthocenter_eq: local=[] total=58
CONSTS CircleSystems.l14_johnson_congruent: local=[] total=24
CONSTS CircleSystems.l14_simson_det_eq_circumcircle_power: local=[] total=92
CONSTS CircleSystems.l14_simson_wallace: local=[] total=71
CONSTS CircleSystems.l14_steiner_line: local=[] total=86
CONSTS CircleSystems.l14_steiner_line_orthocenter: local=[] total=72
CONSTS Arbelos.l14_twin_left: local=[] total=61
CONSTS Arbelos.l14_twin_right: local=[] total=61
CONSTS Arbelos.l14_arbelos_area: local=[] total=89
CONSTS Arbelos.l14_pappus_chain: local=[] total=49
CONSTS Arbelos.l14_pappus_unique: local=[] total=52
CONSTS Arbelos.l14_inversion_bigS: local=[] total=62
CONSTS Arbelos.l14_inversion_leftS: local=[] total=62
CONSTS Arbelos.l14_inversion_pappusCircle: local=[] total=54
CONSTS Arbelos.l14_bankoff: local=[] total=46
CONSTS Arbelos.l14_steiner_porism: local=[] total=49
CONSTS Inversion.l14_invPt_invPt: local=[] total=19
CONSTS Inversion.l14_norm_sq_invPt: local=[] total=30
CONSTS Inversion.l14_dist_sq_invPt: local=[] total=37
CONSTS Inversion.l14_invPt_image_circle: local=[] total=47
CONSTS Inversion.l14_ptolemy_iff_dist_add_dist_invPt: local=[] total=31
CONSTS Inversion.l14_ptolemy_inequality: local=[] total=27
CONSTS Inversion.l14_collinear_invPt_of_concyclic: local=[] total=38
CONSTS Inversion.l14_ptolemy_concyclic: local=[] total=26
CONSTS Inversion.l14_peaucellier: local=[] total=42
CONSTS Inversion.l14_peaucellier_classic: local=[] total=40
CONSTS Inversion.l14_peaucellier_classic_line: local=[] total=44
CONSTS Inversion.l14_peaucellier_line: local=[] total=46
CONSTS Inversion.l14_descartes: local=[] total=37
CONSTS Inversion.l14_soddy: local=[] total=41
CONSTS Inversion.l14_descartes_solve: local=[] total=31
CONSTS Inversion.l14_descartes_vieta: local=[] total=27
CONSTS Inversion.l14_apollonian_integral: local=[] total=31
```

## Gate / tamper
```
Quadrilaterals (jack): PASS (118 declarations, standard axioms only)   [was 92]
  tamper: sorry ax2line evalfake macro wrap falsehyp falsehyp2 falsehyp3 falsestmt fusshyp fussstmt -> ALL TAMPERING TESTS REJECTED
CircleSystems (jack):  PASS (106 declarations, standard axioms only)   [was 78]
  tamper: sorry ax2line evalfake macro wrap falsehyp falsehyp2 falsehyp3 falsestmt -> ALL TAMPERING TESTS REJECTED
Arbelos (john):        PASS (115 declarations, standard axioms only)   [was 93]
  tamper: sorry ax2line evalfake macro wrap falsehyp falsehyp_ext -> ALL TAMPERING TESTS REJECTED
Inversion (john):      PASS (74 declarations, standard axioms only)
  tamper: sorry ax2line evalfake macro wrap falsehyp falsehyp2 falsehyp3 falsestmt -> ALL TAMPERING TESTS REJECTED
```
Every l14 declaration reports `[propext, Classical.choice, Quot.sound]`, except
`Inversion.l14w_apollonian_integral`, which reports `[propext, Quot.sound]` (a subset; standard).
On jack every lake build / gate / tamper ran under `flock ~/pi.lock`. john has no `flock`, so there they ran sequentially.

## Hashes
Pre-existing `.lean` files (sha256 recorded before any edit, re-checked after commit): all unchanged,
except the root file in each repo, which differs only by the one appended `import <Lib>.L14` line
(`git diff` = +1 line). Counts: quad 18/19 unchanged (+root), circles 5/6 (+root), arbelos 7/8 (+root),
inversion 4/5 (+root).
```
# l14i_quad before:
8776fcc1e870a1e6d401f4b29115c2abdcd284f733609cefd82606dbf9e75d3b  ./Quadrilaterals/Algebra.lean
3c2a8dd65ce6eb3384fac01269182b1ba43e5880792aa08e3e2a35acf12d7fff  ./Quadrilaterals/Basic.lean
df1466608b238b0eb7bf00067268fc447a2b26733b6528a299e5a1af20e0a80e  ./Quadrilaterals/Bridges.lean
6b32f1e93139a4f0b89697029d0967be5b2748548f2f07cc32faedaf69b220e1  ./Quadrilaterals/Coord.lean
2d6f93eba01a389ce8e41a8b7beacb405a487fa0b16f00aa2cec915a5024c8bb  ./Quadrilaterals/Cyclic.lean
aecf1e2175401c68ae6358674d61021cef5f7a96f0d9314892aa26ecbf9a2023  ./Quadrilaterals/Frame.lean
7442d6b0f477c43cf5ca7ab1c284bb7c40e91100998dd12e371b009f4bf94345  ./Quadrilaterals/FussAlg.lean
bf8225d1a42b4d7d1e96f8748e5627fdf27b985ce2c6d9788486a9107cce897d  ./Quadrilaterals/Fuss.lean
4cd239a7f4bcb3ea126cd18572c235d90c754da857746d1295d14a8eb8c1d71a  ./Quadrilaterals.lean
2635f19170bceb3669de95fae190396d43ae2ba1c589e99bd65b7c1801ec4050  ./Quadrilaterals/Main.lean
a1b7dc5703d63c0b701dfb16909299e9f5052cd3f4ac56cd1eac7836336f7b6c  ./scratch/B.lean
f5945a9ae03a71674145d2879eec161ca10096a802f70d01599841231e130eee  ./scratch/C2.lean
6fdf95362df8b978aee6c5a7a6f0f92272085ba232d37f46b5e6b685fe2bb9aa  ./scratch/C.lean
9c31805b41bba5ea2214f5f7ac544a07e07595dc4e22ace44c6a61333eba417d  ./scratch/E.lean
102f4c014a3e91558c31dda14c8b3afc5cb5c0b9c33e1303d79d0e205b85ac0c  ./scratch/N.lean
fd05ba0c8e539175ffb5cfe86d98a53244e71d1612c0e625c7620dacf63389d6  ./scratch/PC.lean
19c167a5080ab001900b21b6de49ea26f6cd6f5ca4ac6639fa44c04a8976affd  ./scratch/P.lean
b1bf39176c93f598fbb3386c9a31f8c2ff6f60d50ce8397c6a57c9d80e28fb76  ./scratch/T.lean
7a47c6b1e658b850664c1e32e2fa001f6d481903a63c0e5c0357a7516a2421ac  ./scratch/VA.lean
# l14i_quad after (changed/new):
b44a251e82220908488cb85f5eade0f355313d42ea45149915e9c32ffb4a60b1  Quadrilaterals.lean
3a7fa40d0c76251a5537a5144dab3e6b5cc9ed21fa69063d6e002608d73e33f9  Quadrilaterals/L14.lean
b0db578ebe83aa2401e5fb6c48a2c98dbc3b43197b72c5b8a13281015d234d08  gate.sh
# l14i_circles before:
661db8cb5a3a4c96f6598647b1e70afa890f773c1fd0f153aebd0f1321e940c6  ./CircleSystems/Coaxal.lean
2a690b88e4b06bcabc0740cabcc6e174c9efb4c6a69a7b457e32047953af3b1c  ./CircleSystems/Coord.lean
11942585e088535d61b7dfeb0c4985b1aabf9613fce07c931526eae6232a6e18  ./CircleSystems/Johnson.lean
5bc216d56cef709a822bc0c4673b223010f3d80d3fa10c31c6a28d965fdf5712  ./CircleSystems.lean
634d749617a2eb4b542ef22466b1375cfece730e37b5bbdc20320db75b4d0286  ./CircleSystems/PowerOfPoint.lean
4e02ce0848b0058b09ae10ff0cd8870a1e0b7b9ccd7073581b15dfff4ae27b42  ./CircleSystems/SimsonSteiner.lean
# l14i_circles after (changed/new):
46a51ad4bef71bfed1c8dcbea047586c276180cfb8f7ee1cba6797b92a6324b6  CircleSystems.lean
bef435c55146c508932ea68fd0e200614e9b879026e510b4753d1c37e47eafb5  CircleSystems/L14.lean
a4bcb8c82ff41021a9b2ac148819dc24a2f4032ad41075532788c00d556721a1  gate.sh
# l14i_arbelos before:
13dd3ece4babbae45a3dd8b3fdb488295fb0170b94f683cac69a6becc046277b  ./Arbelos.lean
15513196a5d978ab5fb93e1740a57710065d523289deee46a0fd31b21b58c76f  ./Arbelos/Area.lean
09ed2b3ddbe090f39e2c4af7f376d44902bf1dffe65a7731fc6f5c42dad056ea  ./Arbelos/Bankoff.lean
d6dcc9d46596e62be30fb466a8c5d0b2ca56b9433b35afadf981fd4b3b1de3a3  ./Arbelos/Basic.lean
0392e4a21196616c063e7e0fc73a8dc4790253ba9576022952a13fdc7a598b74  ./Arbelos/Inversion.lean
b64662926ed4fa87e8d44cdea3c757e257161f33a36b7014ed277885149a3383  ./Arbelos/Pappus.lean
a19659ae3b2fd99e1368d8d1a3aea698e39a4e1ae09a96642b85461e76ed5c61  ./Arbelos/Steiner.lean
bb995d95c1122731ff2662f0ce67ee75a48e8cc96bbd28ef19f2411bf4ae73d9  ./Arbelos/Twin.lean
# l14i_arbelos after (changed/new):
075c45dfc69e90c04d6dd357cb9af8688b3962dd0a660a7f9b34fce8d3952461  Arbelos.lean
d9712ccf27fe9c2211c905a78de266ce4ef422018cde263ea77a7ff57a6cea46  Arbelos/L14.lean
6539fa593f422b0acd26c98d22f0b982fcec2169f9d79c1f29ee1138389e1139  gate.sh
# l14i_inversion before:
90860a188a2bead52f053f9f35c71ed9f108b9c7a1fe54ccc33026670444432b  ./Inversion.lean
a82367f1a9fec802afc5b058d4600024fbf4f0498594c4e04157126514852129  ./Inversion/Basic.lean
0108b3aef0d8d7f69db35ab25c5cbb3e8a46a740ff6a242c2c1269f66edeef03  ./Inversion/Descartes.lean
b1afd92778f7aa5cfa276df3ce71c0cf1ad1d461f2d065772657cc3a44925af1  ./Inversion/Peaucellier.lean
8d5a503cc34fafe48ad7e9da6092fb7e85123bfeabc77db4a88af5a549510ada  ./Inversion/PtolemyInversion.lean
# l14i_inversion after (changed/new):
e8a06c2fb6f42212008f59b1b56c1a420c7a761c1e4c2478777d1bacc01bfbf2  Inversion.lean
2791291999404a506e3a6f929bf44acc42fd099e48059db5adce7d4e9b8bdbc2  Inversion/L14.lean
7ed27829ad0fd2fedb1f3ad166d661405c63441c2c99460c33fc7df443e6d4a9  gate.sh
```

## Commits (local only, not pushed; author Josh Bald <jpbald93@gmail.com>, no Co-Authored-By trailer)
| repo | commit |
|---|---|
| jack ~/l14i_quad | 12a24a66301a0fc6f028740df4db7e5ea2510e72 |
| jack ~/l14i_circles | 2f036ed2a5c64b8d99be75f392df89ad06d92c15 |
| john ~/lean/l14i_arbelos | 12beee7877cb0e59bf767735bd5b3ea65be0d79b |
| john ~/lean/l14i_inversion | 09c0761dc574c7082e3130d890a86a8900855bef |

Message: "Layer 14: Mathlib-only restatements and witnesses". L14 file sizes: Quadrilaterals 407 lines,
CircleSystems 317, Arbelos 369, Inversion 339. Sources are also copied in
`/home/work/.openclaw/tmp/paperI/l14/src/`.

DONE L14
