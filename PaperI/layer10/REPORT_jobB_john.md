# Paper I — job B (john): final commits, Layer 10 bridges, gate/tamper, battery

Host `john` (arm64 macOS, Lean v4.33.1). Work copies are `~/lean/final_arbelos` and `~/lean/final_inversion`, made with rsync (`--exclude .lake`) from the l14i clones. In both, `.lake/packages` is a symlink to `/Users/john/lean/paperi_arbelos/.lake/packages`, the same target the l14i clones use. `.lake/build` was copied from the l14i clones to avoid a full rebuild. All Lean runs were serial, and no other Lean process was running at any check.

No `sorry`, `admit`, `axiom` or `native_decide` was added. The gate's forbidden-token scan passed on all sources.

---

## paperi_arbelos → `~/lean/final_arbelos`

**Final commit: `0dddc6e05fc14ad3d25325aecfc1ca225837ae6b`** (working tree clean)

| commit | subject | numstat |
|---|---|---|
| `6c3c3bc3d56955f7e18a7511285da59392b06e2f` | Layer 14/15: simple and disjoint Steiner chains; Bankoff circle existence | Bankoff.lean +47/-0, Steiner.lean +186/-0, gate.sh +1/-0 |
| `0dddc6e05fc14ad3d25325aecfc1ca225837ae6b` | Layer 10: definition bridges; Bankoff centre | Arbelos.lean +1/-0, Bankoff.lean +3/-2, Bridge.lean +213/-0, gate.sh +1/-0 |

Parent is `12beee7` (Layer 14). Both commits are authored and committed by `Josh Bald <jpbald93@gmail.com>` via `git -c`. There is no Co-Authored-By line and no config change.

- Commit 1 holds the uncommitted Layer-15 additions, byte-identical to `~/lean/l14i_arbelos` (checked with `cmp`). It also adds a `gate.sh` line that puts the 12 Layer-15 names on `REQUIRED`: `bankoff_exists IsSimpleSteinerChain HasDisjointDiscs IsDisjointSteinerChain hasDisjointDiscs_iff rotSphere_injective invSphere_inj invSphere_sep steiner_concentric_strong steiner_porism_strong steiner_porism_simple steiner_porism_disjoint`. The gate passed at this commit: `PASS (127 declarations, standard axioms only)`.
- Commit 2 contains the Step-2 change, the bridge file, one root import (`import Arbelos.Bridge`) and one `REQUIRED="$REQUIRED …"` line listing the 11 bridge names.

### Bankoff statement (Step 2): the only statement change

Before (`bankoff_exists`, conclusion):
```lean
    ∃ s : Sphere ℂ, ptC a b ∈ s ∧ T₁ ∈ s ∧ T₂ ∈ s ∧ s.radius = a * b / (a + b) := by
```
After:
```lean
    ∃ s : Sphere ℂ, ptC a b ∈ s ∧ T₁ ∈ s ∧ T₂ ∈ s ∧ s.radius = a * b / (a + b) ∧
      s.center = ⟨2 * a, a * b / (a + b)⟩ := by
```
The centre is written in the library's own frame, `ℂ` with the anonymous constructor `⟨re, im⟩`, i.e. `2a + i·ab/(a+b)`. The proof closes with `rfl` off the existing witness: `…, ?_, ?_, ?_, rfl⟩` became `…, ?_, ?_, ?_, rfl, rfl⟩`. Hypotheses are unchanged. No downstream file used `bankoff_exists`, so nothing else changed.

**Was `-0` kept everywhere else?** Yes. `git diff --numstat 12beee7 HEAD` gives Arbelos.lean 1/0, Bankoff.lean 48/0 net (+47/-0 in commit 1, then +3/-2 in commit 2), Bridge.lean 213/0, Steiner.lean 186/0 and gate.sh 2/0. The only 2 deleted lines are the two Bankoff lines shown above (statement line and `refine` line).

### Layer 10 bridges (`Arbelos/Bridge.lean`): 11 proved, 0 dropped

| lemma | ties | to |
|---|---|---|
| `bridge_vline` | `vline x₀` | the set `{z \| z.re = x₀}` |
| `bridge_perpC` | `perpC a b` | `{z \| z.re = 2a}` |
| `bridge_arbelos_area` | `volume (arbelosRegion a b)` (MeasureTheory Lebesgue measure on ℂ) | `ofReal (π(a+b)²/2 − πa²/2 − πb²/2)`, the classical "big half disc minus two small half discs" |
| `bridge_twin_radius` | `ab/(a+b)` | `1/(1/a+1/b)`, the classical twin radius |
| `bridge_twin_left` / `bridge_twin_right` | twin predicates + `twin_*_exists` | existence **and** radius `ab/(a+b)` in one statement |
| `bankoff_center` | any circle through `C, T₁, T₂` | centre `⟨2a, ab/(a+b)⟩` **and** radius `ab/(a+b)` (strengthens `bankoff`, which gives only the radius) |
| `bridge_bankoff` | Bankoff circle | the classical circle (centre `2a + i·ab/(a+b)`, radius `ab/(a+b)`): it contains `C, T₁, T₂`, and every circle through them equals it |
| `bridge_isSteinerChain_iff` | `IsSteinerChain` | centre-distance tangency to both boundary circles and between consecutive circles (`dist = r+r'`, `dist = R−r`) |
| `bridge_powC` | `powC c s` | Mathlib `Sphere.power s c` |
| `bridge_exists_inversion_concentric` | `exists_inversion_concentric` (via `invSphere`) | Mathlib `EuclideanGeometry.inversion c 1`: images `inversion c 1 '' S₁ = T₁`, `'' S₂ = T₂` with `T₁.center = T₂.center`, positivity stated with `Sphere.power` |

### Gate, tamper, battery

- Gate: `PASS (138 declarations, standard axioms only)`
- Tamper: `7 of 7 rejected` (sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp_ext): `ALL TAMPERING TESTS REJECTED`
- Battery report: `~/leancheck/reports/final_arbelos_20261110_161255.md` (log `.log` alongside). HEAD `0dddc6e…`, 0 uncommitted entries.

| check | result |
|---|---|
| gate (layer 1) | PASS (138 declarations, standard axioms only) |
| tamper (layer 2) | 7/7 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 9 of 9 files ok |
| conclusion mutations (layer 4) | **317/321 rejected** (312 by error, 5 by timeout/heartbeat); 4 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 82 probed ok — no-hyp 33 |
| satisfiability (layer 8) | 77/115 certified [46 with hypotheses, 21 hypothesis-free binders, 10 closed], 37 unresolved, 1 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b) | 0 theorems linked; 0 rejected claims; layer 8 + 8b: 77/115 credited, 38 unresolved |
| hypothesis ablation (layer 6) | 197 needed, **1 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 9 files |
| linter, scratch (layer 7) | 0 warnings in 1 files |
| bridge inventory (layer 9) | 23 notions, 2 has-bridge, 21 NO-BRIDGE |

Battery findings, from the report:
- Unused hypothesis: `steiner_porism (hs₀ : 0 < s₀.radius)`. This is pre-existing: the same line 308 is in canonical `paperi_arbelos` @ 53d0573. I left it alone because this job allows only the Bankoff statement change.
- Mutation survivors: `l14w_twin` ×3 and `twin_left_exists` ×1. All four are in pre-existing statements, none in the bridges.
- `l14h_mem_sphere` is stmt-invalid in layer 8. This is pre-existing (L14 helper).

---

## paperi_inversion → `~/lean/final_inversion`

**Final commit: `c71abb76b265d660ae2d73b629beac2c338c8b27`**, `Layer 10: definition bridges`. Parent is `09c0761`. Authored and committed by `Josh Bald <jpbald93@gmail.com>`. Working tree clean.

Numstat: Inversion.lean +1/-0 (`import Inversion.Bridge`), Inversion/Bridge.lean +161/-0, gate.sh +1/-0 (a `REQUIRED="$REQUIRED …"` line with the 10 bridge names). **`-0` held everywhere.** There is no Bankoff change in this repo.

### Layer 10 bridges (`Inversion/Bridge.lean`): 10 proved, 0 dropped

| lemma | ties | to |
|---|---|---|
| `bridge_invPt` | `invPt R` (as a function, any real inner-product space) | `EuclideanGeometry.inversion 0 R` (`funext`) |
| `bridge_invPt_bijOn` | `invPt R`, `R ≠ 0`, on the punctured space `{0}ᶜ` | `EqOn` Mathlib `inversion 0 R` **and** `BijOn {0}ᶜ {0}ᶜ` (it is an involution there) |
| `bridge_extTangent` | signed tangency `dist² = (r₁+r₂)²` with `r₁, r₂ > 0` | Mathlib `Sphere.IsExtTangent` |
| `bridge_intTangent` | signed tangency with enclosing circle `r₂ < 0`, `r₁ ≤ −r₂` | Mathlib `Sphere.IsIntTangent ⟨c₁,r₁⟩ ⟨c₂,−r₂⟩` |
| `bridge_descartesForm` | `descartesForm = 0` | `(∑kᵢ)² = 2∑kᵢ²` |
| `bridge_isDescartes` | `IsDescartes (a,b,c,d)` over ℤ | the classical real relation on the casts |
| `bridge_descartes_classical` | Descartes' theorem for four mutually **Mathlib-`IsExtTangent`** circles | `k₄ = k₁+k₂+k₃ ± 2√(k₁k₂+k₂k₃+k₃k₁)` with `kᵢ = 1/rᵢ` |
| `bridge_apolloMove` | `apolloMove 3` | the other root of the Descartes quadratic (Vieta sum `2(a+b+c)`), still Descartes |
| `bridge_cross_iff_collinear` | the coordinate condition `P.re*Q.im − P.im*Q.re = 0` | Mathlib `Collinear ℝ {0, P, Q}` |
| `bridge_peaucellier_collinear` | Peaucellier–Lipkin hypotheses | `Collinear ℝ {0, P, Q}` (pivot and the two rhombus vertices) |

Mathlib has a `Sphere.IsTangent` for a sphere and an affine subspace. The inversion library has no sphere-to-line tangency predicate of its own, so nothing needed bridging there.

### Gate, tamper, battery

- Gate: `PASS (84 declarations, standard axioms only)`
- Tamper: `9 of 9 rejected` (sorry, ax2line, evalfake, macro, wrap, falsehyp, falsehyp2, falsehyp3, falsestmt): `ALL TAMPERING TESTS REJECTED`
- Battery report: `~/leancheck/reports/final_inversion_20261110_172039.md`. HEAD `c71abb7…`, 0 uncommitted entries.

| check | result |
|---|---|
| gate (layer 1) | PASS (84 declarations, standard axioms only) |
| tamper (layer 2) | 9/9 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 6 of 6 files ok |
| conclusion mutations (layer 4) | **268/272 rejected** (268 by error, 0 by timeout/heartbeat); 4 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 57 probed ok — no-hyp 30 |
| satisfiability (layer 8) | 55/87 certified [21 with hypotheses, 25 hypothesis-free binders, 9 closed], 32 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b) | 0 theorems linked; 0 rejected claims; layer 8 + 8b: 55/87 credited, 32 unresolved |
| hypothesis ablation (layer 6) | 256 needed, **1 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 6 files |
| linter, scratch (layer 7) | 0 warnings in 1 files |
| bridge inventory (layer 9) | 10 notions, 1 has-bridge, 9 NO-BRIDGE |

Battery findings:
- Unused hypothesis: `bridge_intTangent (h₂ : r₂ < 0)`. This is in **my new lemma**. It is redundant because it follows from `0 < r₁` and `r₁ ≤ −r₂`; I kept it to document the signed-radius convention. It is not wrong and makes nothing vacuous, but it could be deleted (a strengthening) in a follow-up. I did not redo the commit and the hour-long battery inside the time box.
- Mutation survivors: `l14w_ptolemy_inequality` ×3 and `l14w_apollonian_integral` ×1. Both are pre-existing L14 witnesses.

---

## sha256

```
ebfc04c342e6afac3663fd6e8f3756cb454c8593f69af5c36574132177b3ee58  final_arbelos/Arbelos/Bridge.lean
dd8a16f9abda65d23e856273fd6f23f06552b6589f0603defa1468f55d35202e  final_inversion/Inversion/Bridge.lean
e118f6eed44e821d1b7ef52d7782adc536ebd1117afdfdb6e2b205eb712f3c21  final_arbelos/Arbelos/Bankoff.lean
```
(computed with `shasum -a 256` on john at the final commits)

## Deviations / notes

1. **Battery path.** `runall.sh` resolves repos as `$HOME/<repo>`, not `$HOME/lean/<repo>` (`cd "$HOME/$REPO"`). Following the existing house convention on john (`~/Blundon -> ~/lean/Blundon`, `~/paperh_mordell -> …`), I created the symlinks `~/final_arbelos -> ~/lean/final_arbelos` and `~/final_inversion -> ~/lean/final_inversion`. The reports therefore show path `/Users/john/final_<repo>`, which is the same repo.
2. **Arbelos commit split.** I used two commits. The Layer-15 commit also carries one `gate.sh` line adding the 12 Layer-15 names to `REQUIRED`, so the gate covers them at both commits.
3. **Gate style.** New names are added with an appended line `REQUIRED="$REQUIRED …"` directly after the existing `REQUIRED=` line, rather than by editing that long line. This keeps the diff `-0`. The tamper `wrap` test still finds and rewrites the original `REQUIRED="` line (7/7 and 9/9 rejected).
4. **Layer 9 is a heuristic.** The inventory still reports "NO-BRIDGE" for most notions because it only spots name-pattern bridges such as `<notion>_eq` / `mem_<notion>_iff`, not `bridge_*` lemmas. The bridges listed above exist and are gated.
5. **Not bridged.** These were judged internal helpers or concrete data, not "notions": the inversion `private` determinant/dot helpers (`det3`, `dot`, `triple`, `det3g`, `det4g`) and the arbelos coordinates `ptA/ptB/bigS/leftS/rightS/famCircle/rotSphere/l14wChain`. All candidates on the job list were proved; none were dropped.
6. **Time.** About 2.5 h wall-clock, of which the two batteries took about 68 min (arbelos) and 62 min (inversion). Bridging finished well inside the 150-minute cap.
