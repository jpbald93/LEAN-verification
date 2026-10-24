# Paper C — Layer 14 report (Mathlib-only restatements + witnesses)

Started 2026-10-21 21:40 EDT, local clock. STATUS: COMPLETE.
All work was done inline: no subagents. Nothing was committed or pushed.

## Sources
| repo | pinned commit (paper preamble) | toolchain | Mathlib rev (lake-manifest) | packages |
|---|---|---|---|---|
| jpbald93/barbier | 7baae0430954ce78ddf8d6e6bf5a4b841d7b2367 | v4.33.1 | 0df444a360eaa60ab8c11dca51a86af692955474 | symlink → ~/lean/clifford/.lake/packages |
| jpbald93/fourvertex | 14d10449dd1a206f5342099d65d5f4180830d423 | v4.33.1 | 0df444a360eaa60ab8c11dca51a86af692955474 | symlink → ~/lean/clifford/.lake/packages |

Each repo was freshly cloned into john:~/lean/l14C_barbier and john:~/lean/l14C_fourvertex and checked out at its pinned commit. Neither `lake update` nor any cache download was run.

## Changes per repo
- New file: `Barbier/L14.lean` (sha256 0add7ccd1a76799cbd3be28585f9ed85993ef6a8dba847b25586125ed62afcec) and `FourVertex/L14.lean` (sha256 ac7b7250a03400dd269b4c4a24ef138d13f9390df3d00e036940b104e889988d).
- Root file: one line appended at the end (`import Barbier.L14` / `import FourVertex.L14`).
- gate.sh: only the `REQUIRED=` line changed (git diff: 1 line removed, 1 added).
- The L14 files contain no sorry/admit/axiom/native_decide/#eval/set_option/macro/notation/run_cmd, and the gate's token filter passes them.

## Repo barbier — per theorem
"namespace-free" means: the pretty-printed type (pp.fullNames) contains no `Barbier` token, and `Expr.getUsedConstants` of the type, filtered by prefix `Barbier`, is `[]`.

| paper theorem | l14 | namespace-free | witness | distinctness / non-degeneracy | notes |
|---|---|---|---|---|---|
| Thm 3.1 Barbier, smooth (`Barbier.barbier`) | `l14_barbier` | yes ([]) | `l14w_barbier`: h = 2 + cos(3θ)/4, w = 4 | h(0) ≠ h(π/3), so the curve is not a circle; γ(0) ≠ γ(π); π·4 > 0 | Conclusion strengthened: the perimeter integral = πw AND Mathlib `eVariationOn` length over [0,2π] = ofReal(πw) |
| Prop 3.2 smooth ⇒ piecewise (`ConstWidthSupport.toPiecewise`) | `l14_toPiecewise` | yes | `l14w_barbier` (same hypotheses) | as above | The conclusion is the five piecewise fields written out |
| Thm 3.3 Barbier, with corners (`barbier_piecewise`) | `l14_barbier_piecewise` | yes | `l14w_reuleaux` (w = 1) | R is ¬C² (so this case is genuinely beyond the smooth theorem); the three corners are pairwise distinct | The perimeter is ∫₀^{2π}‖deriv γ‖, with Lean junk values for deriv; the paper says this explicitly |
| Thm 4.1 Reuleaux (a)–(f) | `l14_reuleaux` (all six parts in one statement) | yes | `l14w_reuleaux` | γ(0), γ(2π/3), γ(4π/3) pairwise ≠; γ(0), γ(2π/3) ∈ body | R is given by its DEFINING equation (toIcoMod reduction, two branches), not by `Barbier.reuleaux` |
| Thm 5.1 length of C¹ curve (`length_eq_integral_norm_deriv`) | `l14_length` | yes (the library statement was already Mathlib-only) | `l14w_length`: γ(t) = t on [0,1] | γ(0) ≠ γ(1); the integral is 1 | re-export |
| Cor 5.2 perimeter is length | `l14_perimeter_eq_eVariationOn` | yes | `l14w_barbier` | as above | Added the clause `eVariationOn ≠ ⊤` (finiteness), so the toReal does not hide ∞ |
| Thm 5.3 the body (convex; (a)–(d)) | `l14_body` | yes | `l14w_reuleaux` | body membership of two distinct corners | Body written as ⋂ θ {z ∣ Re(z e^{-iθ}) ≤ h θ}; support values via sSup and IsGreatest, as in the library |
| Thm 5.4 the body is a convex body | `l14_convexBody`, `l14_reuleaux_convexBody` | yes | `l14w_reuleaux` | as above | Mathlib `ConvexBody ℂ`; IsCompact; Nonempty |

Bridges, proved by rfl or structure eta: `l14b_curve`, `l14b_perimeter`, `l14b_body`, `l14b_constWidth`, `l14b_piecewise`, `l14b_piecewise_iff`, `l14b_reuleaux` (defining equation ⇒ R = `reuleaux w`, via funext), `l14b_contDiff_curve` (curve is C¹ when h is C²; a public copy of a private library lemma).

## Repo fourvertex — per theorem
| paper theorem | l14 | namespace-free | witness | distinctness / non-degeneracy | notes |
|---|---|---|---|---|---|
| Lemma 6.1 Sturm–Hurwitz (`eq_zero_or_fourSignChanges`) | `l14_sturm` | yes | `l14w_sturm`: g(t) = 6 sin 2t | g(π/4) = 6 ≠ 0, so the "g ≡ 0" branch is excluded | The four-sign-change pattern is written out |
| Thm 6.2 radius form | `l14_radius` | yes | `l14w_oval` (h = 5 + cos 2θ) | ρ is non-constant (1/ρ(0) ≠ 1/ρ(π/2)) | ρ is written as h + h'' |
| Thm 6.3 four-vertex for ovals (`four_vertex`) | `l14_four_vertex` | yes | `l14w_oval` | curvature non-constant ⇒ the four-extrema branch is the live one; c₁<c₂<c₃<c₄ forces the points to be distinct | |
| Thm 7.1 curvature and simplicity (a)(b)(c) | `l14_curv` | yes | `l14w_oval` | γ(0) ≠ γ(π/2) | Signed curvature Im(conj γ'·γ'')/‖γ'‖³ is written out |
| Thm 7.2 four-vertex, textbook form | `l14_four_vertex_signedCurvature` | yes | `l14w_oval` (proves the extrema conclusion for the oval explicitly) | κ(0) ≠ κ(π/2); the four parameters are strictly ordered within one period | Also includes InjOn of γ on [0,2π), i.e. "simple closed curve" |

Bridges, all rfl/Iff.rfl: `l14b_radius`, `l14b_curve`, `l14b_signedCurvature`, `l14b_fourSignChanges`.

## FINDINGS
- **No Mathlib-only restatement was FALSE or needed an extra hypothesis.** Every main theorem was restated with exactly the paper's hypotheses and proved from the library theorem through rfl-level bridges.
- (Observation, not a defect) The Barbier "perimeter" is ∫‖deriv γ‖. Here `deriv` is Lean's total derivative, which is 0 where γ is not differentiable. For the piecewise class (Thm 3.3, Reuleaux (b)) the Mathlib-only statement is therefore about this integral, not about Mathlib length. Only for the Reuleaux triangle is `eVariationOn` length proved (part (f)); the general piecewise perimeter = length is open, as the paper's §limits already says.
- (Observation) Thm 5.1 (`Barbier.length_eq_integral_norm_deriv`) already had a namespace-free type, so its l14 is a re-export.
- Coverage: all theorem/proposition/lemma/corollary environments of paperc.tex are covered (8 in barbier, 5 in fourvertex). The paper also names helper/bridge declarations (`bridge_FourVertices`, `bridge_FourSignChanges`, `bridge_oval`, `trefoil_perimeter`, …). These are bridges or examples, not main theorems, and were not separately restated.

## Type-check output (mechanical namespace check)
Scratch files: john:~/lean/l14C_scratch/CheckB.lean and CheckF.lean. They are outside the repos; set_option and run_cmd appear only there. Each runs `#check @<name>` with pp.fullNames and pp.proofs, and a `run_cmd` that prints `type.getUsedConstants` filtered by the repo namespace prefix.
- Both runs: rc = 0, 0 errors.
- USEDCONST: `[]` for all 12 barbier and 7 fourvertex l14/l14w theorems.
- grep for `Barbier|FourVertex` in the printed types, after stripping each declaration's own name header: 0 hits, in both files.
- Full output: L14L15/C/typecheck_output.txt (581 lines; CheckB.out sha256 35d389fe39507d18498477d41a3d779f2bf6ce8cf74e64412e4092de3551f23d, CheckF.out sha256 580dd49429c9df693c1c8a3be1f5de1cd4f5a8064f03c789fc6865b92aad57ca).

## Gate before → after
- barbier: PASS (62 declarations, standard axioms only) → PASS (82 declarations, standard axioms only)
- fourvertex: PASS (48 declarations, standard axioms only) → PASS (59 declarations, standard axioms only)

## REQUIRED added
- barbier (+20): Barbier.l14b_curve l14b_perimeter l14b_body l14b_constWidth l14b_piecewise l14b_piecewise_iff l14b_reuleaux l14b_contDiff_curve l14_barbier l14_toPiecewise l14_barbier_piecewise l14_reuleaux l14_length l14_perimeter_eq_eVariationOn l14_body l14_convexBody l14_reuleaux_convexBody l14w_barbier l14w_reuleaux l14w_length
- fourvertex (+11): FourVertex.l14b_radius l14b_curve l14b_signedCurvature l14b_fourSignChanges l14_sturm l14_radius l14_four_vertex l14_curv l14_four_vertex_signedCurvature l14w_sturm l14w_oval

## Tamper (run after the L14 changes)
- barbier: sorry, ax2line, evalfake, macro, falsehyp, wrap → each rejected; **ALL TAMPERING TESTS REJECTED** (rc=0)
- fourvertex: sorry, ax2line, evalfake, macro, falsehyp, wrap → each rejected; **ALL TAMPERING TESTS REJECTED** (rc=0)

## Hashes (pre-existing .lean files, fresh clone vs after)
`shasum -a 256 -c` against the fresh-clone list: every pre-existing file is OK except the root file, which differs only by the appended import (git diff shows exactly `+import Barbier.L14` / `+import FourVertex.L14`).
barbier (fresh clone):
```
3b3e0c9b28b615054306c0ed57f66eeb228cd2dcf68b7f4e403ba54a7d454e33  ./Barbier.lean   (root; changed by the 1 import line only)
020d752eff5cd9b727e5ca690ebda4d0d3705a7f8d3c2033f712dea74e05ccef  ./Barbier/Arclen.lean
19135dcb6f225bced220c63f1378d9fc76c07d9b71932a30b08d8d95840a7082  ./Barbier/ArclenFinite.lean
7732afa0bbfc454538a32178b0d8ef2b2728154b8710c8dc7bdb8c542d3ccd98  ./Barbier/Basic.lean
b3bfda483e795b8d242042ffa2e698bb5625fecd5c6829b5dcb6138de96137b1  ./Barbier/Bridge.lean
90b7b22d22bd1bdc681824e29fa72dedf9011ad040290f6fa7ad77151b4b916d  ./Barbier/BridgePiecewise.lean
0034be9474c244360f4c25b24666cbb68a112f2f6ea88b1cf1d9cba725a72afa  ./Barbier/ConvexBodyBridge.lean
1ff02ddb985150d7ee87703c02f06f2734f27232840998378353a10882148407  ./Barbier/Examples.lean
36650d1a5a16d1245b9062266898c33acb0da36c75efcd8cb64b75f6fa3dc69b  ./Barbier/Piecewise.lean
48aa7fd90a919d3e7483cb14af5fbd57b2c1d98d88bd0e7f83986990f0c155fd  ./Barbier/Reuleaux.lean
a9856c24d758caff7a40c62fccd345b7ccfc7c10b1093eacb1c9477699e4f59a  ./Barbier/ReuleauxLength.lean
825ee63a1bb93c9453ee749b7d19857e8bdfd04b13446c31b6d46f0a8f1b6155  ./scratch/Ax.lean
```
fourvertex (fresh clone):
```
50873ec8633fb57a7b07aa7eb2b1c7119248e1a045e729d82ac9dfe4b18006a3  ./FourVertex.lean   (root; changed by the 1 import line only)
7978f1087d65d9e89efd9814c7688b59a0679dad14a14a448cfcc34ba873c3cb  ./FourVertex/Basic.lean
a0143bd9e7818475cea5a4f49bdb06d864433ce4be5b219663e9c2d27d3d7ae8  ./FourVertex/Bridge.lean
c5c1a82e28bbdd7a3b7cb4d95393e4a4444a051c724848f53631b17e774768c1  ./FourVertex/Curvature.lean
b46a536332697d95ad618707de5aa74876a9100509e841d70d0ece5b5ed611a0  ./FourVertex/Examples.lean
b0f85836e1303d4a2e4ca9e1f1eeb9dbdf8b09ae71a903e28f34b23c3c160d40  ./FourVertex/Support.lean
a48c2a38e6e5f0c370627195d4237b148b87154338889ed09b9fd8499549996d  ./FourVertex/Vertices.lean
90810f07fc31502909d8f43d312ff6ac1225059f0077a662a994f85c4f8c99a1  ./scratch/Ax.lean
```

## Wall time
Started 21:40 EDT; restatements + witnesses + gates + type check finished by 21:52; tamper finished at 21:53 EDT. Total about 13 min (time box 2.5 h).
