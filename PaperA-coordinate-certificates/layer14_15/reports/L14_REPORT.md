# Paper A (CoordCertificates) — Layer 14: Mathlib-only restatements + witnesses

Started 2026-10-21 21:54 EDT on john. Status: COMPLETE — 6/6 main theorems restated Mathlib-only with witnesses; 5/5 gates PASS; 5/5 tamper ALL REJECTED; no findings against the paper.

## Setup
* Fresh `git clone` of github.com/jpbald93/{desargues,monge,simson,napoleon,lami} into
  `~/lean/l14A_<repo>`, checked out at the paper's pinned commits:
  desargues b6409255c844, monge a01f7504d12f, simson 7c239b31600, napoleon e16592ae04be,
  lami ea6b038b1a3e (all verified with `git rev-parse HEAD`).
* All five: `lean-toolchain` = leanprover/lean4:v4.33.1, Mathlib rev
  0df444a360eaa60ab8c11dca51a86af692955474 → `.lake/packages` symlinked to
  `~/lean/clifford/.lake/packages`. No `lake update` / cache get.
* **Note (tooling, not a math finding):** `gate.sh` at the pinned commits calls
  `mktemp --suffix=.lean -p .` (GNU-only). Under the wrapper's default BSD mode the gate fails at
  "axiom report" (`mktemp: unrecognized option --suffix`) after a successful build. All gates were
  therefore run as `~/lean/jl -g gate` / `jl -g tamper` (wrapper's GNU mode). This matches the
  paper's availability paragraph (later commits made the scripts BSD-portable; the pinned commits
  are the Lean sources).

## Main theorems (paper theorem environments)
| Paper | decl | repo |
|---|---|---|
| Thm desdet | Desargues.desargues_det | desargues |
| Thm desmk | Desargues.desargues_mk | desargues |
| Thm monge | Monge.monge | monge |
| Thm simson | Simson.simson | simson |
| Thm napoleon | Napoleon.napoleon_outer (+ napoleon_inner) | napoleon |
| Thm lami | Lami.lami_nondegenerate | lami |


## Per-repo results

### desargues (`Desargues/L14.lean`)
| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| desargues_det (Thm desdet) | `l14_desargues_det` | yes (0 hits) | `l14w_desargues_det` | both triangles non-degenerate (`det ≠ 0`); the three Desargues points computed as (-2,-15,0), (-4,-39,-4), (2,-12,-12), pairwise non-proportional (cross product ≠ 0) | `br` replaced by `Matrix.det (Matrix.of ![…])` and Mathlib `⨯₃` |
| desargues_mk (Thm desmk) | `l14_desargues` | yes (0 hits) | `l14w_desargues` | points pinned by `.submodule = ℚ ∙ v`; all 12 hypotheses; both triangles `¬IsCollinear`; O ≠ each of 6 vertices; A≠A', B≠B', C≠C'; 3 Desargues points pairwise distinct in ℙ²; conclusion via `l14_desargues` | statement quantifies over **points of `ℙ K (Fin 3 → K)`**, not representatives; perspective is `IsCollinear {O,A,A'}`, sides/meets are `Projectivization.cross` |

Bridges: `l14b_mk_ne`, `l14b_ne_zero`, `l14b_cross_ne_zero` (computational helpers), plus the library's `br_eq_det`, `br_eq_zero_of_isCollinear_mk`, `cross_mk_of_ne` (Mathlib).
Restatement matches the paper exactly: same 6 vertex inequalities + 3 side inequalities; the
representative hypotheses `a ≠ 0` disappear (they are built into `ℙ`), and `br o a a' = 0`
becomes Mathlib `IsCollinear`. No extra hypothesis was needed.

### monge (`Monge/L14.lean`)
| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| monge (Thm monge) | `l14_monge` (+ `l14_monge_homothety`) | yes (0 hits) | `l14w_monge` | centres (0,0),(4,0),(0,3) `¬Collinear`; radii 1,2,3 distinct; S₁₂=(-4,0), S₂₃=(12,-6), S₃₁=(0,-3/2) pairwise distinct and satisfy the defining property; conclusion via `l14_monge` | centre of similitude by defining property `r₁•(O₂-ᵥS) = r₂•(O₁-ᵥS)`; homothety variant needs radii ≠ 0 (inherent: homothety ratio r₂/r₁) |

Bridge: `l14b_ext_unique` (a point with the defining property equals the library `ext`, for r₁ ≠ r₂); library `det3_eq_zero_iff_collinear`.
Note: the paper's statement allows radii in an arbitrary field incl. 0 / negative; the
defining-property form `l14_monge` keeps exactly the paper's hypotheses (r_i pairwise distinct).
The homothety form `l14_monge_homothety` adds r_i ≠ 0, which is needed only for the ratio r₂/r₁
to be meaningful — not a weakening of the main restatement.

### simson (`Simson/L14.lean`)
| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| simson (Thm simson) | `l14_simson` (+ `l14_simson_feet`) | yes (0 hits) | `l14w_simson` | a=5, b=3+4i, c=-4+3i, p=-5i on |z|=5 (Cospherical with centre 0, radius 5); `¬Collinear {a,b,c}`; p ≠ each vertex; feet computed: -6/5+17/5 i, 2+i, 6-2i, pairwise distinct; conclusion via `l14_simson` | feet = `EuclideanGeometry.orthogonalProjection line[ℝ,·,·] p`; `_feet` variant gives feet by defining property (on line, `inner ℝ (p - F) (v - u) = 0`) |

Bridges: `l14b_foot` (defining property ⇒ orthogonal projection), `l14b_norm_eq`, `l14b_not_collinear`; library `perpFoot_eq_orthogonalProjection`.

### napoleon (`Napoleon/L14.lean`)
| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| napoleon_outer (Thm napoleon) | `l14_napoleon_outer` | yes (0 hits) | `l14w_napoleon` | A=0, B=2, C=2i; outward apexes Xa=(1+√3)(1+i), Xb=-√3+i, Xc=1-√3i satisfy equal-side + `SOppSide`; Napoleon centres (1+√3/3)(1+i), -√3/3+i, 1-(√3/3)i computed via Mathlib `Finset.centroid`, pairwise distinct; conclusion via `l14_napoleon_outer` | apexes by defining property (equilateral + strictly opposite side of the base from the 3rd vertex); centres = `Finset.univ.centroid ℝ ![…]` |
| napoleon_inner | `l14_napoleon_inner` | yes (0 hits) | (none separate) | — | `SSameSide` version; no separate witness written (time) |

Bridges: `l14b_apex_opp` / `l14b_apex_same` (property-defined apex = library `apex ωo` if ABC is
ccw, `apex ωi` if cw — so the Mathlib statement needs **no orientation hypothesis**, it combines
`napoleon_outer` and `napoleon_inner`), `l14b_equilateral`, side-sign lemmas (adapted from the
L14D Lester template), `l14b_centroid`.
Observation (not a finding against the paper): the paper's `napoleon_outer` is "outer" only for a
ccw triangle (`apex_outward`); for a cw triangle the library's `ωo` apexes are inward. The
Mathlib-only statement with the geometric "outward" property is true for both orientations,
since both Napoleon triangles are equilateral; the paper already says this.

### lami (`Lami/L14.lean`)
| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| lami_nondegenerate (Thm lami) | `l14_lami` | yes (0 hits) | `l14w_lami` | forces 3, 4i, -3-4i in ℂ: pairwise distinct, all nonzero, ∠(F₁,F₂)=π/2 (≠0,≠π); common ratio computed = 5 | library statement was already Mathlib-only; restated verbatim |
| lami_oriented | `l14_lami_oriented` | yes (0 hits) | (shares no separate witness) | — | oriented ratio form, `Orientation.oangle` |

No bridges needed.

## FINDINGS
* **No Mathlib-only restatement turned out false or in need of an extra hypothesis.** All six
  main theorems restate with exactly the paper's hypotheses (Desargues ℙ²: the `≠ 0` representative
  hypotheses are absorbed by `ℙ`; Napoleon: the Mathlib form even drops the implicit orientation).
* Tooling: pinned-commit `gate.sh` requires GNU `mktemp --suffix` (BSD mode fails at "axiom
  report"; build itself succeeds). Ran with `jl -g`. Consistent with the paper's statement that a
  later commit fixed BSD portability.
* Minor coverage gaps: no dedicated witness for `l14_napoleon_inner`, `l14_lami_oriented`,
  `l14_monge_homothety`, `l14_simson_feet` (secondary forms; the main forms all have witnesses).

## Mechanical namespace check
Scratch files (`~/lean/l14A_scratch/<repo>.check_{types,explicit}.lean`, set_option only there):
`import <Lib>`, `set_option pp.fullNames true`, `pp.proofs true`, `pp.fieldNotation false`,
`#check @<Lib>.<l14 name>`; second pass additionally `pp.explicit true` (shows all implicit and
instance arguments). The declaration name itself is stripped before grepping for `<Lib>.`:

| repo | default pass hits | pp.explicit pass hits (lines) |
|---|---|---|
| desargues | 0 | 0 (4031 lines) |
| monge | 0 | 0 (883) |
| simson | 0 | 0 (3811) |
| napoleon | 0 | 0 (2525) |
| lami | 0 | 0 (405) |

Type-check output (default pass) is in the appendix.

## Gate before → after (`~/lean/jl -g gate`)
| repo | before | after |
|---|---|---|
| desargues | PASS (24 declarations) | PASS (31 declarations) |
| monge | PASS (7) | PASS (11) |
| simson | PASS (12) | PASS (18) |
| napoleon | PASS (21) | PASS (41) |
| lami | PASS (17) | PASS (20) |
All "standard axioms only" ([propext, Classical.choice, Quot.sound]).

## REQUIRED added (only the REQUIRED= line of gate.sh changed)
* desargues: l14_desargues_det l14_desargues l14b_mk_ne l14b_ne_zero l14b_cross_ne_zero l14w_desargues_det l14w_desargues
* monge: l14b_ext_unique l14_monge l14_monge_homothety l14w_monge
* simson: l14_simson l14b_foot l14_simson_feet l14b_norm_eq l14b_not_collinear l14w_simson
* napoleon: l14b_cross_eq l14b_mem_line_of_cross l14b_sign_neg l14b_sign_pos l14b_cross_of_sOppSide l14b_cross_of_sSameSide l14b_equilateral l14b_cross_apex l14b_ne_of_sOppSide l14b_ne_of_sSameSide l14b_apex_opp l14b_apex_same l14b_cross_cyclic l14_napoleon_outer l14_napoleon_inner l14b_dist_eq l14b_notMem_line l14b_oppSide l14b_centroid l14w_napoleon
* lami: l14_lami l14_lami_oriented l14w_lami

## Tamper (`~/lean/jl -g tamper`)
All 5 repos: `ALL TAMPERING TESTS REJECTED` (6 tests each: sorry, ax2line, evalfake, macro →
FAIL: forbidden token; falsehyp → FAIL: build; wrap → FAIL: nonstandard axioms). Logs:
`~/lean/l14A_<repo>.tamper.log`.

## Hashes
`git diff --numstat` per repo: exactly `1 0 <Lib>.lean` (one appended `import <Lib>.L14`) and
`1 1 gate.sh` (REQUIRED line). Untracked: only `<Lib>/L14.lean`. sha256 of every other
pre-existing `.lean` file is identical to the fresh clone (diff of `shasum -a 256` lists shows
only the root file changed).

Pre-existing files (fresh clone, sha256):

desargues:
```
94b087f2ff5d54ec2fd2a0db0119f21ee61efe358a0468f6b244dd2ad23fcf38  ./Desargues.lean
8eb210482ceb5ee97f9104b8e4e7bb63ae1eff7a12f968dc6d0c56563569bae8  ./Desargues/Basic.lean
2e45e4677757f92f656e29664969a192b10bfd4e0785ca8b4cfc0214935bd784  ./Desargues/Bridge.lean
b9cf1756987a7c967185116484d2477084c50a59c18bc7518ea40d056e932fab  ./Desargues/Examples.lean
bea8c802295339ed22e9453cc5db9b42b736b6ba33e54c82acbe88bc2d4bb341  ./Desargues/Main.lean
89249b1530a13e8c6b0dc1bda7dfd7456c9cc2c9063bd0299cf6c6c81f981cda  ./Desargues/Plane.lean
6435d16fa588edc08d7e8f0a70a179f2e0b5f6b44119645278af19cdb09c04cd  ./scratch/Ax.lean
c2737330bb15f8cc244de78e8e4d6b3745be6f034aa8f8e3ecae37e3af451af1  ./scratch/probe.lean
```
new file: cc9a638b4cbadbd6cc2055e8f854e96922c63784e076676cf0258d091485e560  Desargues/L14.lean

monge:
```
f14f723be188eecc41dc5a9403bac07248756282acfb079a7c58c7ab43400bff  ./Monge.lean
dc59f1c3d86680bc06c307e6ca25bd8636f8fa8da92765b5daf62993caf88484  ./Monge/Basic.lean
b32c8a52815d705dee894123a3f9e2381dc42353c7d71bff3f286e24260ff8b5  ./Monge/Bridge.lean
813537ca7c56f97afb8db680a4d99cfc6e47e5acfa80111e83bbf5e72e6121d5  ./scratch/Ax.lean
```
new file: 4ebbf749f493ef7597904342c5f8c966f9ebe1981d77495a9fe0d491aab81084  Monge/L14.lean

simson:
```
257b79adfd1c64ccc96da8d272ff01d5b659d634bc3c0261e97fe1f805995116  ./Simson.lean
a9d7180281ad12389f2a907e5433bc8247b13efe713070cfbe36b6d0682a64c5  ./Simson/Basic.lean
8fa41750a292760162936c8ddb2b5d79f67afef5fc2e6c229a8293e417c1dff8  ./Simson/Bridge.lean
23af76e601cab8f4401837deac3152c2577cfbac86609146088c2d156beb7e3a  ./Simson/Identity.lean
e2955b5d1c414a58c3ae2fd8d834a201af974f469f05d679ba02de71dd3ae134  ./Simson/Main.lean
b5d5862652626aa432829be16a3e21b617d603c55e96e45015da82a419eafeac  ./scratch/Ax.lean
```
new file: cf32580f2f1eba9ecb51de7c8bbe889be28286060bee7791993f8cb16ce81718  Simson/L14.lean

napoleon:
```
60d7f152537cf50950fb29d8057856fd0230d140ddc927c0b14c65032fb1cdb6  ./Napoleon.lean
b241be8bccfe7841f682da2b4a9eea74872e108b84a238b1d8f71b981a89c534  ./Napoleon/Basic.lean
f12ac6337b1a5f78622e7f0d6ce2d33f905e2ed60fd569b9d435c307052b1920  ./Napoleon/Bridge.lean
357545610fa675abe60910dd4ae42ed94bc07485fa32348dec4d8a6fb68baa8b  ./scratch/Ax.lean
```
new file: 56770a1ca995efbf867002d28abb72e35384d773d38f48487c46b800bfe82fbc  Napoleon/L14.lean

lami:
```
5f8e89e269d706211094e3726a68146ce3211a1acd866450def6f5f925f4b76a  ./AxCheck.lean
b73b09d6475edf77db5aa799c428e38a13394edee5f64ecfec06db104b0a0e1a  ./Lami.lean
cca0cae5e1c6b679d44efae104fdb7f2558811c8208c96ace82379ae9a5b7d45  ./Lami/Basic.lean
```
new file: 5e117b786d38b106798be55ce14f4723e9d7a8b80eb860ed28a379a352160283  Lami/L14.lean

Root files after (one line appended): Desargues.lean 8b483cf6…, Monge.lean 17f7e4bb…,
Simson.lean 0cc47209…, Napoleon.lean f97b8416…, Lami.lean de50e643….

Nothing committed, nothing pushed.

## Wall time
21:54 → 22:20 EDT, about 26 minutes (well inside the 2.5 h time box). Logs: `~/lean/l14A_<repo>.{gate_before,gate_after,tamper,types,types_explicit}.log`. Scratch check files are in `~/lean/l14A_scratch/` (moved out of the repos so the trees hold only L14.lean + 2 one-line edits).

## Appendix: type-check output (pp.fullNames, pp.fieldNotation false)

### desargues
```
@Desargues.l14_desargues_det : ∀ {K : Type u_1} [inst : Field K] {o a b c a' b' c' : Fin 3 → K},
  o ≠ 0 →
    Matrix.det (Matrix.of ![o, a, a']) = 0 →
      Matrix.det (Matrix.of ![o, b, b']) = 0 →
        Matrix.det (Matrix.of ![o, c, c']) = 0 →
          Matrix.det
              (Matrix.of
                ![(crossProduct ((crossProduct a) b)) ((crossProduct a') b'),
                  (crossProduct ((crossProduct b) c)) ((crossProduct b') c'),
                  (crossProduct ((crossProduct c) a)) ((crossProduct c') a')]) =
            0
@Desargues.l14_desargues : ∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K]
  {O A B C A' B' C' : Projectivization K (Fin 3 → K)},
  A ≠ B →
    B ≠ C →
      C ≠ A →
        A' ≠ B' →
          B' ≠ C' →
            C' ≠ A' →
              Projectivization.IsCollinear {O, A, A'} →
                Projectivization.IsCollinear {O, B, B'} →
                  Projectivization.IsCollinear {O, C, C'} →
                    Projectivization.cross A B ≠ Projectivization.cross A' B' →
                      Projectivization.cross B C ≠ Projectivization.cross B' C' →
                        Projectivization.cross C A ≠ Projectivization.cross C' A' →
                          Projectivization.IsCollinear
                            {Projectivization.cross (Projectivization.cross A B) (Projectivization.cross A' B'),
                              Projectivization.cross (Projectivization.cross B C) (Projectivization.cross B' C'),
                              Projectivization.cross (Projectivization.cross C A) (Projectivization.cross C' A')}
Desargues.l14w_desargues_det : have o := ![0, 0, 1];
have a := ![1, 0, 0];
have b := ![0, 1, 0];
have c := ![1, 1, 1];
have a' := ![2, 0, 3];
have b' := ![0, 5, -1];
have c' := ![4, 4, 11];
(o ≠ 0 ∧
    Matrix.det (Matrix.of ![o, a, a']) = 0 ∧
      Matrix.det (Matrix.of ![o, b, b']) = 0 ∧ Matrix.det (Matrix.of ![o, c, c']) = 0) ∧
  Matrix.det (Matrix.of ![a, b, c]) ≠ 0 ∧
    Matrix.det (Matrix.of ![a', b', c']) ≠ 0 ∧
      (crossProduct ((crossProduct a) b)) ((crossProduct a') b') = ![-2, -15, 0] ∧
        (crossProduct ((crossProduct b) c)) ((crossProduct b') c') = ![-4, -39, -4] ∧
          (crossProduct ((crossProduct c) a)) ((crossProduct c') a') = ![2, -12, -12] ∧
            (crossProduct ![-2, -15, 0]) ![-4, -39, -4] ≠ 0 ∧
              (crossProduct ![-4, -39, -4]) ![2, -12, -12] ≠ 0 ∧
                (crossProduct ![2, -12, -12]) ![-2, -15, 0] ≠ 0 ∧
                  Matrix.det
                      (Matrix.of
                        ![(crossProduct ((crossProduct a) b)) ((crossProduct a') b'),
                          (crossProduct ((crossProduct b) c)) ((crossProduct b') c'),
                          (crossProduct ((crossProduct c) a)) ((crossProduct c') a')]) =
                    0
Desargues.l14w_desargues : ∃ O A B C A' B' C',
  Projectivization.submodule O = ℚ ∙ ![0, 0, 1] ∧
    Projectivization.submodule A = ℚ ∙ ![1, 0, 0] ∧
      Projectivization.submodule B = ℚ ∙ ![0, 1, 0] ∧
        Projectivization.submodule C = ℚ ∙ ![1, 1, 1] ∧
          Projectivization.submodule A' = ℚ ∙ ![2, 0, 3] ∧
            Projectivization.submodule B' = ℚ ∙ ![0, 5, -1] ∧
              Projectivization.submodule C' = ℚ ∙ ![4, 4, 11] ∧
                (A ≠ B ∧
                    B ≠ C ∧
                      C ≠ A ∧
                        A' ≠ B' ∧
                          B' ≠ C' ∧
                            C' ≠ A' ∧
                              Projectivization.IsCollinear {O, A, A'} ∧
                                Projectivization.IsCollinear {O, B, B'} ∧
                                  Projectivization.IsCollinear {O, C, C'} ∧
                                    Projectivization.cross A B ≠ Projectivization.cross A' B' ∧
                                      Projectivization.cross B C ≠ Projectivization.cross B' C' ∧
                                        Projectivization.cross C A ≠ Projectivization.cross C' A') ∧
                  ¬Projectivization.IsCollinear {A, B, C} ∧
                    ¬Projectivization.IsCollinear {A', B', C'} ∧
                      O ≠ A ∧
                        O ≠ B ∧
                          O ≠ C ∧
                            O ≠ A' ∧
                              O ≠ B' ∧
                                O ≠ C' ∧
                                  A ≠ A' ∧
                                    B ≠ B' ∧
                                      C ≠ C' ∧
                                        Projectivization.cross (Projectivization.cross A B)
                                              (Projectivization.cross A' B') ≠
                                            Projectivization.cross (Projectivization.cross B C)
                                              (Projectivization.cross B' C') ∧
                                          Projectivization.cross (Projectivization.cross B C)
                                                (Projectivization.cross B' C') ≠
                                              Projectivization.cross (Projectivization.cross C A)
                                                (Projectivization.cross C' A') ∧
                                            Projectivization.cross (Projectivization.cross C A)
                                                  (Projectivization.cross C' A') ≠
                                                Projectivization.cross (Projectivization.cross A B)
                                                  (Projectivization.cross A' B') ∧
                                              Projectivization.IsCollinear
                                                {Projectivization.cross (Projectivization.cross A B)
                                                    (Projectivization.cross A' B'),
                                                  Projectivization.cross (Projectivization.cross B C)
                                                    (Projectivization.cross B' C'),
                                                  Projectivization.cross (Projectivization.cross C A)
                                                    (Projectivization.cross C' A')}
```

### monge
```
@Monge.l14_monge : ∀ {K : Type u_1} [inst : Field K] (O₁ O₂ O₃ S₁₂ S₂₃ S₃₁ : K × K) (r₁ r₂ r₃ : K),
  r₁ ≠ r₂ →
    r₂ ≠ r₃ →
      r₃ ≠ r₁ →
        r₁ • (O₂ -ᵥ S₁₂) = r₂ • (O₁ -ᵥ S₁₂) →
          r₂ • (O₃ -ᵥ S₂₃) = r₃ • (O₂ -ᵥ S₂₃) → r₃ • (O₁ -ᵥ S₃₁) = r₁ • (O₃ -ᵥ S₃₁) → Collinear K {S₁₂, S₂₃, S₃₁}
@Monge.l14_monge_homothety : ∀ {K : Type u_1} [inst : Field K] (O₁ O₂ O₃ S₁₂ S₂₃ S₃₁ : K × K) (r₁ r₂ r₃ : K),
  r₁ ≠ 0 →
    r₂ ≠ 0 →
      r₃ ≠ 0 →
        r₁ ≠ r₂ →
          r₂ ≠ r₃ →
            r₃ ≠ r₁ →
              (AffineMap.homothety S₁₂ (r₂ / r₁)) O₁ = O₂ →
                (AffineMap.homothety S₂₃ (r₃ / r₂)) O₂ = O₃ →
                  (AffineMap.homothety S₃₁ (r₁ / r₃)) O₃ = O₁ → Collinear K {S₁₂, S₂₃, S₃₁}
Monge.l14w_monge : (1 ≠ 2 ∧ 2 ≠ 3 ∧ 3 ≠ 1) ∧
  1 • ((4, 0) -ᵥ (-4, 0)) = 2 • ((0, 0) -ᵥ (-4, 0)) ∧
    2 • ((0, 3) -ᵥ (12, -6)) = 3 • ((4, 0) -ᵥ (12, -6)) ∧
      3 • ((0, 0) -ᵥ (0, -3 / 2)) = 1 • ((0, 3) -ᵥ (0, -3 / 2)) ∧
        ¬Collinear ℚ {(0, 0), (4, 0), (0, 3)} ∧
          ((-4, 0) ≠ (12, -6) ∧ (12, -6) ≠ (0, -3 / 2) ∧ (0, -3 / 2) ≠ (-4, 0)) ∧
            Collinear ℚ {(-4, 0), (12, -6), (0, -3 / 2)}
```

### simson
```
@Simson.l14_simson : ∀ {a b c p : ℂ},
  a ≠ b →
    b ≠ c →
      c ≠ a →
        EuclideanGeometry.Cospherical {a, b, c, p} →
          Collinear ℝ
            {↑((EuclideanGeometry.orthogonalProjection line[ℝ, b, c]) p),
              ↑((EuclideanGeometry.orthogonalProjection line[ℝ, c, a]) p),
              ↑((EuclideanGeometry.orthogonalProjection line[ℝ, a, b]) p)}
@Simson.l14_simson_feet : ∀ {a b c p Fa Fb Fc : ℂ},
  a ≠ b →
    b ≠ c →
      c ≠ a →
        EuclideanGeometry.Cospherical {a, b, c, p} →
          Fa ∈ line[ℝ, b, c] ∧ Inner.inner ℝ (p - Fa) (c - b) = 0 →
            Fb ∈ line[ℝ, c, a] ∧ Inner.inner ℝ (p - Fb) (a - c) = 0 →
              Fc ∈ line[ℝ, a, b] ∧ Inner.inner ℝ (p - Fc) (b - a) = 0 → Collinear ℝ {Fa, Fb, Fc}
Simson.l14w_simson : (5 ≠ 3 + 4 * Complex.I ∧
    3 + 4 * Complex.I ≠ -4 + 3 * Complex.I ∧
      -4 + 3 * Complex.I ≠ 5 ∧
        EuclideanGeometry.Cospherical {5, 3 + 4 * Complex.I, -4 + 3 * Complex.I, -5 * Complex.I}) ∧
  ¬Collinear ℝ {5, 3 + 4 * Complex.I, -4 + 3 * Complex.I} ∧
    -5 * Complex.I ≠ 5 ∧
      -5 * Complex.I ≠ 3 + 4 * Complex.I ∧
        -5 * Complex.I ≠ -4 + 3 * Complex.I ∧
          ↑((EuclideanGeometry.orthogonalProjection line[ℝ, 3 + 4 * Complex.I, -4 + 3 * Complex.I]) (-5 * Complex.I)) =
              -6 / 5 + 17 / 5 * Complex.I ∧
            ↑((EuclideanGeometry.orthogonalProjection line[ℝ, -4 + 3 * Complex.I, 5]) (-5 * Complex.I)) =
                2 + Complex.I ∧
              ↑((EuclideanGeometry.orthogonalProjection line[ℝ, 5, 3 + 4 * Complex.I]) (-5 * Complex.I)) =
                  6 - 2 * Complex.I ∧
                -6 / 5 + 17 / 5 * Complex.I ≠ 2 + Complex.I ∧
                  2 + Complex.I ≠ 6 - 2 * Complex.I ∧
                    6 - 2 * Complex.I ≠ -6 / 5 + 17 / 5 * Complex.I ∧
                      Collinear ℝ
                        {↑((EuclideanGeometry.orthogonalProjection line[ℝ, 3 + 4 * Complex.I, -4 + 3 * Complex.I])
                              (-5 * Complex.I)),
                          ↑((EuclideanGeometry.orthogonalProjection line[ℝ, -4 + 3 * Complex.I, 5]) (-5 * Complex.I)),
                          ↑((EuclideanGeometry.orthogonalProjection line[ℝ, 5, 3 + 4 * Complex.I]) (-5 * Complex.I))}
```

### napoleon
```
@Napoleon.l14_napoleon_outer : ∀ {A B C Xa Xb Xc : ℂ},
  Dist.dist Xa B = Dist.dist B C ∧ Dist.dist Xa C = Dist.dist B C ∧ AffineSubspace.SOppSide line[ℝ, B, C] Xa A →
    Dist.dist Xb C = Dist.dist C A ∧ Dist.dist Xb A = Dist.dist C A ∧ AffineSubspace.SOppSide line[ℝ, C, A] Xb B →
      Dist.dist Xc A = Dist.dist A B ∧ Dist.dist Xc B = Dist.dist A B ∧ AffineSubspace.SOppSide line[ℝ, A, B] Xc C →
        Dist.dist (Finset.centroid ℝ Finset.univ ![B, C, Xa]) (Finset.centroid ℝ Finset.univ ![C, A, Xb]) =
            Dist.dist (Finset.centroid ℝ Finset.univ ![C, A, Xb]) (Finset.centroid ℝ Finset.univ ![A, B, Xc]) ∧
          Dist.dist (Finset.centroid ℝ Finset.univ ![C, A, Xb]) (Finset.centroid ℝ Finset.univ ![A, B, Xc]) =
            Dist.dist (Finset.centroid ℝ Finset.univ ![A, B, Xc]) (Finset.centroid ℝ Finset.univ ![B, C, Xa])
@Napoleon.l14_napoleon_inner : ∀ {A B C Xa Xb Xc : ℂ},
  Dist.dist Xa B = Dist.dist B C ∧ Dist.dist Xa C = Dist.dist B C ∧ AffineSubspace.SSameSide line[ℝ, B, C] Xa A →
    Dist.dist Xb C = Dist.dist C A ∧ Dist.dist Xb A = Dist.dist C A ∧ AffineSubspace.SSameSide line[ℝ, C, A] Xb B →
      Dist.dist Xc A = Dist.dist A B ∧ Dist.dist Xc B = Dist.dist A B ∧ AffineSubspace.SSameSide line[ℝ, A, B] Xc C →
        Dist.dist (Finset.centroid ℝ Finset.univ ![B, C, Xa]) (Finset.centroid ℝ Finset.univ ![C, A, Xb]) =
            Dist.dist (Finset.centroid ℝ Finset.univ ![C, A, Xb]) (Finset.centroid ℝ Finset.univ ![A, B, Xc]) ∧
          Dist.dist (Finset.centroid ℝ Finset.univ ![C, A, Xb]) (Finset.centroid ℝ Finset.univ ![A, B, Xc]) =
            Dist.dist (Finset.centroid ℝ Finset.univ ![A, B, Xc]) (Finset.centroid ℝ Finset.univ ![B, C, Xa])
Napoleon.l14w_napoleon : have A := 0;
have B := 2;
have C := { re := 0, im := 2 };
have Xa := { re := 1 + √3, im := 1 + √3 };
have Xb := { re := -√3, im := 1 };
have Xc := { re := 1, im := -√3 };
(Dist.dist Xa B = Dist.dist B C ∧ Dist.dist Xa C = Dist.dist B C ∧ AffineSubspace.SOppSide line[ℝ, B, C] Xa A) ∧
  (Dist.dist Xb C = Dist.dist C A ∧ Dist.dist Xb A = Dist.dist C A ∧ AffineSubspace.SOppSide line[ℝ, C, A] Xb B) ∧
    (Dist.dist Xc A = Dist.dist A B ∧ Dist.dist Xc B = Dist.dist A B ∧ AffineSubspace.SOppSide line[ℝ, A, B] Xc C) ∧
      Finset.centroid ℝ Finset.univ ![B, C, Xa] = { re := 1 + √3 / 3, im := 1 + √3 / 3 } ∧
        Finset.centroid ℝ Finset.univ ![C, A, Xb] = { re := -(√3 / 3), im := 1 } ∧
          Finset.centroid ℝ Finset.univ ![A, B, Xc] = { re := 1, im := -(√3 / 3) } ∧
            Finset.centroid ℝ Finset.univ ![B, C, Xa] ≠ Finset.centroid ℝ Finset.univ ![C, A, Xb] ∧
              Finset.centroid ℝ Finset.univ ![C, A, Xb] ≠ Finset.centroid ℝ Finset.univ ![A, B, Xc] ∧
                Finset.centroid ℝ Finset.univ ![A, B, Xc] ≠ Finset.centroid ℝ Finset.univ ![B, C, Xa] ∧
                  Dist.dist (Finset.centroid ℝ Finset.univ ![B, C, Xa]) (Finset.centroid ℝ Finset.univ ![C, A, Xb]) =
                      Dist.dist (Finset.centroid ℝ Finset.univ ![C, A, Xb])
                        (Finset.centroid ℝ Finset.univ ![A, B, Xc]) ∧
                    Dist.dist (Finset.centroid ℝ Finset.univ ![C, A, Xb]) (Finset.centroid ℝ Finset.univ ![A, B, Xc]) =
                      Dist.dist (Finset.centroid ℝ Finset.univ ![A, B, Xc]) (Finset.centroid ℝ Finset.univ ![B, C, Xa])
```

### lami
```
@Lami.l14_lami : ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] {F₁ F₂ F₃ : V},
  F₁ + F₂ + F₃ = 0 →
    F₁ ≠ 0 →
      F₂ ≠ 0 →
        F₃ ≠ 0 →
          InnerProductGeometry.angle F₁ F₂ ≠ 0 →
            InnerProductGeometry.angle F₁ F₂ ≠ Real.pi →
              (Real.sin (InnerProductGeometry.angle F₂ F₃) ≠ 0 ∧
                  Real.sin (InnerProductGeometry.angle F₃ F₁) ≠ 0 ∧ Real.sin (InnerProductGeometry.angle F₁ F₂) ≠ 0) ∧
                ‖F₁‖ / Real.sin (InnerProductGeometry.angle F₂ F₃) =
                    ‖F₂‖ / Real.sin (InnerProductGeometry.angle F₃ F₁) ∧
                  ‖F₂‖ / Real.sin (InnerProductGeometry.angle F₃ F₁) =
                    ‖F₃‖ / Real.sin (InnerProductGeometry.angle F₁ F₂)
@Lami.l14_lami_oriented : ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
  [inst_2 : Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) {F₁ F₂ F₃ : V},
  F₁ + F₂ + F₃ = 0 →
    F₁ ≠ 0 →
      F₂ ≠ 0 →
        F₃ ≠ 0 →
          ‖F₁‖ / Real.Angle.sin (Orientation.oangle o F₂ F₃) = ‖F₂‖ / Real.Angle.sin (Orientation.oangle o F₃ F₁) ∧
            ‖F₂‖ / Real.Angle.sin (Orientation.oangle o F₃ F₁) = ‖F₃‖ / Real.Angle.sin (Orientation.oangle o F₁ F₂)
Lami.l14w_lami : (3 + 4 * Complex.I + (-3 - 4 * Complex.I) = 0 ∧
    3 ≠ 0 ∧
      4 * Complex.I ≠ 0 ∧
        -3 - 4 * Complex.I ≠ 0 ∧
          InnerProductGeometry.angle 3 (4 * Complex.I) ≠ 0 ∧ InnerProductGeometry.angle 3 (4 * Complex.I) ≠ Real.pi) ∧
  (3 ≠ 4 * Complex.I ∧ 4 * Complex.I ≠ -3 - 4 * Complex.I ∧ -3 - 4 * Complex.I ≠ 3) ∧
    InnerProductGeometry.angle 3 (4 * Complex.I) = Real.pi / 2 ∧
      ‖-3 - 4 * Complex.I‖ / Real.sin (InnerProductGeometry.angle 3 (4 * Complex.I)) = 5 ∧
        ‖3‖ / Real.sin (InnerProductGeometry.angle (4 * Complex.I) (-3 - 4 * Complex.I)) = 5 ∧
          ‖4 * Complex.I‖ / Real.sin (InnerProductGeometry.angle (-3 - 4 * Complex.I) 3) = 5
```
