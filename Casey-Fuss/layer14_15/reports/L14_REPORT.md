# PAPER CaseyFuss — Layer 14 report (Mathlib-only restatement + witnesses)

Machine: jack (jack). Started 2026-10-21 22:27 EDT, finished 22:41 EDT (**wall time ≈ 14 min**).
All work done inline. No subagents or background tasks were used, apart from the two `tests/tamper.sh` runs, which ran under nohup and were waited on by PID. Nothing was committed or pushed.

## Sources
| repo | URL | pinned commit (paper `\commit…`) | clone dir | toolchain | Mathlib rev |
|---|---|---|---|---|---|
| casey | https://github.com/jpbald93/casey | a83c43b8d7c8b1b98c213366cfa27eec8b8ad6c3 | ~/l14CaseyFuss_casey | v4.33.1 | 0df444a360eaa60ab8c11dca51a86af692955474 |
| fuss | https://github.com/jpbald93/fuss | 671efdc610147022ef66e9794988ba72114f85a4 | ~/l14CaseyFuss_fuss | v4.33.1 | 0df444a360eaa60ab8c11dca51a86af692955474 |

Both repos match the expected toolchain and Mathlib, so `.lake/packages` is a symlink to `~/barbier/.lake/packages`. No `lake update` or `cache get` was run.
(The paper's line references point at casey `5f6252c`, but its `\commitcasey` macro pins `a83c43b`. `a83c43b` is the child of `5f6252c` and adds `Casey/Bridge.lean`, so the pinned commit `a83c43b` was used.)

## Repo casey — new file `Casey/L14.lean`
| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Casey.casey / Casey.casey_of_le (Thm 1/2) | `l14_casey` | yes (0 hits) | `l14w_casey` | 4 circles pairwise ≠, each ≠ Γ, r₁>0; T₁..T₄ pairwise ≠; all six tangent-length radicands positive (24,12,4,8,32,12) | Circles are Mathlib `Sphere`s with `C.IsIntTangentAt Γ T` (Mathlib's internal tangency) instead of `tangentCentre`. The tangent length is written out explicitly as `√(dist cᵢ cⱼ² − (rᵢ−rⱼ)²)`, because Mathlib has `commonExtTangents` but no tangent-*length* notion. No extra hypothesis is needed: `IsIntTangentAt` forces 0 ≤ r ≤ R, which is slightly *more* general than `casey` (r<R). |
| Casey.casey_zero_radii_eq_ptolemy (Cor 3) | `l14_casey_ptolemy` | yes | covered by `l14w_casey` config (T's on Γ, p=0) | — | Zero-radius case stated with `Tᵢ ∈ Γ` for `Γ : Sphere P`. |

Witness (ℂ): Γ = (0, 5). C₁=(4,1), C₂=(3i,2), C₃=(−2,3), C₄=(−i,4), tangent at 5, 5i, −5, −5i, with p = 0. The diagonals are proved to give `∠ = π` via `Sbtw`. The witness also proves the conclusion by applying `l14_casey`.
Bridge: `l14_center_of_isIntTangentAt` (`IsIntTangentAt` ⇒ `C.center = tangentCentre Γ.center T Γ.radius C.radius ∧ C.radius ≤ Γ.radius`). Helpers: `l14_dist_eq`, `l14_dist_sq`, `l14_wbtw`.
**Partial coverage:** the external-tangency (signed r<0) reading of `casey_of_le` is *not* restated with Mathlib's `IsExtTangentAt`. Doing so needs mixed internal/external tangent lengths √(d²−(rᵢ±rⱼ)²), and I did not attempt it. `l14_casey` covers the internally tangent case, which is Theorem 1 of the paper.

Gate: before `PASS (18 declarations, standard axioms only)` → after `PASS (25 declarations, standard axioms only)`.
Tamper: sorry, ax2line, evalfake, macro, falsehyp, wrap all rejected → `ALL TAMPERING TESTS REJECTED`.
REQUIRED added (7): Casey.l14_center_of_isIntTangentAt Casey.l14_casey Casey.l14_casey_ptolemy Casey.l14_dist_eq Casey.l14_dist_sq Casey.l14_wbtw Casey.l14w_casey
Changes to existing files: `Casey.lean` +1 line (`import Casey.L14` at the end); `gate.sh` has only the REQUIRED line changed (git diff numstat 1/1).

## Repo fuss — new file `Fuss/L14.lean`
| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Fuss.fuss_of_isBicentric (Thm 4) | `l14_fuss` | yes | `l14w_fuss` | A,B,C,D pairwise ≠ (all 6 pairs); Γ.center ≠ ω.center; Γ ≠ ω | `IsBicentric` unfolded into `∈ Sphere`, ≠, `ω.IsTangent line[ℝ,·,·]`. Bridge `l14_isBicentric_iff` (Iff.rfl). |
| Fuss.poncelet_chain_closes (Thm 5) | `l14_poncelet_chain_closes` | yes (the original type already was) | `l14w_poncelet_chain_closes` | consecutive Tᵢ, Aᵢ ≠ as required, plus A₀≠A₂, A₁≠A₃, T₀≠T₂, T₁≠T₃, non-concentric | Chain A,B,C,D,A over the explicit kite; the conclusion is obtained from the theorem. |
| Fuss.exists_bicentric_of_fuss (Thm 6) | `l14_exists_bicentric` | yes | `l14w_exists_bicentric` | non-concentric; the output quadrilateral is pairwise distinct by statement | Same hypotheses as the paper (d+r<R, Fuss's relation). |
| Fuss.fuss_iff_exists / fuss_iff_forall / exists_iff_forall (Cor 7) | `l14_fuss_iff_exists`, `l14_fuss_iff_forall`, `l14_exists_iff_forall` | yes | `l14w_fuss_iff` | For (Γ, ω) both sides hold, via an explicit kite. For (Γ, ω′ = (0,1)), also inside Γ, Fuss's relation fails and **no** bicentric quadrilateral exists. So neither side is constant. ω ≠ ω′, Γ non-concentric. | — |
| Fuss.fuss_iff_reciprocal (Prop 8) | `l14_fuss_iff_reciprocal` | yes (pure ℝ) | `l14w_fuss_iff_reciprocal` | (R,d,r)=(7,1,24/5) satisfies both sides; r=1 satisfies neither | — |
| Fuss.nonvacuous (Prop 9) | (already a Mathlib-only ∃ statement) | — | superseded by `l14w_exists_bicentric` / `l14w_fuss` | — | `l14w_fuss` exhibits an *explicit* bicentric quadrilateral. |

Witness configuration (ℂ, rational): Γ = (1, 7), ω = (0, 24/5), so d = 1 and d+r = 29/5 < 7, and (49−1)² = 2304 = 2·(24/5)²·50.
Kite: A = 8, B = −24/25 + 168/25 i, C = −6, D = −24/25 − 168/25 i. Tangency points: T_AB = 72/25+96/25 i, T_BC = −96/25+72/25 i, T_CD = −96/25−72/25 i, T_DA = 72/25−96/25 i.
Each vertex is proved to lie on Γ and on the two `ω.orthRadius` tangent lines. Tangency of the side lines then follows from the repo lemma `Fuss.isTangent_of_mem_orthRadius` (proofs only; it does not appear in any type).
Bridges/helpers: `l14_isBicentric_iff`, `l14_dist_eq`, `l14_inner`, `l14_mem_orthRadius`, `l14_mem_Γ`, `l14_mem_ω`, `l14_orth_ω`, `l14_dist_Γω`, `l14_fuss_rel`, `l14_inside`, `l14_ne`, `l14_kite`, `l14_kite_ne`, `l14_kite_tangent`. Witness data defs: `l14Γ l14ω l14ω' l14A l14B l14C l14D l14TAB l14TBC l14TCD l14TDA`. These defs appear only in helper lemmas, never in the type of any `l14_*`/`l14w_*` theorem: `l14w_fuss_iff` was rewritten to existentials for exactly this reason.

Gate: before `PASS (34 declarations, standard axioms only)` → after `PASS (71 declarations, standard axioms only)`.
Tamper: sorry, ax2line, evalfake, macro, falsehyp, wrap all rejected → `ALL TAMPERING TESTS REJECTED`.
REQUIRED added (37): Fuss.l14_isBicentric_iff Fuss.l14_fuss Fuss.l14_poncelet_chain_closes Fuss.l14_exists_bicentric Fuss.l14_fuss_iff_exists Fuss.l14_fuss_iff_forall Fuss.l14_exists_iff_forall Fuss.l14_fuss_iff_reciprocal Fuss.l14_dist_eq Fuss.l14_inner Fuss.l14_mem_orthRadius Fuss.l14Γ Fuss.l14ω Fuss.l14_mem_Γ Fuss.l14_mem_ω Fuss.l14_orth_ω Fuss.l14_dist_Γω Fuss.l14_fuss_rel Fuss.l14_inside Fuss.l14A Fuss.l14B Fuss.l14C Fuss.l14D Fuss.l14TAB Fuss.l14TBC Fuss.l14TCD Fuss.l14TDA Fuss.l14_ne Fuss.l14_kite Fuss.l14_kite_ne Fuss.l14_kite_tangent Fuss.l14w_fuss Fuss.l14w_poncelet_chain_closes Fuss.l14w_exists_bicentric Fuss.l14ω' Fuss.l14w_fuss_iff Fuss.l14w_fuss_iff_reciprocal
Changes to existing files: `Fuss.lean` +1 line (`import Fuss.L14` at the end); `gate.sh` has only the REQUIRED line changed.

## FINDINGS
- **None of the "false / needs an extra hypothesis" kind.** Every Mathlib-only restatement follows from the library theorem with no added hypothesis.
- Observation (casey): with Mathlib's `IsIntTangentAt`, the restatement automatically covers r = R (C = Γ) and r = 0 (point circles). It is consistent with `casey_of_le`.
- Observation (casey, coverage): the signed-radius/external-tangency reading (Thm 2, r<0) was not restated with Mathlib's tangency notions (see above).
- Observation (fuss): the kite witness is in fact convex, with tangency points inside the side segments (T_AB at parameter 4/7 along AB). This is **not** proved in Lean, in line with the paper's "What is not claimed".

## Mechanical type check (scratch, `set_option pp.fullNames true`)
Files: ~/l14CaseyFuss_scratch/{casey,fuss}_types.lean → .out. Check: delete the `@Casey.l14… :` / `@Fuss.l14… :` header of each `#check`, then `grep -c Casey` / `grep -c Fuss` → **0 / 0**. The only hits are the 3 and 12 declaration names themselves. No errors.
Full outputs are appended below.

## Hashes (sha256, fresh clone vs final)
`sha256sum -c` against the pre-change list: every pre-existing file is OK except `Casey.lean`/`Fuss.lean` (+1 import line) and `gate.sh` (REQUIRED line), as permitted. Pre-existing library files unchanged:
```
e7aca8d2d02a424cf805c70c00f227142f89decf14bd65c59a401f0e8f57f5ac  ./Casey/Basic.lean
2afb9042653a1a050e4ae1661ca567e1017b2321d8216924ed7fe9a48cacacf4  ./Casey/Bridge.lean
369fbf1162ddda0c798cf842f74e3214e312b8d3556d3f04bdf17b3e59334593  ./Casey/Main.lean
46577a1bd4080e0371436bdf0e15e3559e111b42fe915a03b4e890753e6f1ec1  ./scratch/Ax.lean
9c90f1d0d6ee28dfb38a01e22379901a05ee5a812783fd1b227a062b591b1762  ./Fuss/Example.lean
ccb14e1cabd94d6cf4d10ba6ae561dec23b1fe8c4ddfd7204a9569d00d4d0116  ./Fuss/Forward.lean
4a8996c0a30a51513fb3268e863f0e33d83364770193da2ec4793bf718f17833  ./Fuss/Geometry.lean
baa6fb1dba3956a4b824fb89c128387491413f3ba3758f9ba4779ee6b02f708c  ./Fuss/Plane.lean
33e27511ac40f054bde6662fc6646d6436d64c8e2a6ee881e059ad5a6db76ff7  ./Fuss/Porism.lean
3601e893d106d17f79506004de524f8b9d6a7aef8abdbc693e483620a8d1e9bd  ./Fuss/Steps.lean
8d747e2f4bdfc04dd78fcca2f9ce5dee32cd9e2666ceed0978985bb17b183e8b  ./scratch/Ax.lean
ada14ccd6647e8d1f6511514ffb40f3e0a3a0c43f0145efe5a880ecc0c2cf7b4  Casey/L14.lean
0d4231595bb8ced2fef3ab1fb0928aa297f6eb921591888eb1fff458bf555d1c  Fuss/L14.lean
```

## Appendix A: casey_types.out
```
@Casey.l14_casey : ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] {P : Type u_2}
  [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (Γ C₁ C₂ C₃ C₄ : EuclideanGeometry.Sphere P)
  {T₁ T₂ T₃ T₄ p : P},
  0 < Γ.radius →
    C₁.IsIntTangentAt Γ T₁ →
      C₂.IsIntTangentAt Γ T₂ →
        C₃.IsIntTangentAt Γ T₃ →
          C₄.IsIntTangentAt Γ T₄ →
            EuclideanGeometry.angle T₁ p T₃ = Real.pi →
              EuclideanGeometry.angle T₂ p T₄ = Real.pi →
                √(Dist.dist C₁.center C₂.center ^ 2 - (C₁.radius - C₂.radius) ^ 2) *
                      √(Dist.dist C₃.center C₄.center ^ 2 - (C₃.radius - C₄.radius) ^ 2) +
                    √(Dist.dist C₂.center C₃.center ^ 2 - (C₂.radius - C₃.radius) ^ 2) *
                      √(Dist.dist C₄.center C₁.center ^ 2 - (C₄.radius - C₁.radius) ^ 2) =
                  √(Dist.dist C₁.center C₃.center ^ 2 - (C₁.radius - C₃.radius) ^ 2) *
                    √(Dist.dist C₂.center C₄.center ^ 2 - (C₂.radius - C₄.radius) ^ 2)
@Casey.l14_casey_ptolemy : ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
  {P : Type u_2} [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (Γ : EuclideanGeometry.Sphere P)
  {T₁ T₂ T₃ T₄ p : P},
  0 < Γ.radius →
    T₁ ∈ Γ →
      T₂ ∈ Γ →
        T₃ ∈ Γ →
          T₄ ∈ Γ →
            EuclideanGeometry.angle T₁ p T₃ = Real.pi →
              EuclideanGeometry.angle T₂ p T₄ = Real.pi →
                Dist.dist T₁ T₂ * Dist.dist T₃ T₄ + Dist.dist T₂ T₃ * Dist.dist T₄ T₁ =
                  Dist.dist T₁ T₃ * Dist.dist T₂ T₄
Casey.l14w_casey : ∃ Γ C₁ C₂ C₃ C₄ T₁ T₂ T₃ T₄ p,
  0 < Γ.radius ∧
    C₁.IsIntTangentAt Γ T₁ ∧
      C₂.IsIntTangentAt Γ T₂ ∧
        C₃.IsIntTangentAt Γ T₃ ∧
          C₄.IsIntTangentAt Γ T₄ ∧
            EuclideanGeometry.angle T₁ p T₃ = Real.pi ∧
              EuclideanGeometry.angle T₂ p T₄ = Real.pi ∧
                C₁ ≠ C₂ ∧
                  C₁ ≠ C₃ ∧
                    C₁ ≠ C₄ ∧
                      C₂ ≠ C₃ ∧
                        C₂ ≠ C₄ ∧
                          C₃ ≠ C₄ ∧
                            C₁ ≠ Γ ∧
                              C₂ ≠ Γ ∧
                                C₃ ≠ Γ ∧
                                  C₄ ≠ Γ ∧
                                    0 < C₁.radius ∧
                                      T₁ ≠ T₂ ∧
                                        T₁ ≠ T₃ ∧
                                          T₁ ≠ T₄ ∧
                                            T₂ ≠ T₃ ∧
                                              T₂ ≠ T₄ ∧
                                                T₃ ≠ T₄ ∧
                                                  Dist.dist C₁.center C₂.center ^ 2 - (C₁.radius - C₂.radius) ^ 2 = 24 ∧
                                                    Dist.dist C₂.center C₃.center ^ 2 - (C₂.radius - C₃.radius) ^ 2 =
                                                        12 ∧
                                                      Dist.dist C₃.center C₄.center ^ 2 - (C₃.radius - C₄.radius) ^ 2 =
                                                          4 ∧
                                                        Dist.dist C₄.center C₁.center ^ 2 -
                                                              (C₄.radius - C₁.radius) ^ 2 =
                                                            8 ∧
                                                          Dist.dist C₁.center C₃.center ^ 2 -
                                                                (C₁.radius - C₃.radius) ^ 2 =
                                                              32 ∧
                                                            Dist.dist C₂.center C₄.center ^ 2 -
                                                                  (C₂.radius - C₄.radius) ^ 2 =
                                                                12 ∧
                                                              √(Dist.dist C₁.center C₂.center ^ 2 -
                                                                        (C₁.radius - C₂.radius) ^ 2) *
                                                                    √(Dist.dist C₃.center C₄.center ^ 2 -
                                                                        (C₃.radius - C₄.radius) ^ 2) +
                                                                  √(Dist.dist C₂.center C₃.center ^ 2 -
                                                                        (C₂.radius - C₃.radius) ^ 2) *
                                                                    √(Dist.dist C₄.center C₁.center ^ 2 -
                                                                        (C₄.radius - C₁.radius) ^ 2) =
                                                                √(Dist.dist C₁.center C₃.center ^ 2 -
                                                                      (C₁.radius - C₃.radius) ^ 2) *
                                                                  √(Dist.dist C₂.center C₄.center ^ 2 -
                                                                      (C₂.radius - C₄.radius) ^ 2)
```
## Appendix B: fuss_types.out
```
@Fuss.l14_fuss : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
  [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]
  (Γ ω : EuclideanGeometry.Sphere P) {A B C D : P},
  0 < ω.radius →
    Dist.dist Γ.center ω.center ≠ Γ.radius →
      A ∈ Γ →
        B ∈ Γ →
          C ∈ Γ →
            D ∈ Γ →
              A ≠ B →
                B ≠ C →
                  C ≠ D →
                    D ≠ A →
                      A ≠ C →
                        B ≠ D →
                          ω.IsTangent line[ℝ, A, B] →
                            ω.IsTangent line[ℝ, B, C] →
                              ω.IsTangent line[ℝ, C, D] →
                                ω.IsTangent line[ℝ, D, A] →
                                  (Γ.radius ^ 2 - Dist.dist Γ.center ω.center ^ 2) ^ 2 =
                                    2 * ω.radius ^ 2 * (Γ.radius ^ 2 + Dist.dist Γ.center ω.center ^ 2)
@Fuss.l14_poncelet_chain_closes : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    Dist.dist Γ.center ω.center ≠ Γ.radius →
      (Γ.radius ^ 2 - Dist.dist Γ.center ω.center ^ 2) ^ 2 =
          2 * ω.radius ^ 2 * (Γ.radius ^ 2 + Dist.dist Γ.center ω.center ^ 2) →
        ∀ {A₀ A₁ A₂ A₃ A₄ T₀ T₁ T₂ T₃ T₄ : P},
          A₀ ∈ Γ →
            A₁ ∈ Γ →
              A₂ ∈ Γ →
                A₃ ∈ Γ →
                  A₄ ∈ Γ →
                    T₀ ∈ ω →
                      T₁ ∈ ω →
                        T₂ ∈ ω →
                          T₃ ∈ ω →
                            T₄ ∈ ω →
                              A₀ ∈ ω.orthRadius T₀ →
                                A₀ ∈ ω.orthRadius T₁ →
                                  A₁ ∈ ω.orthRadius T₁ →
                                    A₁ ∈ ω.orthRadius T₂ →
                                      A₂ ∈ ω.orthRadius T₂ →
                                        A₂ ∈ ω.orthRadius T₃ →
                                          A₃ ∈ ω.orthRadius T₃ →
                                            A₃ ∈ ω.orthRadius T₄ →
                                              A₄ ∈ ω.orthRadius T₄ →
                                                T₀ ≠ T₁ →
                                                  T₁ ≠ T₂ →
                                                    T₂ ≠ T₃ →
                                                      T₃ ≠ T₄ →
                                                        A₀ ≠ A₁ → A₁ ≠ A₂ → A₂ ≠ A₃ → A₃ ≠ A₄ → A₄ = A₀ ∧ T₄ = T₀
@Fuss.l14_exists_bicentric : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    Dist.dist Γ.center ω.center + ω.radius < Γ.radius →
      (Γ.radius ^ 2 - Dist.dist Γ.center ω.center ^ 2) ^ 2 =
          2 * ω.radius ^ 2 * (Γ.radius ^ 2 + Dist.dist Γ.center ω.center ^ 2) →
        ∀ {A : P},
          A ∈ Γ →
            ∃ B C D,
              B ∈ Γ ∧
                C ∈ Γ ∧
                  D ∈ Γ ∧
                    A ≠ B ∧
                      B ≠ C ∧
                        C ≠ D ∧
                          D ≠ A ∧
                            A ≠ C ∧
                              B ≠ D ∧
                                ω.IsTangent line[ℝ, A, B] ∧
                                  ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A]
@Fuss.l14_fuss_iff_exists : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    Dist.dist Γ.center ω.center + ω.radius < Γ.radius →
      ((∃ A B C D,
          A ∈ Γ ∧
            B ∈ Γ ∧
              C ∈ Γ ∧
                D ∈ Γ ∧
                  A ≠ B ∧
                    B ≠ C ∧
                      C ≠ D ∧
                        D ≠ A ∧
                          A ≠ C ∧
                            B ≠ D ∧
                              ω.IsTangent line[ℝ, A, B] ∧
                                ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A]) ↔
        (Γ.radius ^ 2 - Dist.dist Γ.center ω.center ^ 2) ^ 2 =
          2 * ω.radius ^ 2 * (Γ.radius ^ 2 + Dist.dist Γ.center ω.center ^ 2))
@Fuss.l14_fuss_iff_forall : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    Dist.dist Γ.center ω.center + ω.radius < Γ.radius →
      ((∀ A ∈ Γ,
          ∃ B C D,
            A ∈ Γ ∧
              B ∈ Γ ∧
                C ∈ Γ ∧
                  D ∈ Γ ∧
                    A ≠ B ∧
                      B ≠ C ∧
                        C ≠ D ∧
                          D ≠ A ∧
                            A ≠ C ∧
                              B ≠ D ∧
                                ω.IsTangent line[ℝ, A, B] ∧
                                  ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A]) ↔
        (Γ.radius ^ 2 - Dist.dist Γ.center ω.center ^ 2) ^ 2 =
          2 * ω.radius ^ 2 * (Γ.radius ^ 2 + Dist.dist Γ.center ω.center ^ 2))
@Fuss.l14_exists_iff_forall : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    Dist.dist Γ.center ω.center + ω.radius < Γ.radius →
      ((∃ A B C D,
          A ∈ Γ ∧
            B ∈ Γ ∧
              C ∈ Γ ∧
                D ∈ Γ ∧
                  A ≠ B ∧
                    B ≠ C ∧
                      C ≠ D ∧
                        D ≠ A ∧
                          A ≠ C ∧
                            B ≠ D ∧
                              ω.IsTangent line[ℝ, A, B] ∧
                                ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A]) ↔
        ∀ A ∈ Γ,
          ∃ B C D,
            A ∈ Γ ∧
              B ∈ Γ ∧
                C ∈ Γ ∧
                  D ∈ Γ ∧
                    A ≠ B ∧
                      B ≠ C ∧
                        C ≠ D ∧
                          D ≠ A ∧
                            A ≠ C ∧
                              B ≠ D ∧
                                ω.IsTangent line[ℝ, A, B] ∧
                                  ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A])
@Fuss.l14_fuss_iff_reciprocal : ∀ {R d r : ℝ},
  0 ≤ d →
    d < R → r ≠ 0 → ((R ^ 2 - d ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + d ^ 2) ↔ 1 / (R - d) ^ 2 + 1 / (R + d) ^ 2 = 1 / r ^ 2)
Fuss.l14w_fuss : ∃ Γ ω A B C D,
  0 < ω.radius ∧
    Dist.dist Γ.center ω.center ≠ Γ.radius ∧
      A ∈ Γ ∧
        B ∈ Γ ∧
          C ∈ Γ ∧
            D ∈ Γ ∧
              A ≠ B ∧
                B ≠ C ∧
                  C ≠ D ∧
                    D ≠ A ∧
                      A ≠ C ∧
                        B ≠ D ∧
                          ω.IsTangent line[ℝ, A, B] ∧
                            ω.IsTangent line[ℝ, B, C] ∧
                              ω.IsTangent line[ℝ, C, D] ∧
                                ω.IsTangent line[ℝ, D, A] ∧
                                  Γ.center ≠ ω.center ∧
                                    Γ ≠ ω ∧
                                      (Γ.radius ^ 2 - Dist.dist Γ.center ω.center ^ 2) ^ 2 =
                                        2 * ω.radius ^ 2 * (Γ.radius ^ 2 + Dist.dist Γ.center ω.center ^ 2)
Fuss.l14w_poncelet_chain_closes : ∃ Γ ω A₀ A₁ A₂ A₃ A₄ T₀ T₁ T₂ T₃ T₄,
  0 < ω.radius ∧
    Dist.dist Γ.center ω.center ≠ Γ.radius ∧
      (Γ.radius ^ 2 - Dist.dist Γ.center ω.center ^ 2) ^ 2 =
          2 * ω.radius ^ 2 * (Γ.radius ^ 2 + Dist.dist Γ.center ω.center ^ 2) ∧
        A₀ ∈ Γ ∧
          A₁ ∈ Γ ∧
            A₂ ∈ Γ ∧
              A₃ ∈ Γ ∧
                A₄ ∈ Γ ∧
                  T₀ ∈ ω ∧
                    T₁ ∈ ω ∧
                      T₂ ∈ ω ∧
                        T₃ ∈ ω ∧
                          T₄ ∈ ω ∧
                            A₀ ∈ ω.orthRadius T₀ ∧
                              A₀ ∈ ω.orthRadius T₁ ∧
                                A₁ ∈ ω.orthRadius T₁ ∧
                                  A₁ ∈ ω.orthRadius T₂ ∧
                                    A₂ ∈ ω.orthRadius T₂ ∧
                                      A₂ ∈ ω.orthRadius T₃ ∧
                                        A₃ ∈ ω.orthRadius T₃ ∧
                                          A₃ ∈ ω.orthRadius T₄ ∧
                                            A₄ ∈ ω.orthRadius T₄ ∧
                                              T₀ ≠ T₁ ∧
                                                T₁ ≠ T₂ ∧
                                                  T₂ ≠ T₃ ∧
                                                    T₃ ≠ T₄ ∧
                                                      A₀ ≠ A₁ ∧
                                                        A₁ ≠ A₂ ∧
                                                          A₂ ≠ A₃ ∧
                                                            A₃ ≠ A₄ ∧
                                                              A₀ ≠ A₂ ∧
                                                                A₁ ≠ A₃ ∧
                                                                  T₀ ≠ T₂ ∧
                                                                    T₁ ≠ T₃ ∧ Γ.center ≠ ω.center ∧ A₄ = A₀ ∧ T₄ = T₀
Fuss.l14w_exists_bicentric : ∃ Γ ω A,
  0 < ω.radius ∧
    Dist.dist Γ.center ω.center + ω.radius < Γ.radius ∧
      Γ.center ≠ ω.center ∧
        (Γ.radius ^ 2 - Dist.dist Γ.center ω.center ^ 2) ^ 2 =
            2 * ω.radius ^ 2 * (Γ.radius ^ 2 + Dist.dist Γ.center ω.center ^ 2) ∧
          A ∈ Γ ∧
            ∃ B C D,
              B ∈ Γ ∧
                C ∈ Γ ∧
                  D ∈ Γ ∧
                    A ≠ B ∧
                      B ≠ C ∧
                        C ≠ D ∧
                          D ≠ A ∧
                            A ≠ C ∧
                              B ≠ D ∧
                                ω.IsTangent line[ℝ, A, B] ∧
                                  ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A]
Fuss.l14w_fuss_iff : ∃ Γ ω ω',
  Γ.center ≠ ω.center ∧
    ω ≠ ω' ∧
      (0 < ω.radius ∧
          Dist.dist Γ.center ω.center + ω.radius < Γ.radius ∧
            (∃ A B C D,
                A ∈ Γ ∧
                  B ∈ Γ ∧
                    C ∈ Γ ∧
                      D ∈ Γ ∧
                        A ≠ B ∧
                          B ≠ C ∧
                            C ≠ D ∧
                              D ≠ A ∧
                                A ≠ C ∧
                                  B ≠ D ∧
                                    ω.IsTangent line[ℝ, A, B] ∧
                                      ω.IsTangent line[ℝ, B, C] ∧
                                        ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A]) ∧
              ∀ A ∈ Γ,
                ∃ B C D,
                  A ∈ Γ ∧
                    B ∈ Γ ∧
                      C ∈ Γ ∧
                        D ∈ Γ ∧
                          A ≠ B ∧
                            B ≠ C ∧
                              C ≠ D ∧
                                D ≠ A ∧
                                  A ≠ C ∧
                                    B ≠ D ∧
                                      ω.IsTangent line[ℝ, A, B] ∧
                                        ω.IsTangent line[ℝ, B, C] ∧
                                          ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A]) ∧
        0 < ω'.radius ∧
          Dist.dist Γ.center ω'.center + ω'.radius < Γ.radius ∧
            (Γ.radius ^ 2 - Dist.dist Γ.center ω'.center ^ 2) ^ 2 ≠
                2 * ω'.radius ^ 2 * (Γ.radius ^ 2 + Dist.dist Γ.center ω'.center ^ 2) ∧
              ¬∃ A B C D,
                  A ∈ Γ ∧
                    B ∈ Γ ∧
                      C ∈ Γ ∧
                        D ∈ Γ ∧
                          A ≠ B ∧
                            B ≠ C ∧
                              C ≠ D ∧
                                D ≠ A ∧
                                  A ≠ C ∧
                                    B ≠ D ∧
                                      ω'.IsTangent line[ℝ, A, B] ∧
                                        ω'.IsTangent line[ℝ, B, C] ∧
                                          ω'.IsTangent line[ℝ, C, D] ∧ ω'.IsTangent line[ℝ, D, A]
Fuss.l14w_fuss_iff_reciprocal : (7 ^ 2 - 1 ^ 2) ^ 2 = 2 * (24 / 5) ^ 2 * (7 ^ 2 + 1 ^ 2) ∧
  1 / (7 - 1) ^ 2 + 1 / (7 + 1) ^ 2 = 1 / (24 / 5) ^ 2 ∧
    (7 ^ 2 - 1 ^ 2) ^ 2 ≠ 2 * 1 ^ 2 * (7 ^ 2 + 1 ^ 2) ∧ 1 / (7 - 1) ^ 2 + 1 / (7 + 1) ^ 2 ≠ 1 / 1 ^ 2
```
## Appendix C: tamper logs
```
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    falsehyp  rejected (exit 1): FAIL: build
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: Casey.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ALL TAMPERING TESTS REJECTED
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    falsehyp  rejected (exit 1): FAIL: build
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: Fuss.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ALL TAMPERING TESTS REJECTED
```
