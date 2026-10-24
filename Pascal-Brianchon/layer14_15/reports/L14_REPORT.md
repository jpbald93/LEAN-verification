# PAPER Pascal — Layer 14 report (Mathlib-only restatements + witnesses)

Status: **COMPLETE** — 1 repo, gate PASS (59 theorems), tamper ALL REJECTED, pre-existing files unchanged.
Wall time: 2026-10-22 09:06 → 09:29 EDT (≈ 23 min). All work done inline (no subagents).

Paper: `AFM/Pascal/pascal.tex` — "Pascal's hexagon theorem over an arbitrary field, formalised in Lean 4" (J. Bald).
Main statements = paper Table 1 (22 names, namespace `PascalHexagon`).

## Repo: pascal-hexagon

| item | value |
|---|---|
| URL | https://github.com/jpbald93/pascal-hexagon |
| pinned (paper) | `726da4d` → `git rev-parse HEAD` = `726da4dbcce2b955207e26b18e12c9d16f38173e` |
| clone | john:`~/lean/l14Pascal_pascal-hexagon` (fresh `git clone` + `git checkout 726da4d`) |
| toolchain | `leanprover/lean4:v4.33.1` |
| Mathlib rev | `0df444a360eaa60ab8c11dca51a86af692955474` (matches) → `.lake/packages` → `~/lean/clifford/.lake/packages` |
| build before | `Build completed successfully (1814 jobs).` |
| gate before | `jl gate` (default BSD tools): **FAIL** (`mktemp: unrecognized option '--suffix=.lean'` → `FAIL: axiom report`, see FINDING 1). `jl -g gate`: `PASS (32 theorems, standard axioms only)` |
| gate after | `jl -g gate`: **`PASS (59 theorems, standard axioms only)`** (BSD mode: same mktemp FAIL as before) |
| tamper after | `jl -g tamper`: sorry / ax2line / evalfake / macro → `FAIL: forbidden token`; falsehyp → `FAIL: build`; wrap → `FAIL: nonstandard axioms: PascalHexagon.zz_extra_axiom_…`; **`ALL TAMPERING TESTS REJECTED`** |
| new file | `PascalHexagon/L14.lean` (sha256 `8c81c04e3416e7b04aa29b349cba1609fe9598716e284db45b414aa6889a6362`) |
| root file | one line appended at end of `PascalHexagon.lean`: `import PascalHexagon.L14` |
| gate.sh | only the `REQUIRED=` line changed (27 names appended) |
| commits/pushes | none (`git status`: ` M PascalHexagon.lean`, ` M gate.sh`, `?? PascalHexagon/L14.lean`) |

### Per-theorem table

"namespace-free" = the `pp.fullNames` type of the l14 theorem has no `PascalHexagon` occurrence (mechanical check below).
All witnesses are over ℚ with explicit integer vectors.

| paper theorem (Lean name) | l14 | namespace-free | witness | distinctness / non-degeneracy | notes |
|---|---|---|---|---|---|
| Prop 1(a) `pascalDet_eq_pascalBracket` | `l14_pascalDet_eq_pascalBracket` | yes | `l14w_vector` | value at `e₁,e₂,e₃,(1,1,1),(1,2,3),(2,-1,5)` is `-51 ≠ 0` (identity not `0=0`) | `pascalDet`, `pascalBracket`, `br` unfolded to `⨯₃`, `⬝ᵥ` |
| Prop 1(b) `det_verMatrix_eq_neg_pascalBracket` | `l14_det_veronese` | yes | `l14w_vector` | same `-51` point | 6×6 Veronese matrix written as `Matrix.of ![…]` |
| Lemma 2 `pascalDet_eq_zero_of_quadEval` | `l14_pascal_of_coeffs` | yes | `l14w_vector` | `c=(1,1,-1,0,0,0) ≠ 0`; 6 circle points satisfy `ν(v)⬝c=0`; vertices pairwise non-proportional; 3 Pascal points nonzero & pairwise non-proportional | `quadEval`, `ver` unfolded |
| Lemma 3 `apply_eq_quadEval` | `l14_apply_eq_coeffs` | yes | (identity, no hypotheses) | — | `coeffs` written via `Q (Pi.single i 1)`, `QuadraticMap.polar` |
| Lemma 3 `coeffs_ne_zero` | `l14_coeffs_ne_zero` | yes | `l14w_vector` (`Q ≠ 0` for `x²+y²-z²`) | — | |
| Thm 4 `pascal_quadraticMap` | `l14_pascal_quadraticMap` | yes (library type was already Mathlib-only) | `l14w_vector` | `Q=weightedSumSquares ![1,1,-1] ≠ 0`; points distinct; Pascal points pairwise non-proportional | |
| Rem 5 `pascal_matrix` | `l14_pascal_matrix` | yes | `l14w_vector` | `M = diagonal ![1,1,-1]`, `M ≠ 0`, symmetric, `2 ≠ 0`, `vᵀMv=0` for all 6 | |
| Rem 6 `pascalDet_standardConic` | `l14_pascalDet_standardConic` | yes | `l14w_vector` | params `(1,0),(0,1),(1,1),(1,-1),(2,1),(1,3)`: 6 vertices pairwise non-proportional, first two Pascal points non-proportional | stated with `A = ![s0², s0 t0, t0²]` etc. |
| Lemma 7 `isCollinear_mk_iff` | `l14_isCollinear_mk_iff` | yes | `l14w_incidence` | `{(1:0:0),(0:1:0),(1:1:0)}` collinear (det 0), `{(1:0:0),(0:1:0),(1:0:1)}` not (det 1) | conclusion as `Matrix.det ![u,v,w] = 0` |
| Lemma 8(a,b) `mem_line_cross`, `eq_cross_of_orthogonal'` | `l14_line_unique` | yes | `l14w_incidence` | `A ≠ B` | existence + uniqueness of the line through 2 points, Mathlib `cross`/`orthogonal` |
| Lemma 8(a,b) `cross_mem_lines`, `eq_cross_of_orthogonal` | `l14_point_unique` | yes | `l14w_incidence` | `D ≠ E`, `AB ≠ DE` | |
| Lemma 8(c) `cross_cross_spec` | `l14_cross_cross_spec` | yes (library type already Mathlib-only) | `l14w_incidence` | `A≠B`, `D≠E`, `cross A B ≠ cross D E` | |
| Lemma 10 `onConic_mk_iff` | `l14_onConic_mk_iff` | yes | `l14w_incidence` | `(3:4:5)` on `x²+y²-z²`, `(1:0:0)` not | `OnConic` unfolded to `Q P.rep = 0` |
| Thm 1 `pascal`, `pascal'`, Thm 9 `pascal_of_isCollinear` | `l14_pascal` | yes, and **no `cross`** | `l14w_pascal` | unit circle, `A..F = (1,0),(0,1),(-1,0),(3/5,4/5),(0,-1),(4/5,-3/5)`: all 15 vertex pairs distinct; all hypotheses; Pascal points `(1:1:2),(-4:-3:1),(7:6:5)` pairwise distinct | P,R,S arbitrary points given by `IsCollinear`; opposite-sides-distinct written as `¬(IsCollinear {A,B,D} ∧ IsCollinear {A,B,E})`, equivalent to `cross A B ≠ cross D E` by bridge `l14b_cross_ne_iff` |
| Lemma (Pappus proof) `linePair_ne_zero` | — | — | — | — | proof aid only (mentions `linePair`/`dotLeft`); used inside `l14_pappus`, not restated separately |
| Cor 11 `pappus` | `l14_pappus` | yes, no `cross` | `l14w_pappus` | lines `y=0`, `x=0` (`a ≠ b`); `A,C,E=(1,0),(2,0),(3,0)`, `B,D,F=(0,1),(0,3),(0,2)`; all 15 vertex pairs distinct; Pappus points `(1:-1:0),(6:-2:1),(-2:6:1)` pairwise distinct | |
| Thm 12 `brianchon`, `brianchon_concurrent` | `l14_brianchon` | yes, no `cross` | `l14w_brianchon` | the 6 tangents to the unit circle at `(-1,0),(0,-1),(1,0),(-3/5,-4/5),(0,1),(-4/5,3/5)` lie on the dual conic `ℓ₀²+ℓ₁²-ℓ₂²`; 15 line pairs distinct; vertices `Vxy` and opposite vertices distinct; diagonals `(1:1:2),(-4:-3:1),(7:6:5)` pairwise distinct; common point `(7:-9:1)` lies on all three | vertices and diagonals are arbitrary points/lines given by incidence; conclusion = collinear in dual plane ∧ ∃ common point. **Drops** `brianchon_concurrent`'s extra hypothesis that the first two diagonals are distinct (FINDING 3) |

Coverage: 21 of the 22 Table-1 names have a Mathlib-only restatement (the 22nd, `linePair_ne_zero`, is a proof aid whose statement is about the repo's `linePair`; it is used, not restated). Every restatement has a witness or is a hypothesis-free identity (`l14_apply_eq_coeffs`).

### Bridges (in `L14.lean`)
- `l14b_mk_ne`: `v ⨯₃ w ≠ 0 → mk v ≠ mk w`.
- `l14b_col` / `l14b_ncol`: triple product `= 0` / `≠ 0` ⇒ (non)collinear (from library `isCollinear_mk_iff` directions).
- `l14b_cross_ne_iff`: for `A ≠ B`, `D ≠ E`: `cross A B ≠ cross D E ↔ ¬(IsCollinear {A,B,D} ∧ IsCollinear {A,B,E})`.
- `l14b_exists_ne`, `l14b_common_point`: three collinear points of the dual plane have a common incident point, **with no distinctness hypothesis** (degenerate cases handled by choosing an auxiliary line).

### REQUIRED added to gate.sh (27)
`l14b_mk_ne l14b_col l14b_ncol l14b_cross_ne_iff l14b_exists_ne l14b_common_point l14_pascalDet_eq_pascalBracket l14_det_veronese l14_pascal_of_coeffs l14_apply_eq_coeffs l14_coeffs_ne_zero l14_pascal_quadraticMap l14_pascal_matrix l14_pascalDet_standardConic l14_isCollinear_mk_iff l14_line_unique l14_point_unique l14_cross_cross_spec l14_onConic_mk_iff l14_pascal l14_pappus l14_brianchon l14w_pascal l14w_vector l14w_pappus l14w_brianchon l14w_incidence`
All 27 report `[propext, Classical.choice, Quot.sound]` or a subset (gate PASS, 59 = 32 + 27).

## FINDINGS
No Mathlib-only restatement turned out false, and none needed an extra hypothesis. Every restatement is proved from the library theorem plus the bridges above.

1. **Gate portability (infrastructure, not mathematics).** `gate.sh` line 30 uses GNU-only `mktemp --suffix=.lean -p .`. Under the machine's default BSD tool mode (`~/lean/jl gate`) the published gate fails at commit 726da4d, before *and* after L14, with `mktemp: unrecognized option '--suffix=.lean'` → `FAIL: axiom report`. The paper's claimed `PASS (32 theorems…)` reproduces only with GNU tools (`jl -g gate`). `tests/tamper.sh` also uses GNU `sed -i` (no suffix argument), so I ran it with `-g` too. Logs: `~/lean/l14Pascal_pascal-hexagon.gate_before_bsd.log`, `.gate_after_bsd.log`.
2. **Pascal and Pappus do not need `cross` in the statement.** `cross` appears only in the opposite-sides-distinct hypotheses. Those can be replaced by Mathlib `IsCollinear` conditions with an equivalence proof (`l14b_cross_ne_iff`), so `l14_pascal` and `l14_pappus` mention only `QuadraticForm`, `Projectivization.rep`, `≠` and `IsCollinear`/`orthogonal`.
3. **`brianchon_concurrent`'s extra hypothesis can be dropped.** The paper's hypothesis that the first two diagonals are distinct (`h₁₂`) is unnecessary for "∃ a common point", as the paper itself remarks. `l14_brianchon` proves concurrency without it (bridge `l14b_common_point`). So the Mathlib-only statement is stronger than the library's.
4. **Scope reminder, no defect.** As the paper says, Brianchon is stated for lines on a dual conic given as a hypothesis. Tangency is not formalised, and the L14 statement keeps that. The witness uses true tangents to the unit circle (dual conic = `diag(1,1,-1)⁻¹ = diag(1,1,-1)`); tangency is checked numerically, not proved in Lean.
5. Not done: a Lean formalisation of the paper's §5 example showing the hypothesis `AB ≠ DE` cannot be dropped. Only non-vacuity witnesses were produced, not necessity witnesses.

## Mechanical namespace check
Scratch file `~/lean/l14Pascal_scratch/Types.lean` (`import PascalHexagon`, `set_option pp.fullNames true`, `set_option format.width 100000`, `#check @PascalHexagon.<name>` for the 21 non-bridge l14 theorems). Output: `~/lean/l14Pascal_pascal-hexagon.types.log` (rc=0, 21 type headers). After stripping each `PascalHexagon.l14…_name :` header, `grep PascalHexagon` → **0 lines** (empty). `grep cross` on the types of `l14_pascal`, `l14_pappus`, `l14_brianchon` → 0, 0, 0.

## Hashes (sha256, pre-existing files: fresh clone vs after)
| file | before (fresh clone) | after |
|---|---|---|
| ./PascalHexagon.lean | `1a76f25c2f4436a34770a7c321755675dafec7bbf3be5c2c3acc82fd73d2eceb` | `7f4de82c494f13898b9156a8607f425baee3a0516718843e96b726767dc82428` |
| ./PascalHexagon/Bracket.lean | `b2d6d19cfc660df3852913e3ce67da7f6b252e9bec9de8ae1c1801e8951a2589` | unchanged |
| ./PascalHexagon/Brianchon.lean | `111d67fcb8753264bcb29a55cc9826c7fb1750d39717d03b4a88389ed6ab3791` | unchanged |
| ./PascalHexagon/Conic.lean | `81d1578035c2741e65254ac69815196b8ee98789a945853277d7c3a4bcb48540` | unchanged |
| ./PascalHexagon/Correctness.lean | `d79b4d0ee26d302ebff214a96b838489d5f032cd5f8229f7ae50ebbdeb5e1753` | unchanged |
| ./PascalHexagon/Defs.lean | `038688208f2879766a627626665a01372fa304c5486ca5290cfe59f3f31d6625` | unchanged |
| ./PascalHexagon/L14.lean | `(absent)` | `8c81c04e3416e7b04aa29b349cba1609fe9598716e284db45b414aa6889a6362` |
| ./PascalHexagon/Projective.lean | `e2a5e14389910775df82e8db3a01804ebe784c8e62f2135608b0474d234776f9` | unchanged |
| ./PascalHexagon/StandardConic.lean | `a88c9c6b828ffcd2346e4f45ca45f882e52e28158c59e1aa62ff40c0d067dd1f` | unchanged |
| ./PascalHexagon/Veronese.lean | `50d093d435893bd537bd992766aca4b73e70a6f278d7d447422c5c9089bae45c` | unchanged |
| ./gate.sh | `1ee1d0b3259fabcc71f07dfc3364f8a3f06b168dd18efe8663ce3359a3165186` | `77e3e44cd4de8af620d2f044d1d4a9303b1bd506d63aa15ad4b3dac289fcb37a` |
| ./tests/tamper.sh | `6755ada15445a11af0e29c2da5daff2b631de4c79ddf0f6ea72299fc00f3a19f` | unchanged |
(root file: one import appended; gate.sh: REQUIRED line only; L14.lean new.)
Full lists: `~/lean/l14Pascal_pascal-hexagon.sha_before`, `.sha_after` (diff shows only the root file, gate.sh and the new L14.lean).

## Logs on john
`~/lean/l14Pascal_pascal-hexagon.{build_before,gate_before,gate_before_bsd,gate_after,gate_after_bsd,tamper,types,types_stripped}.log`, `.sha_before`, `.sha_after`; scratch: `~/lean/l14Pascal_scratch/`.

## Appendix: type-check output (`pp.fullNames`)
```
@PascalHexagon.l14_pascalDet_eq_pascalBracket : ∀ {K : Type u_1} [inst : CommRing K] (A B C D E F : Fin 3 → K),
  (crossProduct ((crossProduct A) B)) ((crossProduct D) E) ⬝ᵥ
      (crossProduct ((crossProduct ((crossProduct B) C)) ((crossProduct E) F)))
        ((crossProduct ((crossProduct C) D)) ((crossProduct F) A)) =
    A ⬝ᵥ (crossProduct B) E * B ⬝ᵥ (crossProduct C) F * C ⬝ᵥ (crossProduct D) A * D ⬝ᵥ (crossProduct E) F -
          A ⬝ᵥ (crossProduct B) E * B ⬝ᵥ (crossProduct C) F * C ⬝ᵥ (crossProduct D) F * D ⬝ᵥ (crossProduct E) A +
        A ⬝ᵥ (crossProduct B) E * B ⬝ᵥ (crossProduct C) E * C ⬝ᵥ (crossProduct D) F * D ⬝ᵥ (crossProduct F) A -
      A ⬝ᵥ (crossProduct B) D * B ⬝ᵥ (crossProduct C) E * C ⬝ᵥ (crossProduct D) F * E ⬝ᵥ (crossProduct F) A
@PascalHexagon.l14_det_veronese : ∀ {K : Type u_1} [inst : CommRing K] (A B C D E F : Fin 3 → K),
  !![A 0 ^ 2, A 1 ^ 2, A 2 ^ 2, A 0 * A 1, A 1 * A 2, A 2 * A 0;
        B 0 ^ 2, B 1 ^ 2, B 2 ^ 2, B 0 * B 1, B 1 * B 2, B 2 * B 0;
        C 0 ^ 2, C 1 ^ 2, C 2 ^ 2, C 0 * C 1, C 1 * C 2, C 2 * C 0;
        D 0 ^ 2, D 1 ^ 2, D 2 ^ 2, D 0 * D 1, D 1 * D 2, D 2 * D 0;
        E 0 ^ 2, E 1 ^ 2, E 2 ^ 2, E 0 * E 1, E 1 * E 2, E 2 * E 0;
        F 0 ^ 2, F 1 ^ 2, F 2 ^ 2, F 0 * F 1, F 1 * F 2, F 2 * F 0].det =
    -(A ⬝ᵥ (crossProduct B) E * B ⬝ᵥ (crossProduct C) F * C ⬝ᵥ (crossProduct D) A * D ⬝ᵥ (crossProduct E) F -
            A ⬝ᵥ (crossProduct B) E * B ⬝ᵥ (crossProduct C) F * C ⬝ᵥ (crossProduct D) F * D ⬝ᵥ (crossProduct E) A +
          A ⬝ᵥ (crossProduct B) E * B ⬝ᵥ (crossProduct C) E * C ⬝ᵥ (crossProduct D) F * D ⬝ᵥ (crossProduct F) A -
        A ⬝ᵥ (crossProduct B) D * B ⬝ᵥ (crossProduct C) E * C ⬝ᵥ (crossProduct D) F * E ⬝ᵥ (crossProduct F) A)
@PascalHexagon.l14_pascal_of_coeffs : ∀ {K : Type u_1} [inst : CommRing K] [IsDomain K] {c : Fin 6 → K},
  c ≠ 0 →
    ∀ {A B C D E F : Fin 3 → K},
      ![A 0 ^ 2, A 1 ^ 2, A 2 ^ 2, A 0 * A 1, A 1 * A 2, A 2 * A 0] ⬝ᵥ c = 0 →
        ![B 0 ^ 2, B 1 ^ 2, B 2 ^ 2, B 0 * B 1, B 1 * B 2, B 2 * B 0] ⬝ᵥ c = 0 →
          ![C 0 ^ 2, C 1 ^ 2, C 2 ^ 2, C 0 * C 1, C 1 * C 2, C 2 * C 0] ⬝ᵥ c = 0 →
            ![D 0 ^ 2, D 1 ^ 2, D 2 ^ 2, D 0 * D 1, D 1 * D 2, D 2 * D 0] ⬝ᵥ c = 0 →
              ![E 0 ^ 2, E 1 ^ 2, E 2 ^ 2, E 0 * E 1, E 1 * E 2, E 2 * E 0] ⬝ᵥ c = 0 →
                ![F 0 ^ 2, F 1 ^ 2, F 2 ^ 2, F 0 * F 1, F 1 * F 2, F 2 * F 0] ⬝ᵥ c = 0 →
                  (crossProduct ((crossProduct A) B)) ((crossProduct D) E) ⬝ᵥ
                      (crossProduct ((crossProduct ((crossProduct B) C)) ((crossProduct E) F)))
                        ((crossProduct ((crossProduct C) D)) ((crossProduct F) A)) =
                    0
@PascalHexagon.l14_apply_eq_coeffs : ∀ {K : Type u_1} [inst : CommRing K] (Q : QuadraticMap K (Fin 3 → K) K)
  (v : Fin 3 → K),
  Q v =
    ![v 0 ^ 2, v 1 ^ 2, v 2 ^ 2, v 0 * v 1, v 1 * v 2, v 2 * v 0] ⬝ᵥ
      ![Q (Pi.single 0 1), Q (Pi.single 1 1), Q (Pi.single 2 1),
        QuadraticMap.polar (⇑Q) (Pi.single 0 1) (Pi.single 1 1),
        QuadraticMap.polar (⇑Q) (Pi.single 1 1) (Pi.single 2 1),
        QuadraticMap.polar (⇑Q) (Pi.single 2 1) (Pi.single 0 1)]
@PascalHexagon.l14_coeffs_ne_zero : ∀ {K : Type u_1} [inst : CommRing K] {Q : QuadraticMap K (Fin 3 → K) K},
  Q ≠ 0 →
    ![Q (Pi.single 0 1), Q (Pi.single 1 1), Q (Pi.single 2 1), QuadraticMap.polar (⇑Q) (Pi.single 0 1) (Pi.single 1 1),
        QuadraticMap.polar (⇑Q) (Pi.single 1 1) (Pi.single 2 1),
        QuadraticMap.polar (⇑Q) (Pi.single 2 1) (Pi.single 0 1)] ≠
      0
@PascalHexagon.l14_pascal_quadraticMap : ∀ {K : Type u_1} [inst : CommRing K] [IsDomain K]
  {Q : QuadraticMap K (Fin 3 → K) K},
  Q ≠ 0 →
    ∀ {A B C D E F : Fin 3 → K},
      Q A = 0 →
        Q B = 0 →
          Q C = 0 →
            Q D = 0 →
              Q E = 0 →
                Q F = 0 →
                  (crossProduct ((crossProduct A) B)) ((crossProduct D) E) ⬝ᵥ
                      (crossProduct ((crossProduct ((crossProduct B) C)) ((crossProduct E) F)))
                        ((crossProduct ((crossProduct C) D)) ((crossProduct F) A)) =
                    0
@PascalHexagon.l14_pascal_matrix : ∀ {K : Type u_1} [inst : Field K],
  2 ≠ 0 →
    ∀ {M : Matrix (Fin 3) (Fin 3) K},
      M ≠ 0 →
        M.IsSymm →
          ∀ {A B C D E F : Fin 3 → K},
            A ⬝ᵥ M.mulVec A = 0 →
              B ⬝ᵥ M.mulVec B = 0 →
                C ⬝ᵥ M.mulVec C = 0 →
                  D ⬝ᵥ M.mulVec D = 0 →
                    E ⬝ᵥ M.mulVec E = 0 →
                      F ⬝ᵥ M.mulVec F = 0 →
                        (crossProduct ((crossProduct A) B)) ((crossProduct D) E) ⬝ᵥ
                            (crossProduct ((crossProduct ((crossProduct B) C)) ((crossProduct E) F)))
                              ((crossProduct ((crossProduct C) D)) ((crossProduct F) A)) =
                          0
@PascalHexagon.l14_pascalDet_standardConic : ∀ {K : Type u_1} [inst : CommRing K] (s t : Fin 6 → K)
  {A B C D E F : Fin 3 → K},
  A = ![s 0 ^ 2, s 0 * t 0, t 0 ^ 2] →
    B = ![s 1 ^ 2, s 1 * t 1, t 1 ^ 2] →
      C = ![s 2 ^ 2, s 2 * t 2, t 2 ^ 2] →
        D = ![s 3 ^ 2, s 3 * t 3, t 3 ^ 2] →
          E = ![s 4 ^ 2, s 4 * t 4, t 4 ^ 2] →
            F = ![s 5 ^ 2, s 5 * t 5, t 5 ^ 2] →
              (crossProduct ((crossProduct A) B)) ((crossProduct D) E) ⬝ᵥ
                  (crossProduct ((crossProduct ((crossProduct B) C)) ((crossProduct E) F)))
                    ((crossProduct ((crossProduct C) D)) ((crossProduct F) A)) =
                0
@PascalHexagon.l14_isCollinear_mk_iff : ∀ {K : Type u_1} [inst : Field K] {u v w : Fin 3 → K} (hu : u ≠ 0) (hv : v ≠ 0)
  (hw : w ≠ 0),
  Projectivization.IsCollinear {Projectivization.mk K u hu, Projectivization.mk K v hv, Projectivization.mk K w hw} ↔
    Matrix.det ![u, v, w] = 0
@PascalHexagon.l14_line_unique : ∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K]
  {A B : Projectivization K (Fin 3 → K)},
  A ≠ B →
    (A.orthogonal (A.cross B) ∧ B.orthogonal (A.cross B)) ∧
      ∀ (L : Projectivization K (Fin 3 → K)), A.orthogonal L → B.orthogonal L → L = A.cross B
@PascalHexagon.l14_point_unique : ∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K]
  {L M : Projectivization K (Fin 3 → K)},
  L ≠ M →
    ((L.cross M).orthogonal L ∧ (L.cross M).orthogonal M) ∧
      ∀ (P : Projectivization K (Fin 3 → K)), P.orthogonal L → P.orthogonal M → P = L.cross M
@PascalHexagon.l14_cross_cross_spec : ∀ {K : Type u_1} [inst : Field K] [inst_1 : DecidableEq K]
  {A B D E : Projectivization K (Fin 3 → K)},
  A ≠ B →
    D ≠ E →
      A.cross B ≠ D.cross E →
        Projectivization.IsCollinear {A, B, (A.cross B).cross (D.cross E)} ∧
          Projectivization.IsCollinear {D, E, (A.cross B).cross (D.cross E)} ∧
            ∀ (X : Projectivization K (Fin 3 → K)),
              Projectivization.IsCollinear {A, B, X} →
                Projectivization.IsCollinear {D, E, X} → X = (A.cross B).cross (D.cross E)
@PascalHexagon.l14_onConic_mk_iff : ∀ {K : Type u_1} [inst : Field K] (Q : QuadraticForm K (Fin 3 → K)) {v : Fin 3 → K}
  (hv : v ≠ 0), Q (Projectivization.mk K v hv).rep = 0 ↔ Q v = 0
@PascalHexagon.l14_pascal : ∀ {K : Type u_1} [inst : Field K] {Q : QuadraticForm K (Fin 3 → K)},
  Q ≠ 0 →
    ∀ {A B C D E F P R S : Projectivization K (Fin 3 → K)},
      Q A.rep = 0 →
        Q B.rep = 0 →
          Q C.rep = 0 →
            Q D.rep = 0 →
              Q E.rep = 0 →
                Q F.rep = 0 →
                  A ≠ B →
                    B ≠ C →
                      C ≠ D →
                        D ≠ E →
                          E ≠ F →
                            F ≠ A →
                              ¬(Projectivization.IsCollinear {A, B, D} ∧ Projectivization.IsCollinear {A, B, E}) →
                                ¬(Projectivization.IsCollinear {B, C, E} ∧ Projectivization.IsCollinear {B, C, F}) →
                                  ¬(Projectivization.IsCollinear {C, D, F} ∧ Projectivization.IsCollinear {C, D, A}) →
                                    Projectivization.IsCollinear {A, B, P} →
                                      Projectivization.IsCollinear {D, E, P} →
                                        Projectivization.IsCollinear {B, C, R} →
                                          Projectivization.IsCollinear {E, F, R} →
                                            Projectivization.IsCollinear {C, D, S} →
                                              Projectivization.IsCollinear {F, A, S} →
                                                Projectivization.IsCollinear {P, R, S}
@PascalHexagon.l14_pappus : ∀ {K : Type u_1} [inst : Field K] {a b A B C D E F P R S : Projectivization K (Fin 3 → K)},
  A.orthogonal a →
    C.orthogonal a →
      E.orthogonal a →
        B.orthogonal b →
          D.orthogonal b →
            F.orthogonal b →
              A ≠ B →
                B ≠ C →
                  C ≠ D →
                    D ≠ E →
                      E ≠ F →
                        F ≠ A →
                          ¬(Projectivization.IsCollinear {A, B, D} ∧ Projectivization.IsCollinear {A, B, E}) →
                            ¬(Projectivization.IsCollinear {B, C, E} ∧ Projectivization.IsCollinear {B, C, F}) →
                              ¬(Projectivization.IsCollinear {C, D, F} ∧ Projectivization.IsCollinear {C, D, A}) →
                                Projectivization.IsCollinear {A, B, P} →
                                  Projectivization.IsCollinear {D, E, P} →
                                    Projectivization.IsCollinear {B, C, R} →
                                      Projectivization.IsCollinear {E, F, R} →
                                        Projectivization.IsCollinear {C, D, S} →
                                          Projectivization.IsCollinear {F, A, S} →
                                            Projectivization.IsCollinear {P, R, S}
@PascalHexagon.l14_brianchon : ∀ {K : Type u_1} [inst : Field K] {Q : QuadraticForm K (Fin 3 → K)},
  Q ≠ 0 →
    ∀ {a b c d e f Vab Vbc Vcd Vde Vef Vfa δ₁ δ₂ δ₃ : Projectivization K (Fin 3 → K)},
      Q a.rep = 0 →
        Q b.rep = 0 →
          Q c.rep = 0 →
            Q d.rep = 0 →
              Q e.rep = 0 →
                Q f.rep = 0 →
                  a ≠ b →
                    b ≠ c →
                      c ≠ d →
                        d ≠ e →
                          e ≠ f →
                            f ≠ a →
                              Vab.orthogonal a ∧ Vab.orthogonal b →
                                Vbc.orthogonal b ∧ Vbc.orthogonal c →
                                  Vcd.orthogonal c ∧ Vcd.orthogonal d →
                                    Vde.orthogonal d ∧ Vde.orthogonal e →
                                      Vef.orthogonal e ∧ Vef.orthogonal f →
                                        Vfa.orthogonal f ∧ Vfa.orthogonal a →
                                          Vab ≠ Vde →
                                            Vbc ≠ Vef →
                                              Vcd ≠ Vfa →
                                                Vab.orthogonal δ₁ ∧ Vde.orthogonal δ₁ →
                                                  Vbc.orthogonal δ₂ ∧ Vef.orthogonal δ₂ →
                                                    Vcd.orthogonal δ₃ ∧ Vfa.orthogonal δ₃ →
                                                      Projectivization.IsCollinear {δ₁, δ₂, δ₃} ∧
                                                        ∃ X, X.orthogonal δ₁ ∧ X.orthogonal δ₂ ∧ X.orthogonal δ₃
PascalHexagon.l14w_pascal : ∃ Q A B C D E F P R S,
  Q = QuadraticMap.weightedSumSquares ℚ ![1, 1, -1] ∧
    Q ≠ 0 ∧
      Q A.rep = 0 ∧
        Q B.rep = 0 ∧
          Q C.rep = 0 ∧
            Q D.rep = 0 ∧
              Q E.rep = 0 ∧
                Q F.rep = 0 ∧
                  (A ≠ B ∧
                      A ≠ C ∧
                        A ≠ D ∧
                          A ≠ E ∧
                            A ≠ F ∧ B ≠ C ∧ B ≠ D ∧ B ≠ E ∧ B ≠ F ∧ C ≠ D ∧ C ≠ E ∧ C ≠ F ∧ D ≠ E ∧ D ≠ F ∧ E ≠ F) ∧
                    ¬(Projectivization.IsCollinear {A, B, D} ∧ Projectivization.IsCollinear {A, B, E}) ∧
                      ¬(Projectivization.IsCollinear {B, C, E} ∧ Projectivization.IsCollinear {B, C, F}) ∧
                        ¬(Projectivization.IsCollinear {C, D, F} ∧ Projectivization.IsCollinear {C, D, A}) ∧
                          Projectivization.IsCollinear {A, B, P} ∧
                            Projectivization.IsCollinear {D, E, P} ∧
                              Projectivization.IsCollinear {B, C, R} ∧
                                Projectivization.IsCollinear {E, F, R} ∧
                                  Projectivization.IsCollinear {C, D, S} ∧
                                    Projectivization.IsCollinear {F, A, S} ∧
                                      (P ≠ R ∧ R ≠ S ∧ P ≠ S) ∧ Projectivization.IsCollinear {P, R, S}
PascalHexagon.l14w_vector : have A := ![1, 0, 1];
have B := ![0, 1, 1];
have C := ![-1, 0, 1];
have D := ![3, 4, 5];
have E := ![0, -1, 1];
have F := ![4, -3, 5];
have c := ![1, 1, -1, 0, 0, 0];
have M := Matrix.diagonal ![1, 1, -1];
have Q := QuadraticMap.weightedSumSquares ℚ ![1, 1, -1];
have s := ![1, 0, 1, 1, 2, 1];
have t := ![0, 1, 1, -1, 1, 3];
have W := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1], ![1, 2, 3], ![2, -1, 5]];
(crossProduct ((crossProduct (W 0)) (W 1))) ((crossProduct (W 3)) (W 4)) ⬝ᵥ
      (crossProduct ((crossProduct ((crossProduct (W 1)) (W 2))) ((crossProduct (W 4)) (W 5))))
        ((crossProduct ((crossProduct (W 2)) (W 3))) ((crossProduct (W 5)) (W 0))) =
    -51 ∧
  c ≠ 0 ∧
    (∀ v ∈ [A, B, C, D, E, F],
        ![v 0 ^ 2, v 1 ^ 2, v 2 ^ 2, v 0 * v 1, v 1 * v 2, v 2 * v 0] ⬝ᵥ c = 0 ∧ Q v = 0 ∧ v ⬝ᵥ M.mulVec v = 0) ∧
      Q ≠ 0 ∧
        2 ≠ 0 ∧
          M ≠ 0 ∧
            M.IsSymm ∧
              (∀ v ∈ [A, B, C, D, E, F], ∀ w ∈ [A, B, C, D, E, F], v ≠ w → (crossProduct v) w ≠ 0) ∧
                (crossProduct ((crossProduct A) B)) ((crossProduct D) E) ≠ 0 ∧
                  (crossProduct ((crossProduct B) C)) ((crossProduct E) F) ≠ 0 ∧
                    (crossProduct ((crossProduct C) D)) ((crossProduct F) A) ≠ 0 ∧
                      (crossProduct ((crossProduct ((crossProduct A) B)) ((crossProduct D) E)))
                            ((crossProduct ((crossProduct B) C)) ((crossProduct E) F)) ≠
                          0 ∧
                        (crossProduct ((crossProduct ((crossProduct B) C)) ((crossProduct E) F)))
                              ((crossProduct ((crossProduct C) D)) ((crossProduct F) A)) ≠
                            0 ∧
                          (crossProduct ((crossProduct ((crossProduct A) B)) ((crossProduct D) E)))
                                ((crossProduct ((crossProduct C) D)) ((crossProduct F) A)) ≠
                              0 ∧
                            (∀ (i j : Fin 6),
                                i ≠ j →
                                  (crossProduct ![s i ^ 2, s i * t i, t i ^ 2]) ![s j ^ 2, s j * t j, t j ^ 2] ≠ 0) ∧
                              (crossProduct
                                    ((crossProduct
                                        ((crossProduct ![s 0 ^ 2, s 0 * t 0, t 0 ^ 2]) ![s 1 ^ 2, s 1 * t 1, t 1 ^ 2]))
                                      ((crossProduct ![s 3 ^ 2, s 3 * t 3, t 3 ^ 2]) ![s 4 ^ 2, s 4 * t 4, t 4 ^ 2])))
                                  ((crossProduct
                                      ((crossProduct ![s 1 ^ 2, s 1 * t 1, t 1 ^ 2]) ![s 2 ^ 2, s 2 * t 2, t 2 ^ 2]))
                                    ((crossProduct ![s 4 ^ 2, s 4 * t 4, t 4 ^ 2]) ![s 5 ^ 2, s 5 * t 5, t 5 ^ 2])) ≠
                                0
PascalHexagon.l14w_pappus : ∃ a b A B C D E F P R S,
  A.orthogonal a ∧
    C.orthogonal a ∧
      E.orthogonal a ∧
        B.orthogonal b ∧
          D.orthogonal b ∧
            F.orthogonal b ∧
              a ≠ b ∧
                (A ≠ B ∧
                    A ≠ C ∧
                      A ≠ D ∧
                        A ≠ E ∧ A ≠ F ∧ B ≠ C ∧ B ≠ D ∧ B ≠ E ∧ B ≠ F ∧ C ≠ D ∧ C ≠ E ∧ C ≠ F ∧ D ≠ E ∧ D ≠ F ∧ E ≠ F) ∧
                  ¬(Projectivization.IsCollinear {A, B, D} ∧ Projectivization.IsCollinear {A, B, E}) ∧
                    ¬(Projectivization.IsCollinear {B, C, E} ∧ Projectivization.IsCollinear {B, C, F}) ∧
                      ¬(Projectivization.IsCollinear {C, D, F} ∧ Projectivization.IsCollinear {C, D, A}) ∧
                        Projectivization.IsCollinear {A, B, P} ∧
                          Projectivization.IsCollinear {D, E, P} ∧
                            Projectivization.IsCollinear {B, C, R} ∧
                              Projectivization.IsCollinear {E, F, R} ∧
                                Projectivization.IsCollinear {C, D, S} ∧
                                  Projectivization.IsCollinear {F, A, S} ∧
                                    (P ≠ R ∧ R ≠ S ∧ P ≠ S) ∧ Projectivization.IsCollinear {P, R, S}
PascalHexagon.l14w_brianchon : ∃ Q a b c d e f Vab Vbc Vcd Vde Vef Vfa δ₁ δ₂ δ₃ X,
  Q = QuadraticMap.weightedSumSquares ℚ ![1, 1, -1] ∧
    Q ≠ 0 ∧
      Q a.rep = 0 ∧
        Q b.rep = 0 ∧
          Q c.rep = 0 ∧
            Q d.rep = 0 ∧
              Q e.rep = 0 ∧
                Q f.rep = 0 ∧
                  (a ≠ b ∧
                      a ≠ c ∧
                        a ≠ d ∧
                          a ≠ e ∧
                            a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f) ∧
                    (Vab.orthogonal a ∧ Vab.orthogonal b) ∧
                      (Vbc.orthogonal b ∧ Vbc.orthogonal c) ∧
                        (Vcd.orthogonal c ∧ Vcd.orthogonal d) ∧
                          (Vde.orthogonal d ∧ Vde.orthogonal e) ∧
                            (Vef.orthogonal e ∧ Vef.orthogonal f) ∧
                              (Vfa.orthogonal f ∧ Vfa.orthogonal a) ∧
                                Vab ≠ Vde ∧
                                  Vbc ≠ Vef ∧
                                    Vcd ≠ Vfa ∧
                                      (Vab.orthogonal δ₁ ∧ Vde.orthogonal δ₁) ∧
                                        (Vbc.orthogonal δ₂ ∧ Vef.orthogonal δ₂) ∧
                                          (Vcd.orthogonal δ₃ ∧ Vfa.orthogonal δ₃) ∧
                                            (δ₁ ≠ δ₂ ∧ δ₂ ≠ δ₃ ∧ δ₁ ≠ δ₃) ∧
                                              X.orthogonal δ₁ ∧ X.orthogonal δ₂ ∧ X.orthogonal δ₃
PascalHexagon.l14w_incidence : ∃ Q A B D E G,
  A ≠ B ∧
    D ≠ E ∧
      A.cross B ≠ D.cross E ∧
        A ≠ D ∧
          B ≠ E ∧
            Projectivization.IsCollinear {A, B, G} ∧
              G ≠ A ∧
                G ≠ B ∧
                  ¬Projectivization.IsCollinear {A, B, D} ∧
                    Matrix.det ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0]] = 0 ∧
                      Matrix.det ![![1, 0, 0], ![0, 1, 0], ![1, 0, 1]] = 1 ∧
                        Q = QuadraticMap.weightedSumSquares ℚ ![1, 1, -1] ∧ Q ![3, 4, 5] = 0 ∧ Q ![1, 0, 0] ≠ 0
```
