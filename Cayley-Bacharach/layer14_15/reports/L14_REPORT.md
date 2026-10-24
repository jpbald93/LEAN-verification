# Paper CB (Cayley–Bacharach) — Layer 14 report: Mathlib-only restatements + witnesses

Paper: `AFM/CayleyBacharach/cayley_bacharach.tex` (one repo).
Wall time: 2026-10-21 23:12 EDT → 00:17 EDT (about 1 h 05 min). All work was done inline, with no subagents.

## Repo: jpbald93/cayley-bacharach @ 9a4f11e82c291bc9428ad9b66bfaba388acf63de
- Fresh `git clone` → `john:~/lean/l14CB_cayley-bacharach`, then `git checkout 9a4f11e`. HEAD verified.
- `lean-toolchain` = `leanprover/lean4:v4.33.1`. Mathlib rev in the manifest = `0df444a360eaa60ab8c11dca51a86af692955474`. `.lake/packages` is symlinked to `~/lean/clifford/.lake/packages`. No update or cache fetch was run.
- New file: `CayleyBacharach/L14.lean` (1050 lines, sha256 `b4d5e13c06d3d93551449aacc4811c5efc1bcde20b50b19c450a89f751d620d4`), namespace `CBL14`.
- `CayleyBacharach.lean`: one line appended at the end, `import CayleyBacharach.L14`.
- `gate.sh`: only the `REQUIRED=` line changed (27 names appended).
- Nothing committed or pushed. Scratch files are in `~/lean/l14CB_scratch/` (B, W, L14 drafts; T.lean and TW.lean hold the `set_option pp.fullNames` type prints).

### Encoding used for the Mathlib-only statements
- A plane cubic / conic / line is `F : MvPolynomial (Fin 3) K` with `F.IsHomogeneous 3 / 2 / 1`.
- A point of ℙ²(K) is a vector `Fin 3 → K`. "Distinct projective points" is `LinearIndependent K ![u, v]`. Vanishing is `MvPolynomial.eval v F = 0`.
- "Exactly meet in P" means every nonzero common zero is `c • P i`.
- A common line component is `∃ ℓ q q', homogeneous of degree 1/2/2, ℓ ≠ 0, F = ℓ*q, G = ℓ*q'`. A common conic component is defined the same way.
- The space of cubics through the points is `homogeneousSubmodule (Fin 3) K 3 ⊓ ⨅ i, ker (aeval (P i))`, and its dimension is `Module.finrank`.
- The field-size conditions are `∃ s : Finset K, 10 < s.card`, `∃ t, t ≠ 0 ∧ t ≠ 1`, `Fintype.card K`, and `[Infinite K]`.
- Collinearity of projective points is `Matrix.det ![X, Y, Z] = 0`, and lines through two points use the Mathlib cross product `⨯₃`.

### Table

| paper theorem / decl | l14 | namespace-free | witness | distinctness / non-degeneracy | notes |
|---|---|---|---|---|---|
| Thm gp — `cayley_bacharach_any` | `l14_cayley_bacharach_any` | yes | `l14w_cayley_bacharach` (ℚ, 3×3 grid) | 9 points pairwise lin. indep.; F, G lin. indep.; H = F+G ≠ c•F, ≠ c•G; no 5 collinear and no conic, both proved | every field |
| Thm ncf — `cayley_bacharach_of_no_common_factor_any` | `l14_cayley_bacharach_of_no_common_factor_any` | yes | `l14w_cayley_bacharach` | no common line component and no common conic component, both proved | every field |
| Thm classical (infinite) — `cayley_bacharach_classical` | `l14_cayley_bacharach_classical` | yes | `l14w_cayley_bacharach` | exactness proved: every nonzero common zero is a multiple of a grid point | |
| Thm classical / f3 (finite, \|K\|∉{4,5,7}) — `cayley_bacharach_classical_finite` (subsumes `_card8`, `_card3`, `_zmod3`) | `l14_cayley_bacharach_classical_finite` | yes | `l14w_cayley_bacharach_zmod3` (𝔽₃) | over 𝔽₃ the same F, G meet in exactly all 9 points of 𝔽₃² (exactness proved); H ≠ c•F, c•G | the witness instance is \|K\|=3 |
| Thm f3 — `cayley_bacharach_card3` | `l14_cayley_bacharach_card3` | yes | `l14w_cayley_bacharach_zmod3` | as above | |
| Thm criterion — `finrank_ker_evalMap_eq_two_iff` | `l14_finrank_eq_two_iff` | yes | `l14w_finrank_eq_two_iff` | both directions instantiated: 8 grid points give finrank = 2; 8 points with 5 on y=0 give finrank ≠ 2 | finrank of a Mathlib submodule of `MvPolynomial` |
| Thm Pascal — `pascal_clean` | `l14_pascal` (explicit cross-product points) and `l14_pascal_points` (X, Y, Z by defining incidence) | yes | `l14w_pascal` (6 rational points on x²+y²=z²) | conic proved not a product of linear forms (via Gram det ≠ 0); the 3 Pascal points pairwise lin. indep.; det = 0 | \|K\|>10 |
| Thm Pappus — `pappus_clean` | `l14_pappus`, `l14_pappus_points` | yes | `l14w_pappus` (ℚ) | the 3 Pappus points pairwise lin. indep.; all incidence and non-incidence hypotheses proved | \|K\|>10 |
| Lemma line — `line_lemma` | `l14_line_lemma` | yes | `l14w_line_lemma` (ℚ, F = z(x²+y²+z²)) | F ≠ 0, and the conic factor q ≠ 0 | \|K\|≥3 stated as `∃ t, t≠0 ∧ t≠1` |
| `line_lemma_false_zmod_two` | `l14_line_lemma_false_zmod_two` | yes | (it is itself a concrete statement over 𝔽₂) | non-divisibility proved via the coefficient of x²y | |
| `det_gram_eq_zero_iff` | not restated | — | — | — | Skipped for time. `gram` is a repo definition, and a Mathlib-only form would need the quadratic-form matrix; it is used internally in `circleQ_irr` |

Bridges (`l14b_*`, also in REQUIRED):
- `l14b_eval3/2/1`: `MvPolynomial.eval` of a homogeneous polynomial equals the library's `eval` / `evalC` / `⬝ᵥ` of its coefficient vector.
- `l14b_cubicsThrough`: the Mathlib submodule is the image of `ker (evalMap P)` under the injective linear map from coefficient vectors to polynomials, so the two have equal finrank.
- `l14b_mulLin_iff`: `F = ℓ * q` ⇔ `cv F = mulLin (cv ℓ) (cv q)`.
- `l14b_lin`, `l14b_con`: the Mathlib no-common-component hypotheses are equivalent (↔) to the library's `hlin`/`hcon`.
- `l14b_exact`: the Mathlib exactness hypothesis gives `ExactlyMeetIn`.
- `l14b_meet`: any point on two distinct lines is a multiple of the cross product.

These rest on the fact that every homogeneous polynomial of degree 1/2/3 in 3 variables is `toP E c` for the library's monomial order (`eq_toP` plus explicit surjectivity of the exponent tables).

## FINDINGS
1. **No Mathlib-only restatement turned out false or needed an extra hypothesis.** Every hypothesis maps to the library's by a proved ↔ or ⇒ bridge.
2. **The published gate is not portable to macOS/BSD (environment finding, not a proof issue).** `gate.sh` line 31 uses `mktemp --suffix=.lean -p .`, which BSD `mktemp` rejects. Under `jl gate` (default system tools) the gate fails, both before and after: "FAIL: axiom report", with `mktemp: unrecognized option --suffix=.lean`. Under `jl -g gate` (GNU tools) it passes. `tests/tamper.sh` also uses GNU `sed -i` with no suffix argument. All gate and tamper results below are therefore from GNU mode.
3. Minor: the paper presents Pascal/Pappus as "the points L12×L45 … are collinear" with explicit cross-product terms. I added `l14_pascal_points` and `l14_pappus_points`, where X, Y, Z are any points satisfying the two incidences each (the defining property). These follow from the library theorem plus the library's `pascal_generic`/`pappus_generic`, so no extra hypothesis is needed.
4. Not covered: `det_gram_eq_zero_iff` (see table), and the auxiliary decls (`conic_three`, `cubic_four`, `conics_le_*`, …), which are internal lemmas rather than main theorems.

## Type-check output (mechanical namespace check)
Scratch file `~/lean/l14CB_scratch/T.lean` (12 l14 theorems) and `TW.lean` (6 witnesses), with `set_option pp.fullNames true`. Logs: `~/lean/l14CB_cayley-bacharach.types.log` (189 lines) and `.types_w.log` (99 lines). Result: 0 errors.

Command: `grep -o "PlaneCubic[A-Za-z._]*\|CBL14[A-Za-z0-9_.]*" | grep -v "^CBL14\.l14w\?_"`. The excluded matches are the `#check` header names only.
```
== types      (no output)
== types_w    (no output)
```
So no `PlaneCubic.*` and no `CBL14` definition (gridQ, Fw, circleQ, …) occurs in any l14/l14w type. The witnesses inline their points and polynomials as `![…]` literals and `X i` terms. Excerpt:
```
@CBL14.l14_cayley_bacharach_any : ∀ {K : Type u_1} [inst : Field K] (P : Fin 9 → Fin 3 → K),
  (∀ (i j : Fin 9), i ≠ j → LinearIndependent K ![P i, P j]) →
    (∀ (ℓ : MvPolynomial (Fin 3) K), ℓ.IsHomogeneous 1 → ℓ ≠ 0 → ∀ (s : Finset (Fin 8)),
        (∀ i ∈ s, (MvPolynomial.eval (P i.castSucc)) ℓ = 0) → s.card ≤ 4) →
      (∀ (q : MvPolynomial (Fin 3) K), q.IsHomogeneous 2 → (∀ (i : Fin 8), (MvPolynomial.eval (P i.castSucc)) q = 0) → q = 0) →
        ∀ (F G : MvPolynomial (Fin 3) K), F.IsHomogeneous 3 → G.IsHomogeneous 3 → LinearIndependent K ![F, G] →
          (∀ (i : Fin 9), (MvPolynomial.eval (P i)) F = 0) → (∀ (i : Fin 9), (MvPolynomial.eval (P i)) G = 0) →
            ∀ (H : MvPolynomial (Fin 3) K), H.IsHomogeneous 3 →
              (∀ (i : Fin 8), (MvPolynomial.eval (P i.castSucc)) H = 0) → (MvPolynomial.eval (P 8)) H = 0
```
(The full prints are in the logs on john.)

## Gate
- Before: `jl -g gate`: **PASS (100 declarations, standard axioms only)**. `jl gate` (BSD): FAIL at mktemp (finding 2).
- After: `jl -g gate`: **PASS (127 declarations, standard axioms only)**. All 27 new names report `[propext, Classical.choice, Quot.sound]`. `jl gate` (BSD): same mktemp FAIL as before.

## Tamper (`jl -g tamper`)
```
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    falsehyp  rejected (exit 1): FAIL: build
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: PlaneCubic.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ALL TAMPERING TESTS REJECTED
```

## Hashes
`~/lean/l14CB_cayley-bacharach.sha_before` / `.sha_after` cover 25 files: CayleyBacharach/*.lean, the root file, gate.sh, tests, lakefile, and manifest. The only differences are the two files this task is allowed to change:
```
CayleyBacharach.lean  ca17373d…fcb43 → 3ddade8b…64b92   (one import line appended)
gate.sh               f8ca04b5…53303 → 4a67babc…4fa0c   (REQUIRED line only)
```
All 21 pre-existing `CayleyBacharach/*.lean` files are byte-identical to the fresh clone. `git status`: ` M CayleyBacharach.lean`, ` M gate.sh`, `?? CayleyBacharach/L14.lean`.
The forbidden-token grep over L14.lean is empty: no sorry/admit/axiom/native_decide/#eval/set_option/macro/notation/run_cmd.

## REQUIRED added (27)
CBL14.l14_cayley_bacharach_any CBL14.l14_cayley_bacharach_of_no_common_factor_any CBL14.l14_cayley_bacharach_classical CBL14.l14_cayley_bacharach_classical_finite CBL14.l14_cayley_bacharach_card3 CBL14.l14_finrank_eq_two_iff CBL14.l14_pascal CBL14.l14_pascal_points CBL14.l14_pappus CBL14.l14_pappus_points CBL14.l14_line_lemma CBL14.l14_line_lemma_false_zmod_two CBL14.l14w_cayley_bacharach CBL14.l14w_cayley_bacharach_zmod3 CBL14.l14w_finrank_eq_two_iff CBL14.l14w_pascal CBL14.l14w_pappus CBL14.l14w_line_lemma CBL14.l14b_eval3 CBL14.l14b_eval2 CBL14.l14b_eval1 CBL14.l14b_cubicsThrough CBL14.l14b_mulLin_iff CBL14.l14b_lin CBL14.l14b_con CBL14.l14b_exact CBL14.l14b_meet
