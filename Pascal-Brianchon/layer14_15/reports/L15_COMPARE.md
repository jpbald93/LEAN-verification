# L15 classical comparison — Paper Pascal (pascal-hexagon)

**Repository.** Fresh clone of `jpbald93/pascal-hexagon` at the pinned commit `726da4d` = `726da4dbcce2b955207e26b18e12c9d16f38173e`, in `john:~/lean/l15Pascal_pascal-hexagon`.
- Toolchain v4.33.1, Mathlib `0df444a3…`, so `.lake/packages` is symlinked to `~/lean/clifford/.lake/packages`.
- `pascal.tex` cites only this repository. primitive-root-families (`e30457a`) is not referenced by the Pascal paper, so it was not used.

**Build and gate.**
- `~/lean/jl build`: `Build completed successfully (1814 jobs)`.
- `~/lean/jl gate` with the default BSD tools: **FAIL** at `mktemp --suffix` (GNU-only option). This is a portability defect of `gate.sh`, and the L14 BSD log shows the same failure.
- `~/lean/jl -g gate` with GNU tools: **`PASS (32 theorems, standard axioms only)`** (rc 0).

**Scratch file.** `john:~/lean/l15Pascal_pascal-hexagon/scratch/L15_compare.lean`, sha256 `e696a6bf86fe87dd30d5ca86c95f05f2cbad673904e0459d82670b1c4b83655a`, 1587 lines.
- Copies: `/tmp/l15p/L15_compare.lean` and `AFM/L14L15/Pascal/L15_compare.lean`.
- The writer's definitions and 20 statements are copied verbatim. Each statement is wrapped as `def classical_X : Prop := ∀ <binders>, <concl>`, and a normalised comparison confirms the text is unchanged.
- The file `import`s `PascalHexagon` and sets two linter options (scratch only).

## Result table

| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| Setting_noThreeCollinear | **O→proved** | `cov_Setting_noThreeCollinear` (via `noThreeCollinear`) | — | NEW PROOF, any characteristic, with the writer's char-free `QNondeg`. The paper never assumes nondegeneracy. |
| Setting_join_obligation | E (bridge) | `cov_Setting_join_obligation` (`isLine_join`) | — | Mathlib linear algebra. |
| Pascal1_a_obligation | E | `cov_Pascal1_a_obligation` | — | Uses the repo's `eq_cross_of_orthogonal` and `cross_mem_lines`, plus the new no-three-collinear lemma to get opposite sides distinct. |
| **Pascal1_a** | **E** | `cov_Pascal1_a` | — | From repo `pascal'` (Theorem 1). The paper is **strictly stronger**: any nonzero Q, any characteristic, only consecutive vertices distinct and opposite sides distinct. The classical hypotheses (nondegenerate conic, six distinct points) imply the repo's hypotheses. |
| Pascal2_a (tangent / five-point) | **O→proved** | `cov_Pascal2_a` (+ `tangent_pascal_vec`, `pascal5_mk`) | — | The paper does not claim it. NEW PROOF in any characteristic: apply the repo's `pascalDet_eq_zero_of_quadEval` over `K[X]` to F(X) = Q(w)·A − b(A,w)·w with w = x + X·u, factor out b(A,w) = X·b(A,u), then set X = 0. Q(x) ≠ 0 because the tangent meets the conic only at A. |
| Pascal2_a_obligation | O→proved | `cov_Pascal2_a_obligation` | — | Existence and uniqueness of the tangent (= polar, see below) and the three intersection points. |
| **Pascal2_b (Pappus)** | **E** | `cov_Pascal2_b` | — | From repo `pappus` (Corollary). The repo is stronger: it allows a = b and points at l∩m, needing only consecutive vertices distinct and opposite sides distinct. The classical hypotheses imply these (bridge `pappus_hyps`). |
| Pascal2_b_obligation, _obligation' | E | `cov_Pascal2_b_obligation`, `cov_Pascal2_b_obligation'` | — | Repo incidence lemmas. |
| **Pascal3_a (Braikenridge–Maclaurin)** | **O→proved** | `cov_Pascal3_a` (+ `cone_contra`, `pig`, `key3`, `formOf`) | — | The paper does not claim the converse. NEW PROOF in any characteristic. Repo identities `pascalDet_eq_pascalBracket` and `det_verMatrix_eq_neg_pascalBracket` give det V = 0, so some c ≠ 0 has Vc = 0. That c gives a form through all six points. The form satisfies `QNondeg`: if q(x+v) = q(x) for all x, then (Cramer) every conic point lies on one of two lines through [v], and pigeonhole on five points with no three collinear gives a contradiction. Brute force over GF(4), GF(8), GF(16) found no char-2 counterexample (the hyperoval configurations never have collinear Pascal points). |
| Pascal3_a_obligation | O→proved | `cov_Pascal3_a_obligation` | — | |
| **Brianchon1_a** | **N→closed** | `cov_Brianchon1_a` | none after NEW PROOF | Repo `brianchon` takes "lines on a nonzero dual conic" as its hypothesis and **does not define tangency or construct the dual conic**; the paper says so explicitly in §Brianchon. So the repo statement is narrower than the classical tangent-line statement. Closed here by a new polarity argument: tangent = polar (`tangent_iff`), vertex a∩b ↦ chord AB, Pascal points ↦ diagonals (`diagonal_core`), collinear ↔ concurrent (`incidence_core`), applied to `cov_Pascal1_a` (i.e. repo `pascal'`). The repo's `brianchon` / `brianchon_concurrent` is not used. |
| Brianchon1_a_obligation | O→proved | `cov_Brianchon1_a_obligation` | — | Opposite vertices are distinct because their polars are distinct chords. |
| Brianchon2_a_polarIsLine | O→proved | `cov_Brianchon2_a_polarIsLine` | — | Needs char ≠ 2 (and uses it). |
| Brianchon2_a_tangent | O→proved | `cov_Brianchon2_a_tangent` (`tangent_iff`) | — | Holds in **any characteristic**; `hK` is unused. |
| Brianchon2_a_vertex / incidence / diagonal | O→proved | `cov_Brianchon2_a_vertex`, `cov_Brianchon2_a_incidence`, `cov_Brianchon2_a_diagonal` | — | The paper only remarks "duality is literal" in the cross-product model and does not formalise the polarity correspondence. |
| Brianchon2_b (pentagon form) | O→proved | `cov_Brianchon2_b` | — | Dual of `cov_Pascal2_a` via the polarity lemmas. |
| Brianchon2_b_obligation | O→proved | `cov_Brianchon2_b_obligation` | — | |

Count: 20/20 proved. The E statements reduce to repo theorems: Pascal1_a, Pascal2_b and their obligations. Brianchon1_a is N in the repo (dual-conic hypothesis, no tangency) and was closed here. Pascal2_a, Pascal3_a, the Setting lemma, Brianchon2_* and Brianchon2_b are O: the paper does not claim them, and they are now proved. No statement is D: no writer statement is false, and there is no conflict with the repo.

## NEW PROOFS (scratch only, no library edits)
- **Bridge.** Writer submodule-lines ↔ repo/Mathlib `cross`/`orthogonal`/`IsCollinear`: `line_eq_ker`, `join_eq_ker_cross`, `onLine_join_iff`, `collinearPts_iff`, `isMeet_join_iff`.
- `noThreeCollinear`: no three collinear points on a `QNondeg` conic, in any characteristic.
- `tangent_iff`: the "meets the conic only at A" tangent is exactly the polar line, in any characteristic.
- Polarity: `isLine_polarLine` (char ≠ 2), `vertex_core`, `incidence_core`, `diagonal_core`.
- `tangent_pascal_vec`: the five-point Pascal identity, by specialising K[X].
- Braikenridge–Maclaurin: `formOf`, `coeffs_formOf`, `key3`, `pig`, `cone_contra`, `cov_Pascal3_a`.

## Obligations
All 8 writer obligations are **proved**, none carried as hypotheses. There is no sorry, admit or axiom anywhere.

## Checks
- Compile: `jl lake env lean scratch/L15_compare_ax.lean` (the scratch plus 20 `#print axioms` lines), **rc=0**, 0 errors, 8.4 s wall. The only remaining warning is a style lint (`<;>` sequencing).
- Forbidden grep (`sorry|admit|native_decide|axiom`) on `L15_compare.lean`: **no hits**.
- `#print axioms`: all 20 `cov_*` theorems → `[propext, Classical.choice, Quot.sound]`.
- Library hash (`find … -not -path ./.lake/* -not -path ./scratch/* | sort | xargs shasum -a 256 | shasum -a 256`): before `5cd59ae842d9a0c7a4a1f942d4cfe6f88c71a83a83c9d13468ddf8de4e8984f9`, after **identical**. `git status` shows only `?? scratch/`.

## Notes for the paper comparison
1. The paper's Theorem 1 genuinely generalises the textbook Pascal statement: any nonzero Q, char 2 allowed, degenerate conics allowed, and the hypotheses are only consecutive-distinct plus opposite-sides-distinct. The textbook form follows directly.
2. The paper's Brianchon theorem is honest but narrower than the textbook one: the hypothesis is "on a dual conic" and tangency is never connected. L15 closes this gap in char ≠ 2 with roughly 250 lines of polarity lemmas built on the repo's Pascal.
3. Not in the paper but provable cheaply from its identity: the tangent (five-point) form and the Braikenridge–Maclaurin converse, both in any characteristic.
4. Gate portability: `gate.sh` requires GNU `mktemp` and fails on stock macOS.

Wall time: about 1 h 25 min (17:28 → 18:52 EDT).
