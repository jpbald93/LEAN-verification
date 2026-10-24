# L15 classical comparison — Paper CaseyFuss

Comparer: Layer 15 (not blind). Writer file: `/tmp/blindCaseyFuss/Classical.lean` (blind, 9 statements incl. 2 obligations).
Machine: jack (`jack`). Every `lake`/`lean` call ran under `flock ~/l15jack.lock`.

## Repositories (fresh clones of the published pinned commits)
| repo | path | commit (= paper `\commitcasey` / `\commitfuss`) | Mathlib | gate |
|---|---|---|---|---|
| casey | `~/l15CaseyFuss_casey` | `a83c43b8d7c8b1b98c213366cfa27eec8b8ad6c3` (HEAD; the paper's text says "line references to 5f6252c", while its macro pins a83c43b = 5f6252c + `Casey/Bridge.lean`) | `0df444a3…` → `.lake/packages` symlinked to `~/barbier/.lake/packages` | `PASS (18 declarations, standard axioms only)` rc=0 |
| fuss | `~/l15CaseyFuss_fuss` | `671efdc610147022ef66e9794988ba72114f85a4` (HEAD) | `0df444a3…` (same symlink) | `PASS (34 declarations, standard axioms only)` rc=0 |

Gate logs: `jack:~/l15CaseyFuss_gate_casey.log`, `jack:~/l15CaseyFuss_gate_fuss.log`.

## Result table
| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| `classical_CaseyFuss1_a_obligation` | **E** | `cov_CaseyFuss1_a_obligation` | — | radicand ≥ 0 via `Casey.dist_tangentCentre_sq_sub_sq` + NEW bridge |
| `classical_CaseyFuss1_a` | **E** | `cov_CaseyFuss1_a` | — | via `Casey.casey_of_le`. The disjointness hypothesis `hdisj` is **not needed** (and the repo's `casey` uses neither it nor `rᵢ < R`) |
| `classical_CaseyFuss1_b_obligation` | **E** | `cov_CaseyFuss1_b_obligation` | — | |
| `classical_CaseyFuss1_b` | **E** | `cov_CaseyFuss1_b` | — | both conjuncts: chord formula from `Casey.tangentLength_tangentCentre` (+`Real.sqrt_mul`), Casey relation from `Casey.casey_of_le` (signed radii) |
| `classical_CaseyFuss1_c` (converse) | **D** (as written false) + **O** | `not_classical_CaseyFuss1_c : ¬ classical_CaseyFuss1_c` | — | The paper does not claim the converse (README: "The converse … not formalised"). The writer's formalisation is **false**: C₀ is the unit circle, C₁ is the point (1,0), C₂ = C₃ is the point (−1,0), with all ε = s₁ = s₂ = +1. Then t₀₁ = t₀₂ = t₀₃ = 0, so the relation holds. But no circle Γ and no line meets C₀ in exactly one point while passing through both (1,0) and (−1,0). The textbook converse tacitly needs distinct/non-degenerate circles, and the writer added no such hypothesis, so this is a **writer mis-statement** (missing non-degeneracy). It is not a disagreement with the paper. |
| `classical_CaseyFuss2_a` | **N** | `cov_CaseyFuss2_a_part` | (i) extra hypothesis `x < R`; (ii) the clause `x = 0 ↔ ABCD square` | Part proved: all of (reciprocal form, (R²−x²)² = 2r²(R²+x²), x² = R²+r²−r√(4R²+r²), √2 r ≤ R, R = √2 r ↔ x = 0) for the writer's convex `BicentricWith`, plus `x < R`. Route: NEW `isBicentric_of_with` (writer's convex incircle ⇒ repo `Fuss.IsBicentric`) → `Fuss.fuss_of_isBicentric` (needs `d ≠ R`) → `Fuss.fuss_iff_reciprocal` + NEW algebra `fuss_algebra`. `x < R` is classically automatic for convex bicentric quadrilaterals, because I is inside the quad, which is inside Γ. It is not derived here, because the repo's line-tangent notion allows x = R (crossed example in the paper). The square clause is classically true but not formalised in the repo and was not attempted. The paper is narrower here; the writer's statement is believed correct. |
| `classical_CaseyFuss2_b` (converse) | **N** | `cov_CaseyFuss2_b_part` | convexity of the produced quadrilateral and contact points on the sides (`BicentricWith` vs `Fuss.IsBicentric`) | Proved with the repo's notion (4 distinct points on Γ, side **lines** tangent to ω). The paper explicitly does not claim convexity ("What is not claimed"). The paper is narrower. |
| `classical_CaseyFuss3_a` | **N** | `cov_CaseyFuss3_a_part` | in the 3 conclusions, `BicentricWith` (convex + contact points on segments) is weakened to `Fuss.IsBicentric` | Hypotheses are the writer's verbatim (incl. `hex` with convex `BicentricWith`). Proved: (1) a quad through every P ∈ Γ; (2) the writer's chain (consecutive distinct, `LineTangent` = exactly one common point, no backtracking) has p₄ = p₀ and p₃ ≠ p₀, and (p₀..p₃) is `IsBicentric`; (3) the set of quadruples is infinite. NEW for (2): `tangentAt_of_lineTangent` (unique common point ⇒ Mathlib `IsTangentAt`, via `secondInter`), `not_three` (no three points of Γ on one tangent ⇒ T_n ≠ T_{n+1}), and `Fuss.poncelet_chain_closes` applied to the shifted chain p₁…p₅. NEW for (3): Γ is infinite (connected sphere, `isConnected_sphere` + countable ⇒ totally disconnected), and q ↦ q 0 is onto Γ. |
| `classical_CaseyFuss3_b` | **N** | `cov_CaseyFuss3_b_part` | ⇐ direction and the "through every point" clause only with `Fuss.IsBicentric` (not convex `BicentricWith`) | The ⇒ direction is proved exactly as written (from convex `BicentricWith`; x < R follows here from `StrictlyInside`). The paper is narrower (no convexity claim). |

Summary: 4 E (1a, 1a-obl, 1b, 1b-obl), 4 N (2a, 2b, 3a, 3b), 1 D (1c is false as written, writer mis-statement; also O, since the paper does not claim the converse).

## NEW PROOFS (all in scratch, none in the library)
- casey scratch: `tc_eq` (a centre with the right distances is `Casey.tangentCentre`), `int_dist`/`ext_dist` (the writer's `InternallyTangentAt`/`ExternallyTangentAt` ⇒ |OC| = R ∓ r, |KC| = r, |KO| = R), `signed_bridge`, `no_mid`, `cyc_angles` (writer's `CyclicOrder4` on a circle ⇒ Mathlib/Casey angle-π cyclic order), `casey_signed`, `radicand_nonneg`, counterexample `not_classical_CaseyFuss1_c`.
- fuss scratch: `tangentAt_of_side` (writer's `TangentToSide` ⇒ `IsTangentAt`, by a quadratic-minimum argument), `ne_of_not_collinear`, `isBicentric_of_with`, `fuss_of_with`, `fuss_algebra` (all algebraic consequences incl. √2 r ≤ R and the equality case), `fuss_of_recip`, `tangentAt_of_lineTangent`, `not_collinear_of_mem`, `not_three`, infinitude of Γ inside `cov_CaseyFuss3_a_part`.

## Obligations
Both writer obligations (`classical_CaseyFuss1_a_obligation`, `classical_CaseyFuss1_b_obligation`) are **proved** (E). No construction obligation was carried as a hypothesis. The only extra hypothesis anywhere is `hdR : x < R` in `cov_CaseyFuss2_a_part`, stated as a theorem hypothesis (no sorry/axiom).

## Compile
- `jack:~/l15CaseyFuss_casey/scratch/L15_compare.lean` (395 lines, sha256 `d429bcb3…01f26`): `flock ~/l15jack.lock lake env lean scratch/L15_compare.lean` **rc=0**, 0 errors, 2 linter warnings (deprecated `push_neg`, unused simp arg). Log: `jack:~/l15CaseyFuss_casey_cmp.log`.
- `jack:~/l15CaseyFuss_fuss/scratch/L15_compare.lean` (417 lines, sha256 `140a7000…c42ac0f3`): **rc=0**, 0 errors, 0 warnings. Log: `jack:~/l15CaseyFuss_fuss_cmp.log`.
- Local copies: `<ws>/AFM/L14L15/CaseyFuss/{casey_L15.lean,fuss_L15.lean}` (also `/tmp/l15cf/`).

## Forbidden grep
`grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|\baxiom "` on both scratch files: no matches (grep rc=1). `set_option linter.unusedVariables false` is used only in scratch, to silence binder warnings from the verbatim `∀` packaging.

## #print axioms (all `[propext, Classical.choice, Quot.sound]`)
cov_CaseyFuss1_a, cov_CaseyFuss1_a_obligation, cov_CaseyFuss1_b, cov_CaseyFuss1_b_obligation, not_classical_CaseyFuss1_c, cov_CaseyFuss2_a_part, cov_CaseyFuss2_b_part, cov_CaseyFuss3_a_part, cov_CaseyFuss3_b_part, isBicentric_of_with.

## Library hashes (before = after)
- casey: `f282f47b5e15e95eee25d62b94c80159470ff6ac0266c66577d3eb921129fc59` / same
- fuss: `48394675e1507936fba87e33b0c2a3765d1363902f31c47078966f814a3ede31` / same
`git status`: only `?? scratch/L15_compare.lean` in each clone.

## Wall time
About 75 min (clone at epoch 1792660257 to report). No l14/battery/other dirs touched; the only background PID started was the gate runner (484423, finished).
