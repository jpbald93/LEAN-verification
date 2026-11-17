# L15 — Paper K vs Płatek (arXiv:2604.03067v1): statement-by-statement comparison

Verifier job, host **john** (`Joshs-Mac-Mini.local`, arm64, Lean 4.33.1, project `~/lean/l13_inversion`).
No new mathematics, no edits to Aims or claims. Source = `src/main.tex` (verbatim). Ours = the four
`src/paperK_*.lean` files. Verdicts: **E** equivalent, **O** ours weaker / other (added hypothesis, dropped
conclusion, special case), **N** neither (different object, or no source counterpart at all).

## 1. Recompile evidence (john, independent of jack)

Files copied to `~/lean/l13_inversion/scratch/l15_<name>.lean` (the `scratch/` directory is excluded through
`.git/info/exclude`; `git status --short` was empty before and after — no tracked file touched). sha256 of each
copy on john equals the job copy. Run sequentially, `ps aux | grep -c "[l]ean "` = 0 before each run,
command `lake env lean scratch/l15_<name>.lean`. Raw logs: `recompile/<name>.out`.

| file | namespace | rc | wall | `#print axioms` lines | non-standard axioms | warnings |
|---|---|---|---|---|---|---|
| `paperK_lie_core.lean` (sha 6a19ca20…) | PaperK | 0 | 10 s | 10 | 0 | 0 |
| `paperK_degenerate2d.lean` (sha a77e2e53…) | PaperK2 | 0 | 8 s | 17 | 0 | 1 (style: `unnecessarySeqFocus`, line 272) |
| `paperK_3d.lean` (sha 57af2130…) | PaperK3 | 0 | 6 s | 12 | 0 | 0 |
| `paperK_general_n.lean` (sha 9e28c5a3…) | PaperKn | 0 | 6 s | 13 | 0 | 0 |

Every one of the 52 printed declarations reports exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`,
`admit`, `axiom` or `native_decide` token in any of the four files (grep). All four compile on john; nothing to
report as a compile finding.

## 2. Conventions that every row depends on

SOURCE:
```
(X|Y)=-x_1y_1+\sum_{i=2}^{n+1}x_iy_i+x_{n+2}y_{n+3}+x_{n+3}y_{n+2},
```

SOURCE:
```
X=(r,\, c_1,\,\dots,\, c_n,\, v,\, w)\in V.
```

SOURCE:
```
The homogeneous center is $c=[c_1:\cdots: c_n: v]$, where $v=0$ represents a point at infinity.
```

SOURCE:
```
We denote by $P_{X} = (p_2,\,\dots,\,p_{n+1},\,p_{n+2})$ the point of concurrency of these lines.
```

SOURCE:
```
Note that the radius may be negative. Its sign is determined by the orientation of the cycle.
```

Ours: `PaperK.B`, `PaperK2.B`, `PaperK3.B`, `PaperKn.B` are all `r r' − c·c' − v w' − w v'` on the same coordinate
order `(r, c, v, w)` — i.e. **B = −(·|·)**. The null cone and orthogonality are sign-invariant, so every
statement of the form `B … = 0` transfers verbatim; a statement about the *value* of B (e.g. the power constant
`−B(P,P)/P₃²` in `PaperK.power_eq_of_B_eq_zero`) changes sign in the source convention. The source's affine
centre `[c : v]` is our `PaperK.pt` / `PaperKn.pt` = `c / v`; "not at infinity" is `v ≠ 0`, which in Lean is
`P 3 ≠ 0` (n = 2), `P 4 ≠ 0` (n = 3), `P.v ≠ 0` (general n). Radii are signed (oriented) on both sides; Lean's
tangency is the oriented (Laguerre) equation `‖c − c'‖² = (r − r')²`. Affine cycles are encoded with `v = 1`,
`w = (r² − ‖c‖²)/2` (`PaperK2.circ`, `PaperK3.sph`, `PaperKn.aff`), which is Definition 2.1's relation
`2wv = r² − ‖c‖²` at `v = 1`.

## 3. Comparison table

| row | our statement | source statement | scope | verdict | reason |
|---|---|---|---|---|---|
| Form | `PaperK.B`, `PaperKn.B` | (X\Y) of §2.1 (quoted above) | n = 2, 3, general n | N | B is the negative of the source form: same null cone and same orthogonality, so all zero-set statements transfer, but any statement about a value of B (the power constant) flips sign. |
| Def 2.1 / 2.3 · encoding | `PaperK2.circ`, `PaperK3.sph`, `PaperKn.aff`, `PaperKn.Cyc` | Definitions 2.1 and 2.3 | affine only (v = 1) | O | The constructors realise only the v = 1 chart of Definition 2.1 (spheres with finite centre); hyperplanes (v = 0) exist as raw vectors in `PaperKn.Cyc` but no theorem quantifies over them. |
| K1 · Lemma 2.4 (null cone) | `PaperK.B_self_eq_zero_iff`, `PaperK3.B_self_zero_iff`, `PaperKn.B_self_eq_zero_iff` | Lemma 2.4 (Cycles) | n = 2, n = 3, general n | O | Lean proves only the coordinate identity B(X,X) = 0 ⇔ r² − ‖c‖² = 2vw (the relation of Def 2.1); "represents a cycle" and the projective class are not formalised, so the geometric direction of Lemma 2.4 is not stated. |
| K1 · Lemma 2.5 (tangency ⇔ orthogonality) | `PaperK.tangency_identity`, `PaperK.B_eq_zero_iff_tangent`, `PaperKn.B_eq_zero_iff_tangent`, `PaperK3.tangency_identity` | Lemma 2.5 (Tangency) | n = 2, general n (iff); n = 3 (identity only) | O | Restricted to two spheres with v ≠ 0 on both sides, and "tangent" is defined as the oriented equation (r v' − r' v)² = ‖c v' − c' v‖²; tangency involving hyperplanes or v = 0 is not covered, and both cycles must be null (the identity is false without it, as the K3 docstring notes). |
| K1 · Prop 3.1 | `PaperK.prop31`, `PaperK.prop31_cofactor` | Proposition 3.1 (quoted in §4) | n = 2 only, affine | O | Lean proves the per-index collinearity step: assuming `hspan` (the B-orthogonal complement of the other three rows lies in span{A, A'}) and v ≠ 0 for A, A', P, the point `pt P` lies on the line through `pt A`, `pt A'`; the source's derivation of `hspan` from "exactly two distinct Apollonius cycles", the cycle condition on A, A', and centres at infinity are not formalised; `prop31_cofactor` removes only the existence assumption on P by taking P = G·cofactor. |
| K4 · Prop 3.1 | `PaperKn.prop31` | Proposition 3.1 | general n, affine | O | Same shape as the n = 2 row for n + 2 cycles in ℝⁿ: `hspan` is taken as hypothesis, P is given, v ≠ 0 for A, A', P is assumed, conclusion per index; concurrency of all n + 2 lines is the immediate corollary (one P for every i) but is not itself a stated theorem. |
| K1 · equal power (ours) | `PaperK.equal_power`, `PaperK.power_eq_of_B_eq_zero` | none (closest: the w-shift construction in the proof of Thm 3.6) | n = 2 only | N | No source counterpart: the statement that (P_X, ρ = p_r/p_v) has the same Laguerre power −B(P,P)/p_v² with respect to every cycle orthogonal to P is our reformulation, not a statement of Płatek. |
| K1 · E2 explicit P_X (ours) | `PaperK.explicit_power`, `PaperK.explicit_power_indep` | none (the source gives only existence of P) | n = 2 only, needs det[r a b 1] ≠ 0 | N | Ours: the explicit point (−det[r b s 1], det[r a s 1])/(2D) with ρ = −det[a b s 1]/(2D) has equal Laguerre power to all four circles; the Lean theorem does not state that this point equals `pt` of the cofactor vector or lies on the centre-lines (that link is a hand derivation, see §5). |
| K2 · E1 in ℝ² (ours) | `PaperK2.equal_power`, `PaperK2.PX_circumcentre`, `PaperK2.square_PX`, `PaperK2.equilateral_PX`, `PaperK2.equal_power_point_unique` | none | n = 2 only, equal radii | N | Ours: for three circles of a common radius r₀ with non-collinear centres, every P orthogonal to them with p_v ≠ 0 has `pt P` = circumcentre; square and equilateral instances follow; the continuity / removable-singularity claim of EXTENSION §2 is numerics only and is not in Lean. |
| K2 · overlap with Example (Circumcenter) | `PaperK2.PX_circumcentre` at r₀ = 0 | Example (Circumcenter), §4.1 | n = 2, point cycles | O | At r₀ = 0 the three circles are the vertices as point cycles, so our theorem identifies the source's concurrency point as the circumcentre; it does not prove the source's claim that the perpendicular bisectors concur, and the r₀ = 0 instance must be credited to Płatek's example, not to us. |
| K2 · square: source conclusion ill-posed | `PaperK2.square_apollonius`, `PaperK2.square_apollonius_radii_ne`, `PaperK2.square_null_space` | Proposition 3.1 hypothesis "exactly two distinct Apollonius cycles" | n = 2, one configuration | N | Ours: for the four unit circles of a square, each triple has exactly two affine oriented tangent circles, distinct but concentric, so the source's hypothesis holds among affine cycles while "the line through the centers" is undefined, and the null space is 2-dimensional (P not unique); lines (v = 0) are outside the Lean statement, so "exactly two" in the source's full sense is not established. |
| K3 · Thm 3.6 in ℝ³ | `PaperK3.tetra_thm36` | Theorem 3.6 (quoted in §4) | n = 3 only, one configuration | N | Different statement: Thm 3.6 gives a sphere centred at P_X tangent to every hyperplane in T_i (common tangent hyperplanes of A_i, A_i'); `tetra_thm36` mentions no A_i, no T_i and no hyperplane, it proves P_X = 0 and that the two spheres of radius √3 + 1 and 1 − √3 at P_X are B-orthogonal to the four unit spheres, i.e. that the Apollonius pair of X∖X₅ is centred at P_X — an E1 fact, despite the name. |
| K3 · Morita corollary | `PaperK3.tetra_thm36`, `PaperK3.tetra_tangent_B` | Corollary (K. Morita), `\label{mort}` | n = 3 | N | Not Morita's configuration: the unit spheres at (±1,±1,±1) with an even number of minus signs are pairwise 2√2 apart, so they are not mutually tangent, and no tangent cone or inscribed sphere appears in the Lean statement. |
| K3 · E1 in ℝ³ (ours) | `PaperK3.tetra_PX_origin`, `PaperK3.tetraR_PX_origin`, `PaperK3.tetra_tangent_B`, `PaperK3.equal_power` | none | n = 3 only, regular tetrahedron | N | Ours: for four equal spheres at a regular tetrahedron plus an arbitrary fifth sphere, every orthogonal P with p_v ≠ 0 has P_X = tetrahedron centre; P 4 ≠ 0 is exactly the source's "P_X not at infinity" hypothesis (p_{n+2} ≠ 0). |
| K4 · Thm 3.6 at general n | none (`PaperKn.simplex_E1`, `PaperKn.simplex_circumradius` are not about T_i) | Theorem 3.6 | general n | N | No Lean statement at general n mentions the hyperplane families T_i or the sphere P' of the source proof, so Theorem 3.6 is not formalised in any dimension; `simplex_circumradius` computes the common squared distance from P_X to the centres, a different quantity. |
| K4 · E1 at general n (ours) | `PaperKn.simplex_E1`, `PaperKn.simplex_circumradius`, `PaperKn.dist_sq_const` | none | general n, n + 1 unit spheres | N | Ours: n + 1 affinely independent unit spheres with centroid 0 **and equal centre norms (`hnorm`)** force P_X = 0, and the common squared distance is the circumradius squared; the fifth cycle X₀ is unconstrained and its hypothesis `_hP0` is unused. |
| K4 · hypothesis finding | `PaperKn.simplex_E1` (with `hnorm`), `PaperKn.brief_E_false` | none — the source makes no E1 claim, so it has no such hypothesis to omit | n = 2 counterexample | N | `brief_E_false` refutes in Lean our own brief's centroid version of E1 (right triangle (−1,−1), (2,−1), (−1,2): centroid 0, but P_X = (1/2,1/2), the circumcentre); it refutes nothing in Płatek, and it shows the correct general-n reading is "P_X = circumcentre" (cf. `PaperK2.PX_circumcentre`), with `hnorm` the condition that circumcentre = centroid. |

Source statements with **no Lean counterpart at all** (listed so that nothing is read into silence):

| source item | status |
|---|---|
| Lemma (Decomposition), Definition and Lemma on R_P | not formalised |
| Lemma `\label{interchange}` (R_P swaps A_i, A_i') | not formalised |
| Theorem 3.4 `\label{main1}` (B_i, B_i' lines through P_X) | not formalised; numerically checked at n = 2 only (EXTENSION §0). Note: the source statement lists pairs B_1 … B_n although i runs to n + 2 — a source typo to flag, not ours to fix. |
| Theorem 3.6 `\label{main2}` | not formalised in any dimension (see the K3/K4 rows) |
| Corollary (Morita) `\label{mort}` | not formalised |
| §4 examples and corollaries (incenter, outer Apollonius, mixtilinear, Soddy line, gasket) | not formalised |

## 4. Source statements quoted

Proposition 3.1:

SOURCE:
```
We are given $n+2$ cycles in $ \mathbb{R}^n$ in a set $X=\{X_1,\,\dots, \,X_{n+2}\}$. Let, for all $1 \leq i\leq n+2$ and cycles $X\backslash X_i$, there are exactly two distinct Apollonius cycles $A_i$ and $A_i'$ tangent to each of them. Then the lines through the centers of the pairs of cycles $A_1,\,A_1'$; $A_2,\,A_2';\,\dots$; and $A_{n+2}A_{n+2}'$ are concurrent.
```

The two proof steps our `hspan` hypothesis and the P-existence hypothesis stand in for:

SOURCE:
```
Since this is a homogeneous system of $n+2$ linear equations in $n+3$ variables, such a $[P]$ exists.
```

SOURCE:
```
Then $Y_1$ is a $2$-dimensional subspace of $\mathbb{P}(V)$. Since $[A_1]$ and $[A_1']$ are two distinct projective points of $Y_1$, we have
```

Lemmas 2.4 and 2.5:

SOURCE:
```
A projective point $[X]\in \mathbb{P}(V)$ represents a cycle if and only if $(X|X)=0$.
```

SOURCE:
```
Two cycles $[X]$ and $[Y]$ are tangent if and only if $(X|Y)=0$.
```

Theorem 3.4, conclusion:

SOURCE:
```
Then the lines through the centers of the pairs of cycles $B_1$, $\,B_1';\, B_2,\,B_2';\,\dots;$\\$\,B_n,\,B_n'$, where $B_i \neq B_i'$ for all $i$, are concurrent at a point $P_X$.
```

Theorem 3.6 and its "not at infinity" hypothesis:

SOURCE:
```
We define  $T_i$ $(1 \leq i \leq n+2)$ as the set of hyperplanes tangent to two cycles $A_i$ and $A_i'$. We assume that the point $P_X$, the point of concurrency of the lines through the centers of the solutions to the Apollonius problem, is not a point at infinity. Then there exists a sphere with the center $P_X$ tangent to all hyperplanes in sets $T_1,\,T_2,\,\dots,\,T_{n+2}$.
```

SOURCE:
```
Since $P_X$ is not a point at infinity, we have $p_{n+2}\neq0$.
```

Morita corollary (hypothesis and conclusion):

SOURCE:
```
Let $S_{O1}$, $S_{O2}$, $S_{O3}$, and $S_{O4}$ be four spheres externally tangent to each other and $S$ be an outer sphere tangent to $S_{O1}$, $S_{O2}$, $S_{O3}$, and $S_{O4}$
```

SOURCE:
```
Then there exists a unique sphere inscribed in $\{S_{O1}S_{I1}\}$, $\{S_{O2}S_{I2}\}$, $\{S_{O3}S_{I3}\}$, and $\{S_{O4}S_{I4}\}$.
```

Example (Circumcenter):

SOURCE:
```
The perpendicular bisectors of a triangle are concurrent at a single point, the circumcenter.
```

## 5. Our Lean signatures quoted

```lean
-- file: src/paperK_lie_core.lean
theorem prop31 (X : Fin 4 → Fin 5 → ℝ) (i : Fin 4) (A A' P : Fin 5 → ℝ)
    (hspan : ∀ Y, (∀ j, j ≠ i → B Y (X j) = 0) → Y ∈ Submodule.span ℝ {A, A'})
    (hP : ∀ j, B P (X j) = 0)
    (hA : A 3 ≠ 0) (hA' : A' 3 ≠ 0) (hP3 : P 3 ≠ 0) :
    P ∈ Submodule.span ℝ {A, A'} ∧
      (∃ s t : ℝ, s + t = 1 ∧ pt P = s • pt A + t • pt A') ∧
      Collinear ℝ ({pt P, pt A, pt A'} : Set (ℝ × ℝ)) := by
```

```lean
-- file: src/paperK_general_n.lean
theorem prop31 (X : Fin (n+2) → Cyc n) (i : Fin (n+2)) (A A' P : Cyc n)
    (hspan : ∀ Y, (∀ j, j ≠ i → B Y (X j) = 0) → ∃ α β : ℝ, Y = α • A + β • A')
    (hP : ∀ j, B P (X j) = 0)
    (hA : A.v ≠ 0) (hA' : A'.v ≠ 0) (hPv : P.v ≠ 0) :
    (∃ s t : ℝ, s + t = 1 ∧ pt P = s • pt A + t • pt A') ∧
      Collinear ℝ ({pt P, pt A, pt A'} : Set (Fin n → ℝ)) := by
```

```lean
-- file: src/paperK_3d.lean
theorem tetra_thm36 (r a b c : ℝ) (P : Fin 6 → ℝ)
    (hP : ∀ i, B P (tetraFam r a b c i) = 0) (hP4 : P 4 ≠ 0) :
    (P 1 / P 4 = 0 ∧ P 2 / P 4 = 0 ∧ P 3 / P 4 = 0) ∧
    (∀ i : Fin 4,
      B (sph (Real.sqrt 3 + 1) (P 1 / P 4) (P 2 / P 4) (P 3 / P 4))
        (tetraFam 0 0 0 0 (Fin.castSucc i)) = 0 ∧
      B (sph (1 - Real.sqrt 3) (P 1 / P 4) (P 2 / P 4) (P 3 / P 4))
        (tetraFam 0 0 0 0 (Fin.castSucc i)) = 0) := by
```

```lean
-- file: src/paperK_general_n.lean
theorem simplex_E1 {m : ℕ} (hm : m = n + 1) (c : Fin m → Fin n → ℝ)
    (hsum : ∑ i, c i = 0) (hc : AffineIndependent ℝ c)
    (hnorm : ∀ i j, ∑ k, (c i k)^2 = ∑ k, (c j k)^2)
    (X₀ : Cyc n) (P : Cyc n) (hPv : P.v ≠ 0)
    (hP : ∀ i, B P (aff 1 (c i)) = 0) (_hP0 : B P X₀ = 0) :
    pt P = 0 := by
```

```lean
-- file: src/paperK_general_n.lean
theorem brief_E_false : ¬ (∀ (c : Fin 3 → Fin 2 → ℝ), ∑ i, c i = 0 → AffineIndependent ℝ c →
    ∀ (X₀ P : Cyc 2), P.v ≠ 0 → (∀ i, B P (aff 1 (c i)) = 0) → B P X₀ = 0 → pt P = 0) := by
```

Reviewer notes on the signatures (observations, not new results): in `PaperK.prop31` the vectors A, A' need
not be null and the rows X j need not be cycles, so the theorem is pure linear algebra; the geometric content of
Prop 3.1 sits entirely in `hspan`. In `PaperKn.simplex_E1`, given `hnorm` and `hc` the origin is already the
circumcentre, so `hsum` looks mathematically redundant there (not checked in Lean). The E2 ↔ P_X link: matching
`PaperK.row_relation` against B(P, X_i) = 0 gives P = (q₀, −q₁, −q₂, 2q₃, −q₄) for q = cofactor(`PaperK.Mrow`),
whose `pt` is exactly the `explicit_power` point and whose v-slot is −2·det[r a b 1] — so `hD` is the
"not at infinity" condition for that vector; this is a hand check by the verifier, not a Lean theorem.

## 6. Ours, not the source's

Nothing in this section may be attributed to Płatek, and nothing above that is Płatek's may be presented here.

- **E2 — explicit formula for P_X (n = 2).** `PaperK.explicit_power`, `PaperK.explicit_power_indep`: with
  D = det[r a b 1] ≠ 0, the point (−det[r b s 1], det[r a s 1])/(2D) and radius −det[a b s 1]/(2D) have equal
  Laguerre power to all four circles. The source has no formula. Only n = 2. The K1 file records that the brief's
  own display had the a/b columns swapped and failed numerically; the Lean version uses the corrected sign.
  The identification with the concurrency point is the hand check in §5, not Lean.
- **Equal-power lemma.** `PaperK.equal_power`, `PaperK2.equal_power`, `PaperK3.equal_power`,
  `PaperKn.equal_power`: every cycle orthogonal to P has the same Laguerre power from (P_X, p_r/p_v).
  Mechanism for E1; no source statement.
- **E1 — degenerate / symmetric locus.** Equal-radius triangle (`PaperK2.PX_circumcentre`), equilateral triple
  (`PaperK2.equilateral_PX`), square with its 2-dimensional null space and concentric Apollonius pairs
  (`PaperK2.square_PX`, `PaperK2.square_apollonius`, `PaperK2.square_null_space`), regular tetrahedron
  (`PaperK3.tetra_PX_origin`, also under the misleading name `PaperK3.tetra_thm36`), regular simplex with `hnorm`
  (`PaperKn.simplex_E1`). In each case P_X is the symmetry centre / circumcentre. **Not formalised:** the
  continuity and Lipschitz convergence of P_X to that centre (EXTENSION §2, numerics only) and the
  P_X-at-infinity hyperplane statement (EXTENSION §2b/§3 E1(3), not even checked numerically).
- **Correction of our own E1 at general n.** `PaperKn.brief_E_false`: the centroid version is false; the
  `hnorm` version is proved. A refutation of our brief, not of the source.
- **The negative result below.**

### Negative result — the completion map does not fix P_X

The natural strengthening "the Apollonius completion map fixes the concurrency point" (i.e. the derived
configuration built from the B_i has concurrency point P_X again) is **false**: in 6 generic n = 2
configurations (`iterate.py`) the derived configuration's own concurrency point differs from P_X by 5.7e-02 to
3.1e-01, while Theorem 3.4 holds in the same runs to residual ≤ 8.7e-14. So the completion map does not fix P_X; the derived configuration has its own, different concurrency point.
Status: **numerical refutation only** — there is no Lean counterexample in the four files, and none is claimed.
It refutes a conjecture of ours, not anything Płatek states (Theorem 3.4 is about the B_i lines meeting at the
*original* P_X, which is consistent with this). Reference: `AFM/PaperK/EXTENSION.md` — the brief cites §2, but in
the file this result is **§1** ("Hypothesis tested and REFUTED"); §2 is the degenerate locus.

## 7. Gate output

`python3 check_l15.py` (checks: every `PaperK*.name` identifier and every quoted Lean block against the four
`src/*.lean` files; every `SOURCE:` block verbatim in `src/main.tex` after whitespace normalisation; every
verdict-table row has a verdict in {E, O, N} and a non-empty reason; the negative-result heading is present):

```
L15 GATE PASS (17 rows, 44 ids, 16 source quotes)
(gate tamper check by the verifier: 7 planted defects — misspelt id, wrong namespace, altered SOURCE quote,
verdict "E?", altered Lean signature, removed negative-result heading, emptied reason — each gave L15 GATE FAIL)
```

## 8. What this means for the Paper K claims

**May be published as formalisations of Płatek** (with the scope stated, never as "Prop 3.1 formalised"
unqualified): the coordinate content of Lemmas 2.4/2.5 for spheres with finite centre (n = 2, 3, general n),
and the linear-algebra core of Proposition 3.1 — the collinearity step given the two-dimensional orthogonal
complement — at n = 2 (`PaperK.prop31`, `PaperK.prop31_cofactor`) and general n (`PaperKn.prop31`), affine
chart only. No row is **E**: the step from "exactly two distinct Apollonius cycles" to `hspan`, Theorem 3.4,
Theorem 3.6 and the Morita corollary are **not** formalised, and `PaperK3.tetra_thm36` must not be described as
Theorem 3.6 or Morita (rename recommended, e.g. `tetra_apollonius_centre`; claims not edited here).

**May be published as extensions (ours):** E2 (explicit P_X at n = 2, with the cofactor link stated as a
derivation), the equal-power lemma, and E1 in its proved form — P_X is the circumcentre for equal radii in ℝ²,
the centre for the square, equilateral triple, regular tetrahedron and regular simplex (`hnorm`); plus the
observation that the square satisfies Prop 3.1's hypothesis among affine cycles while its conclusion is
undefined. The continuity / Lipschitz part of E1 and the P_X-at-infinity part are numerical claims only.

**Must be stated as refuted:** (a) our brief's general-n E1 without `hnorm` (centroid version) — refuted in Lean
by `PaperKn.brief_E_false`; the correct reading is circumcentre; (b) "the completion map fixes P_X" — refuted
numerically (EXTENSION §1), no Lean proof. Neither refutes any statement of Płatek.
