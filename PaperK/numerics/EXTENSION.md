# Paper K — extension design and numerical evidence (2026-11-10)

Josh's instruction: **"Try to extend it"** — extend Płatek (arXiv:2604.03067) rather than formalise it as
published. This file records what the numbers say *before* any proof is dispatched, per
`AFM/NOVELTY_SCOUT_PROTOCOL.md`. Code: `AFM/PaperK/num/` (`apollonius.py`, `iterate.py`, `atinfinity.py`,
`t_i.py`). All checks are double-precision numerics; nothing here is a proof.

## 0. What was confirmed first (the sanity check I owed you)

`apollonius.py` implements the oriented Apollonius solve exactly as the Lie model forces it: unknown
`(x, r) ∈ ℝⁿ × ℝ` with signed radius, tangency `|x−c_i|² = (r+ρ_i)²`, subtract the first equation to get `n`
linear equations, parametrise `x = x₀ + w r`, and solve the resulting quadratic in `r` (two roots = the
`{A_i, A_i'}` of the paper). This also pins the orientation convention: negative `r` is the enclosing cycle.

| check | dimension | result |
|---|---|---|
| **Prop 3.1** (the `n+2` pair-lines concur at `P_X`) | n = 2, 3, 4 | holds; max distance from a line to the fitted point 1.3e-14 … 1e-16 relative |
| **Thm 3.4** (the derived `B_i, B_i'` lines pass through the same `P_X`) | n = 2 | holds; residual 2.5e-14 … 5.2e-16 |

So the source paper's two main statements are numerically sound where the configuration is non-degenerate, and
the brief for any proof job can hand the runner a worked example rather than a hope.

## 1. Hypothesis tested and REFUTED (negative result)

**"The completion map fixes the concurrency point."** Natural guess: since Thm 3.4 shows the derived cycles
`B_i` produce lines through `P_X`, maybe `P` of the derived configuration `{B_i}` is again `P_X` — which would
make `P` an invariant of the Apollonius dynamics and a strong extension.

False. `iterate.py`, 6 generic configurations at n = 2 where every step is well defined:

```
trial 2:  |P({B_i}) − P_X| = 7.7e-02      (Thm 3.4 residual 3.9e-14)
trial 3:  |P({B_i}) − P_X| = 3.1e-01      (2.5e-14)
trial 20: 2.8e-01                          (5.2e-16)
trial 23: 5.7e-02                          (8.7e-14)
trial 29: 8.4e-02                          (1.3e-14)
trial 36: 5.7e-02                          (3.9e-14)
```

The derived configuration's own concurrency point is a *different* point, consistently, while Thm 3.4 itself
holds to machine precision in the same runs. This is recorded as a negative result: it kills a plausible
paper claim and it should be stated in the paper, because a reader will ask.

## 2. Extension candidate found: the degenerate locus is real and reachable

Płatek's statements are about a *line through the centres* of `A_i` and `A_i'`. Two ways that line can fail to
exist are not excluded, and both occur:

**(a) Concentric pairs.** For the four unit circles at the corners of a square, all four subsets have their two
Apollonius cycles *concentric* at the centre (`t_i.py`):

```
i=0: A=(0,0) r=−2.4142 ;  A'=(0,0) r=0.4142   (centre-line direction 0 — the line is undefined)
... same for i = 1, 2, 3
```

The theorem's conclusion is then vacuous as stated, yet the configuration obviously has a distinguished point:
the common centre. So `P_X` has a continuous extension to this locus, and the extension is *not* the paper's
statement.

**This is now verified, not just observed (`degenerate.py`, `continuity.py`).** Three equal circles in
equilateral position plus a fourth circle: the subset without the fourth has concentric Apollonius cycles, so
its pair-line does not exist — yet the remaining three lines still concur (residual 1.8e-15) at exactly the
triangle's centre `(1, √3/3)`. Same in ℝ³ with a regular tetrahedron of unit spheres plus a fifth sphere: the
remaining four lines concur at the tetrahedron's centre `(0,0,0)` (residual 1.2e-14).

Continuity, measured: perturb one of the equilateral circles by `d` and follow `P` (`continuity.py`):

```
d=1e-1  |P − centre| = 2.9e-03      (concurrence residual 1.8e-15, 3 lines)
d=1e-2  |P − centre| = 2.9e-05                        (3.6e-15)
d=1e-3  |P − centre| = 2.9e-07                        (4.0e-15)
d=1e-4  |P − centre| = 2.9e-09                        (7.9e-15)
d=1e-5  |P − centre| = 2.9e-11                        (7.3e-15)
```

`P` converges to the symmetry centre at first order in the perturbation, and Płatek's concurrency holds exactly
at every `d > 0`. So the degenerate locus is removable, the limit value is the symmetry centre, and the
convergence is Lipschitz — a statement the source paper does not make.

**(b) `P_X` at infinity / far away.** Over 3000 random configurations the concurrence system reaches condition
number 1.5e6 with `P_X ≈ (855, 293)`, so `P_X` moves continuously toward infinity in reachable families.
Płatek's Thm 3.6 needs `P_X` **not** at infinity as an explicit hypothesis — the case is not covered by his
paper, and it is exactly the case the degenerate families approach.

## 3. The extension the paper should claim (proposal)

**Statement E1 (total version).** Let `X = {X_1, …, X_{n+2}}` be cycles in ℝⁿ with `Ap(X∖{X_i}) = {A_i, A_i'}`
(the two solutions of the oriented Apollonius problem, by the quadratic of §0). Then:

1. whenever the `n+2` centre-lines are defined and no two are parallel in a bad way, they concur at `P_X` (Płatek, Prop 3.1 — *not ours*);
2. on the symmetric locus where `A_i` and `A_i'` are concentric for some `i`, the pair-line of that subset does not exist, the remaining `n+1` lines still concur, and their point converges to the symmetry centre of the configuration — with the convergence Lipschitz in the perturbation (§2a, verified in ℝ² and ℝ³);
3. `P_X` at infinity is a genuine case; Thm 3.6's conclusion then degenerates to a hyperplane statement rather than failing.

**Statement E2 (quantitative).** An explicit coordinate expression for `P_X` in the given data (the source
gives only an existence proof through the Lie construction), the radius of the inscribed sphere of Thm 3.6 as an
explicit function, and continuity of both as the configuration varies. This is the part that makes the Lean
development concrete and is the most defensible "extension" claim: the paper states the theorems, it does not
compute.

**Statement E3 (optional, later).** The same statements in the space forms `Sⁿ` and `Hⁿ`: the Lie model is
uniform, the paper restricts to ℝⁿ, so the transport is a real extension — but it is heavy and should not gate
the paper.

**Explicitly not claimed:** any invariance of `P_X` under the Apollonius completion (§1), and any first-ness of
Prop 3.1 / Thm 3.4 / Thm 3.6 themselves — those are Płatek's.

## 4. What must be checked before dispatch

- **Done:** Prop 3.1 (n = 2, 3, 4), Thm 3.4 (n = 2), the refutation of the fixed-point claim, the degenerate
  locus and its continuity (ℝ², ℝ³).
- **E1(3)**, the `P_X`-at-infinity case: compute the hyperplane families `T_i` in a configuration with `P_X`
  far out, and check the predicted limiting hyperplane direction. Not done.
- **E2**, the explicit formula for `P_X`: derive it symbolically with sympy for a general `n = 2` configuration
  and check against the numerical `P_X`. This is the gate for the first Lean dispatch — the job must be handed
  a formula, not a hope.
- **Scout delta** for the extension: confirm E1's degenerate statement and E2's formula appear neither in
  Płatek's §3–4 (his text has no formula and no degenerate discussion) nor in the 2026 literature. Partly
  checked; the formula half cannot be checked until it exists.
