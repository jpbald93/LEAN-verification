# K0 — the Lie form and the explicit formula for P_X (Płatek, arXiv:2604.03067)

Files: `formula.py` (run `python3 formula.py`; output saved in `formula_output.txt`).
Coordinates as in Def 2.3: X = (r, c_1..c_n, v, w), slots numbered 1..n+3 as in the paper
(r = slot 1, c = slots 2..n+1, v = slot n+2, w = slot n+3). For a sphere with centre x and
radius r we normalise v = 1, c = x, w = (r^2 - |x|^2)/2.

## 1. The form

    (X|Y) = r r' - c·c' - v w' - w v',      G = diag(1, -I_n, [[0,-1],[-1,0]]),  G^2 = I,
    (X|X) = r^2 - |c|^2 - 2vw.

Signature (2, n+1): this is the Lie quadric.

**Lemma 2.4 holds.** Def 2.1 imposes 2wv = r^2 - |c|^2, which is literally (X|X) = 0. Conversely a
nonzero null X with v != 0 is a sphere (radius r/v, possibly 0 = point sphere); with v = 0 it has
r^2 = |c|^2, so c != 0 gives the hyperplane -2c·x - 2w = 0 with orientation sign(r)·c/|c|, and c = 0
forces r = 0, X = (0,..,0,w): the point at infinity.

**The form is unique up to scale** (so the brief's question "which form" has exactly one answer).
Proof: a symmetric β vanishing on all cycles vanishes on the real points of the nondegenerate
indefinite quadric {Q = 0}, which are Zariski dense in it; the quadric is irreducible (rank ≥ 3), so
its ideal is (Q) and a quadratic form in it is λQ. Also checked symbolically at n = 2 (solve all 15
coefficients of β from β(X,X) ≡ 0 on v = 1 cycles → β = λG).

**Lemma 2.5: the identity.** For any two cycles (verified symbolically, n = 3, with w eliminated):

    -2 v v' (X|Y) = (r v' - r' v)^2 - |c v' - c' v|^2 .

With v = v' = 1:  -2(X|Y) = (r - r')^2 - |x - x'|^2.  Hence

    (X|Y) = 0   <=>   |x - x'| = |r - r'|      (oriented contact).

Sphere/hyperplane (v' = 0, unit normal u = c'/r', offset d = -w'/r'): (X|Y)/r' = r - (u·x - d),
tangent iff the signed distance of the centre equals r. Two hyperplanes: (X|Y) = |c||c'|(1 - cos θ),
zero iff parallel with the same orientation (contact at infinity).

**The "naive" problem and its repair.** `apollonius.py` uses |x - x'| = |r + r'|. Under that
convention the same identity gives (X|Y) = 2 r r' (formula.py prints 2.000 for two externally
tangent unit circles), never 0. Since Lemma 2.4 already forces the form to be λQ, **no symmetric form
makes Lemma 2.4 and 2.5 hold simultaneously with the |r + r'| convention** — the obstruction is the
displayed identity. What works: keep the form, and read the radius slot as the *Lie* signed radius,
r_Lie = -r_ref (equivalently: tangency = oriented contact, same-sign radii touch internally). This
is a convention change on the data, not on the form. Crucially it does not affect P_X: negating all
radii maps X ↦ diag(-1, I) X, which maps the witness P ↦ (-p_1, p_2, ..., p_{n+3}) and leaves the
centre slots and the v-slot unchanged up to a common sign (checked: P_X identical to machine zero).
Each reference Apollonius solution (x, r) is the Lie solution (x, -r), same centres, same lines.

## 2. The witness P

Let X be the (n+2)×(n+3) matrix with rows X_i and M = X G (rows X_i^T G). Define the generalised
cross product ×(A)_k = (-1)^k det(A with column k deleted) (k = 0..n+2, 0-based). Then

    P = ×(X G) = (-1)^{n+1} G ×(X)        [×(AG) = det G · G^{-1} ×(A), det G = (-1)^{n+1}]

and M P = 0 by Laplace expansion of a determinant with a repeated row. P ≠ 0 iff rank M = n+2.
Writing q = ×(X), the slots of P are (q_r, -q_c, -q_w, -q_v) (G swaps v and w). So the v-slot of
P is (up to sign) the minor with the **w-column** removed:

    p_{n+2} ∝ D := det[ r_i | x_i | 1 ]_{i=1..n+2}           ((n+2)×(n+2)),
    P_X = (p_2, ..., p_{n+1}) / p_{n+2}.

**Remark 3.2 normalisation.** In 1-based slots p_2..p_{n+1} are the c-slots and p_{n+2} the v-slot,
so P_X = (p_2 : ... : p_{n+1} : p_{n+2}) is exactly the homogeneous centre [c : v] of Def 2.1 applied
to P; the affine point is (p_2..p_{n+1})/p_{n+2}; p_1 and p_{n+3} drop out. This is the only reading
consistent with "centres collinear" in the proof (centre of αA + βA' is an affine combination of the
two centres with weights ∝ α v_A, β v_A').

**Equivalent linear form (useful for Lean later).** Normalising P = (ρ, x, 1, w_P), the n+2
equations (P|X_i) = 0 read ρ r_i - x·x_i - w_i = w_P, i.e.

    |x - x_i|^2 - (ρ - r_i)^2 = -(P|P)      for all i  (same value for every i).

So P_X is the **Laguerre radical centre** of the n+2 oriented spheres: the centre of the
(generally imaginary) cycle with equal Laguerre power to all of them; ρ is its radius. Subtracting
i = 1 gives the (n+1)×(n+1) linear system ρ(r_i - r_1) - x·(x_i - x_1) = w_i - w_1, i = 2..n+2,
whose Cramer denominator is D. P is itself a cycle iff that common power is 0, i.e. iff there is an
oriented sphere tangent to all n+2 data spheres.

### n = 2 written out

Circles (a_i, b_i; r_i), i = 1..4, with s_i = a_i^2 + b_i^2 - r_i^2 (= -2w_i). Columns are 4-vectors:

    P = ( -½ det[a b s 1],  -½ det[r b s 1],  ½ det[r a s 1],  det[r a b 1],  ½ det[r a b s] )
          slot r             slot c1           slot c2          slot v         slot w

    P_X = ( -det[r b s 1],  det[r a s 1] ) / ( 2 det[r a b 1] ).

(Checked against the generic cofactor code to 7.7e-16 and against the closed form `px_n2_closed`
to 1.3e-15 on 2000 random signed configurations.)

## 3. Numerical comparison (formula vs `apollonius.py` + `point_from_lines`)

Relative difference |P_formula - P_ref| / max(1, |P_ref|), over configurations where the reference is
defined (all n+2 Apollonius problems have two real solutions):

| n | radii | defined / 3000 | max rel diff | median | max distance of P_formula to the 2(n+2) centre-lines (rel) |
|---|-------|---------------|--------------|--------|------|
| 2 | positive | 2443 | 6.1e-10 | 6.9e-16 | 1.7e-13 |
| 2 | signed   | 1136 | 7.6e-12 | 6.8e-16 | 1.7e-13 |
| 3 | positive | 1920 | 3.9e-09 | 9.4e-16 | 3.9e-13 |
| 3 | signed   |  542 | 6.9e-12 | 9.1e-16 | 2.8e-13 |
| 4 | positive | 1708 | 5.9e-12 | 1.2e-15 | 5.4e-12 |
| 4 | signed   |  391 | 8.0e-12 | 1.2e-15 | 5.9e-13 |

On the exact `prop31` configurations (seeds 100+n) the differences are 1.6e-16 … 1.9e-14.
The two outliers above 1e-10 are reference-side conditioning: the n = 3 worst case has |P| ≈ 3046
and cond(point_from_lines matrix) ≈ 1.2e8, while the formula's point lies on all reference lines to
< 4e-13. Lemma checks: max |(X|X)| = 1.8e-15 on random cycles, max |(X|Y)| = 7.1e-15 on random
oriented-contact pairs.

## 4. Degenerate cases

**(a) Four unit circles at the corners of a square (or any rectangle).** Here M has rank n+1 = 3
(singular values 3, 2, 2, 0 for the square), so **the cofactor vector P is identically 0** — neither
"p_{n+2} = 0" nor "P is a cycle"; the formula is 0/0. Reason: all four triples have the *same*
Apollonius pair A, A' (concentric at the centre, Lie radii 1 ∓ √(w²+1)), so all four X_i lie in the
3-dim space ⟨A, A'⟩^⊥ and are linearly dependent; the kernel is 2-dimensional and equals ⟨A, A'⟩
(verified). Every kernel vector has c = 0, so every witness with v ≠ 0 has centre at the symmetry
centre — the "remaining structure" is the kernel, not a line. (The one kernel direction with v = 0,
A·v_A' - A'·v_A, also has c = 0 and so no centre at all.) The formula's value is recovered as a limit:

*Proposition (proven).* If rank M = n+1 and ker M ⊂ {c = 0}, then for any perturbation M + εE the
c-slots of ×(M + εE) are O(ε²) while the first-order term lies in ker M. Proof: the ε¹ term is
Σ_j ×(M with row j replaced by E_j); it annihilates every row M_k, k ≠ j, trivially, and
M_j · ×(…E_j…) = ± E_j · ×(M) = 0. So when that kernel element has v ≠ 0, P_X = O(ε) → the
symmetry centre. Observed: perturbing centres and radii by ε gives max |P_X| over 200 random
directions = 1.8e0, 4.9e-3, 8.0e-5 for ε = 1e-2, 1e-4, 1e-6 (O(ε) with a direction-dependent constant;
uniformity of that constant is NOT proven). For a rectangle the reference code returns "P = None",
which is this rank drop, not a point at infinity.

**(b) Three unit circles in equilateral position + a fourth circle (radius ≠ 1).** M has full rank,
p_{n+2} ≠ 0 (e.g. 2.25, 1.04, -5.20 for different fourth circles) and **P is not a cycle**
((P|P)/|P|² = 0.13 … 0.56). P_X is exactly the triangle centre for *every* fourth circle (errors
0 … 1.2e-15), with a one-line proof from the Laguerre form: equal power to three circles of equal
radius gives |x - x_1| = |x - x_2| = |x - x_3| for any ρ, so x is the circumcentre; the fourth equation
only fixes ρ. The concentric triple-pair contributes no line, but the formula never needs lines.
Breaking the symmetry by d moves P_X by 2.887·d² (2.9e-3, 2.9e-7, 2.9e-11 for d = 1e-1, 1e-3, 1e-5),
matching `continuity.py` digit for digit. Extra observation: if the fourth radius is also 1, the
r-column equals the 1-column, so D = 0 *and* the c-slots vanish: P ∝ (1, 0, 0, 0, 1) (a non-null
vector, (P|P) = 1) and P_X has no centre — equal radii give no information about the point.

**When is p_{n+2} = 0 with c ≠ 0 (P_X at infinity)?** Exactly when D = det[r | x | 1] = 0, i.e. the
points (x_i, r_i) ∈ R^{n+1} lie on a common affine hyperplane. This explains the large condition
numbers in `atinfinity.py`.

## Proven vs guessed

Proven (algebra above, with symbolic/numeric confirmation):
- the form, its uniqueness up to scale given Lemma 2.4, and the contact identity behind Lemma 2.5;
- impossibility of Lemma 2.4 + 2.5 under the |r + r'| tangency convention, and that P_X is invariant
  under the convention flip r ↦ -r;
- P = ×(XG) = (-1)^{n+1} G ×(X); M P = 0; the Laguerre-radical-centre characterisation; n = 2 formula;
- the equilateral case (b), and the first-order lemma used in case (a).

Checked numerically only:
- agreement with the independent Apollonius route at n = 2, 3, 4 (table above);
- O(ε) convergence to the symmetry centre at the square along random directions.

Guessed / taken from the brief, not verified against the paper's text:
- that the paper's tangency means oriented contact |x - x'| = |r - r'| (forced by its two lemmas, but
  the paper does not write it), and that point spheres and the point at infinity count as "cycles";
- that Remark 3.2's (p_2..p_{n+1}, p_{n+2}) uses 1-based slots of Def 2.3 (the only reading in
  which it is the homogeneous centre of P).
