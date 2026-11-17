"""Numeric probe for Płatek arXiv:2604.03067 (Prop 3.1) in dimension n.

Oriented sphere: (centre x in R^n, signed radius r). Tangency to another sphere:
|x_i - x_j|^2 = (r_i + r_j)^2  (signed radii: negative for enclosing).
Oriented hyperplane: unit normal u, offset d; tangency: <u, x> - d = -r  (one convention,
    checked against the sphere-sphere formula in the limit of a large sphere).

Ap(S) for a set S of n+1 given objects = the (generically two) objects tangent to all of S.
For spheres only this is: n linear equations after subtracting the first, then a quadratic in r.
"""
import numpy as np
from itertools import combinations

def ap_spheres(C, R):
    """C: (m,n) centres, R: (m,) signed radii, m = n+1. Returns list of (x, r) solutions."""
    C = np.asarray(C, float); R = np.asarray(R, float)
    m, n = C.shape
    d = C[1:] - C[0]                    # (n, n) after subtracting the first
    delta = R[1:] - R[0]
    # -2 d.x - 2 delta r = (R_i^2 - R_0^2) - (|C_i|^2 - |C_0|^2)
    rhs = (R[1:]**2 - R[0]**2) - ((C[1:]**2).sum(1) - (C[0]**2).sum())
    # unknowns: x (n), then r free -> x = x0 + w * r
    # solve  -2 d . x - 2 delta r = rhs  ->  d . x = -(rhs/2) - delta r
    A = d
    b0 = -rhs/2.0
    x0 = np.linalg.solve(A, b0)
    w = np.linalg.solve(A, -delta)
    # substitute into |x - C0|^2 = (r + R0)^2
    # |x0 + w r - C0|^2 - (r+R0)^2 = 0
    p = x0 - C[0]
    a = (w @ w) - 1.0
    b = 2*(p @ w) - 2*R[0]
    c = (p @ p) - R[0]**2
    if abs(a) < 1e-12:
        roots = [-c/b] if abs(b) > 1e-12 else []
    else:
        disc = b*b - 4*a*c
        if disc < -1e-9:
            return [], disc
        disc = max(disc, 0.0)
        roots = [(-b + np.sqrt(disc))/(2*a), (-b - np.sqrt(disc))/(2*a)]
    sols = []
    for r in roots:
        sols.append((x0 + w*r, r))
    return sols, disc

def point_from_lines(P0s, P1s):
    """Least-squares intersection of lines through (P0s[i], P1s[i]) in R^n."""
    P0s = np.asarray(P0s, float); P1s = np.asarray(P1s, float)
    n = P0s.shape[1]
    M = np.zeros((n, n)); y = np.zeros(n)
    for p0, p1 in zip(P0s, P1s):
        v = p1 - p0
        nv = v @ v
        if nv < 1e-14:
            continue
        proj = np.eye(n) - np.outer(v, v)/nv      # plane perpendicular to the line
        M += proj
        y += proj @ p0
    if abs(np.linalg.det(M)) < 1e-10:
        return None, None
    P = np.linalg.solve(M, y)
    return P, M

def concurrence_residual(P, P0s, P1s):
    res = 0.0
    for p0, p1 in zip(P0s, P1s):
        v = p1 - p0; nv = v @ v
        if nv < 1e-14: continue
        w = P - p0
        perp = w - (w @ v)/nv * v
        res = max(res, np.linalg.norm(perp))
    return res

def random_config(n, m, rng, lo=0.3, hi=2.0, spread=3.0, signed=False):
    C = rng.uniform(-spread, spread, size=(m, n))
    R = rng.uniform(lo, hi, size=m)
    if signed:
        R = R * rng.choice([-1, 1], size=m)
    return C, R

def prop31(n, trials=5, seed=0, verbose=True):
    rng = np.random.default_rng(seed)
    out = []
    for t in range(trials):
        C, R = random_config(n, n+2, rng)
        centres_plus, centres_minus = [], []
        ok = True
        for i in range(n+2):
            idx = [j for j in range(n+2) if j != i]
            sols, disc = ap_spheres(C[idx], R[idx])
            if len(sols) != 2:
                ok = False; out.append(("degenerate", disc)); break
            centres_plus.append(sols[0][0]); centres_minus.append(sols[1][0])
        if not ok: continue
        P, M = point_from_lines(centres_plus, centres_minus)
        if P is None:
            out.append(("parallel-lines", None)); continue
        res = concurrence_residual(P, centres_plus, centres_minus)
        scale = max(1.0, np.linalg.norm(C, axis=1).max())
        out.append(("residual", res/scale))
        if verbose:
            print(f"n={n} trial {t}: max line-distance (relative) = {res/scale:.3e}")
    return out

if __name__ == "__main__":
    for n in (2, 3, 4):
        print("="*60, "\nPROP 3.1 numeric check in R^%d (spheres only)" % n)
        prop31(n, trials=6, seed=100+n)
