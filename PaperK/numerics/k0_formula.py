"""K0: explicit formula for P_X (Płatek, arXiv:2604.03067, Prop 3.1 / Remark 3.2).

Coordinates (Def 2.3):  X = (r, c_1..c_n, v, w),   sphere centre x <-> c = v*x, 2wv = r^2 - |c|^2.
Form (pinned by Lemma 2.4, unique up to scale):
    (X|Y) = r r' - c.c' - v w' - w v'        Gram matrix G, G @ G = I.
    (X|X) = r^2 - |c|^2 - 2vw.
P = null vector of the (n+2)x(n+3) matrix M with rows X_i^T G, computed as the generalised cross
product  P_k = (-1)^k det(M with column k removed)  (k = 0..n+2, 0-based).
P_X = (p_2..p_{n+1}) / p_{n+2}   (1-based paper indexing; the c-slots over the v-slot).

The reference (apollonius.py) uses tangency |x_i - x_j| = |r_i + r_j|; the form gives
|x_i - x_j| = |r_i - r_j| (oriented contact). Both produce the same centre-lines, see FORMULA.md.
"""
import numpy as np
from apollonius import ap_spheres, point_from_lines, concurrence_residual, random_config


def gram(n):
    G = np.zeros((n + 3, n + 3))
    G[0, 0] = 1.0
    G[1:n + 1, 1:n + 1] = -np.eye(n)
    G[n + 1, n + 2] = G[n + 2, n + 1] = -1.0
    return G


def cycle(x, r):
    x = np.asarray(x, float)
    return np.concatenate([[r], x, [1.0], [(r * r - x @ x) / 2.0]])


def lie(X, Y):
    n = len(X) - 3
    return X @ gram(n) @ Y


def witness(C, R):
    """Cofactor (generalised cross product) null vector of rows X_i^T G."""
    C = np.asarray(C, float); R = np.asarray(R, float)
    n = C.shape[1]
    M = np.array([cycle(C[i], R[i]) for i in range(n + 2)]) @ gram(n)
    P = np.array([(-1) ** k * np.linalg.det(np.delete(M, k, axis=1)) for k in range(n + 3)])
    return P, M


def px_formula(C, R):
    P, _ = witness(C, R)
    n = np.asarray(C).shape[1]
    return P[1:n + 1] / P[n + 1], P


def px_n2_closed(C, R):
    """n = 2 written out: s_i = a_i^2 + b_i^2 - r_i^2,
    x = -1/2 det[r b s 1] / det[r a b 1],  y = +1/2 det[r a s 1] / det[r a b 1]."""
    a, b = C[:, 0], C[:, 1]; r = np.asarray(R, float); s = a * a + b * b - r * r; one = np.ones(4)
    D = np.linalg.det(np.column_stack([r, a, b, one]))
    x = -0.5 * np.linalg.det(np.column_stack([r, b, s, one])) / D
    y = 0.5 * np.linalg.det(np.column_stack([r, a, s, one])) / D
    return np.array([x, y])


def px_reference(C, R):
    m = len(R); plus = []; minus = []
    for i in range(m):
        idx = [j for j in range(m) if j != i]
        sols, _ = ap_spheres(C[idx], R[idx])
        if len(sols) != 2:
            return None, None, None
        plus.append(sols[0][0]); minus.append(sols[1][0])
    P, M = point_from_lines(plus, minus)
    return P, plus, minus


def compare(n, trials, seed, signed=False, verbose=False):
    rng = np.random.default_rng(seed)
    rels, lin = [], []
    for t in range(trials):
        C, R = random_config(n, n + 2, rng, signed=signed)
        Pref, plus, minus = px_reference(C, R)
        if Pref is None:
            continue
        Pf, P = px_formula(C, R)
        rel = np.linalg.norm(Pf - Pref) / max(1.0, np.linalg.norm(Pref))
        rels.append(rel)
        lin.append(concurrence_residual(Pf, plus, minus) / max(1.0, np.linalg.norm(Pf)))
        if verbose:
            print(f"  n={n} trial {t}: P_formula={np.round(Pf, 6)}  rel |P_f - P_ref| = {rel:.2e}")
    return np.array(rels), np.array(lin)


def check_lemmas(rng, n=2, N=2000):
    """Lemma 2.4 on random cycles; Lemma 2.5 on constructed tangent pairs (oriented contact)."""
    q, t = 0.0, 0.0
    for _ in range(N):
        x = rng.normal(size=n); r = rng.normal()
        X = cycle(x, r)
        q = max(q, abs(lie(X, X)))
        u = rng.normal(size=n); u /= np.linalg.norm(u); r2 = rng.normal()
        # oriented contact: |x - x2| = |r - r2|
        Y = cycle(x + (r - r2) * u, r2)
        t = max(t, abs(lie(X, Y)))
    return q, t


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    q, t = check_lemmas(rng)
    print(f"Lemma 2.4  max |(X|X)| on 2000 random cycles           = {q:.1e}")
    print(f"Lemma 2.5  max |(X|Y)| on 2000 oriented-contact pairs   = {t:.1e}")
    X = cycle([0, 0], 1.0); Y = cycle([2, 0], 1.0)
    print(f"externally tangent unit circles (|x-x'|=r+r'): (X|Y) = {lie(X, Y):.3f}  (= 2 r r')")
    print(f"same pair with r' -> -r':                       (X|Y) = {lie(X, cycle([2, 0], -1.0)):.3f}")

    print("\n== same configurations as apollonius.prop31 (seeds 100+n) ==")
    for n in (2, 3, 4):
        compare(n, 6, 100 + n, verbose=True)

    print("\n== bulk comparison, formula vs apollonius.py + point_from_lines ==")
    for n in (2, 3, 4):
        for signed in (False, True):
            rels, lin = compare(n, 3000, 1000 + n + 10 * signed, signed=signed)
            print(f"n={n} signed={signed!s:5}: defined in {len(rels):4d}/3000   "
                  f"rel diff max={rels.max():.2e} median={np.median(rels):.2e}   "
                  f"max line-dist of P_formula={lin.max():.2e}")

    print("\n== n=2 closed form vs cofactor formula ==")
    rng = np.random.default_rng(5); worst = 0.0
    for _ in range(2000):
        C, R = random_config(2, 4, rng, signed=True)
        a = px_n2_closed(C, R); b = px_formula(C, R)[0]
        worst = max(worst, np.linalg.norm(a - b) / max(1, np.linalg.norm(b)))
    print(f"max rel diff = {worst:.2e}")

    print("\n== degenerate (a): unit circles at the corners of a square / rectangle ==")
    for wdt in (1.0, 2.0):
        C = np.array([[-wdt, -1], [wdt, -1], [-wdt, 1], [wdt, 1]], float); R = np.ones(4)
        P, M = witness(C, R)
        sv = np.linalg.svd(M, compute_uv=False)
        ns = np.linalg.svd(M)[2][-2:]              # basis of the 2-dim null space
        print(f" w={wdt}: singular values of M = {np.round(sv, 4)}  -> rank {np.sum(sv > 1e-9)}")
        print(f"   cofactor vector P = {np.round(P, 12)} (identically zero)")
        for z in ns:
            print(f"   null-space basis vector {np.round(z, 4)}: centre slots c={np.round(z[1:3], 12)}, v={z[3]:.4f},"
                  f" (Z|Z)={lie(z, z):.4f}")
        # apollonius.py reports the concentric pair with radii sqrt(w^2+1)-1, -sqrt(w^2+1)-1 in its
        # |x-x'|=|r+r'| convention; as Lie cycles (oriented contact) the radii are negated.
        A = cycle([0, 0], 1 - np.sqrt(wdt ** 2 + 1)); A2 = cycle([0, 0], 1 + np.sqrt(wdt ** 2 + 1))
        print(f"   kernel contains the concentric Apollonius pair A, A' (Lie radii 1-sqrt(w^2+1), 1+sqrt(w^2+1)): "
              f"{np.round([lie(cycle(C[j], 1), A) for j in range(4)], 12)} "
              f"{np.round([lie(cycle(C[j], 1), A2) for j in range(4)], 12)}")

    print("\n== degenerate (b): equilateral unit triple + 4th circle ==")
    eq = np.array([[0, 0], [2, 0], [1, np.sqrt(3)]], float)
    target = np.array([1.0, np.sqrt(3) / 3])
    for c4, r4 in [((1.0, 0.4), 0.35), ((1.1, 0.4), 0.35), ((-3.0, 2.0), 0.7), ((5.0, 5.0), 2.5)]:
        C = np.vstack([eq, c4]); R = np.array([1, 1, 1, r4], float)
        Pf, P = px_formula(C, R)
        Pn = P / np.linalg.norm(P)
        print(f" 4th=({c4}, r={r4}): P_X={np.round(Pf, 12)}  |P_X-centroid|={np.linalg.norm(Pf - target):.1e}"
              f"  p_(n+2)={P[3]:.4f}  (P|P)/|P|^2={lie(Pn, Pn):.4f}")
    print(" all four radii equal (no centre information at all):")
    for c4 in [(1.0, 0.4), (4.0, -1.0)]:
        C = np.vstack([eq, c4]); R = np.ones(4); P, M = witness(C, R)
        print(f"   4th=({c4}, r=1): P/|P| = {np.round(P / np.linalg.norm(P), 6)}  (c-slots and v-slot all 0)")
    print(" square perturbed by eps (random directions): max |P_X - 0|")
    rng = np.random.default_rng(9); Cs = np.array([[-1., -1], [1, -1], [-1, 1], [1, 1]])
    for eps in (1e-2, 1e-4, 1e-6):
        m = max(np.linalg.norm(px_formula(Cs + eps * rng.normal(size=(4, 2)), 1 + eps * rng.normal(size=4))[0])
                for _ in range(200))
        print(f"   eps={eps:.0e}: {m:.2e}")
    print(" continuity.py perturbation (third circle moved by d):")
    for d in (1e-1, 1e-3, 1e-5):
        C = np.vstack([eq, [1.0, 0.4]]); C[2] += [d, 0]; R = np.array([1, 1, 1, .35])
        Pf, _ = px_formula(C, R)
        print(f"   d={d:.0e}: |P_X - centroid| = {np.linalg.norm(Pf - target):.3e}")
