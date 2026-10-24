#!/usr/bin/env python3
"""Paper D — reproducible numerical re-check of the main theorems (independent of the Lean code).

Each check builds random configurations satisfying the hypotheses of the Lean statement, evaluates the
conclusion at high precision, and runs a NEGATIVE CONTROL (a deliberately false variant) on the same
configurations. Fixed seeds; run:  python3 paperd_numerics.py  (needs mpmath). Output is JSON lines.

The coordinate formulas here are written from the mathematics (not copied from the Lean sources).
"""
import json, random, sys, time
from mpmath import mp, mpf, mpc, sqrt, fabs, exp, pi, conj as mconj

mp.dps = 60
SEED = 20261014
OUT = []

def rec(**k):
    OUT.append(k); print(json.dumps(k), flush=True)

def C(rng, s=3):
    return mpc(rng.uniform(-s, s), rng.uniform(-s, s))

def cj(z): return mconj(z)

def col(a, b, c):  # signed collinearity determinant Im((b-a) conj(c-a))
    return ((b - a) * cj(c - a)).imag

def circ_centre(a, b, c):
    d = 2 * (a.real * (b.imag - c.imag) + b.real * (c.imag - a.imag) + c.real * (a.imag - b.imag))
    ux = (abs(a)**2 * (b.imag - c.imag) + abs(b)**2 * (c.imag - a.imag) + abs(c)**2 * (a.imag - b.imag)) / d
    uy = (abs(a)**2 * (c.real - b.real) + abs(b)**2 * (a.real - c.real) + abs(c)**2 * (b.real - a.real)) / d
    return mpc(ux, uy)

def concyc_res(pts):
    """max deviation of points from the circle through the first three (scale-free), or line residual"""
    o = circ_centre(pts[0], pts[1], pts[2]); r = abs(pts[0] - o)
    return max(fabs(abs(p - o) - r) for p in pts[3:]) / max(r, mpf(1))

def circle_or_line_res(pts):
    lin = max(fabs(col(pts[0], pts[1], p)) for p in pts[2:]) / max(abs(pts[1] - pts[0])**2, mpf('1e-30'))
    if lin < mpf('1e-40'):
        return lin
    return concyc_res(pts)

def mindist(pts):
    return min(abs(p - q) for i, p in enumerate(pts) for q in pts[i + 1:])

def summarize(name, n, worst, ctrl_viol, ctrl_n, extra=None):
    d = dict(check=name, configs=n, worst_residual=mp.nstr(worst, 3), control_violated=ctrl_viol,
             control_trials=ctrl_n)
    if extra: d.update(extra)
    rec(**d)

# ---------------------------------------------------------------- Clifford (circles through M = 0)
def second(ci, cj_):  # second intersection of |z-ci|=|ci|, |z-cj|=|cj|
    return (cj(ci) * cj_ - ci * cj(cj_)) / (cj(ci) - cj(cj_))

def circ3(a, b, c):  # (centre, radius)
    o = circ_centre(a, b, c); return o, abs(a - o)

def miquel_point(cs):
    """common point of the four circles Gamma_ijk of four circles (classical Clifford point), found as the
    second intersection of Gamma_123 and Gamma_124 (they share P_12)."""
    c1, c2, c3, c4 = cs
    P12 = second(c1, c2)
    o1, _ = circ3(P12, second(c1, c3), second(c2, c3))
    o2, _ = circ3(P12, second(c1, c4), second(c2, c4))
    # reflect P12 in the line of centres o1 o2
    d = o2 - o1
    return o1 + d * cj((P12 - o1) / d)

def on_circle_res(z, o, r): return fabs(abs(z - o) - r) / max(r, mpf(1))

def genpos_ok(cs, tol=mpf('1e-3')):
    n = len(cs)
    for i in range(n):
        for j in range(i + 1, n):
            if fabs((cj(cs[i]) * cs[j]).imag) < tol: return False
            if abs(second(cs[i], cs[j])) < tol: return False
            for k in range(j + 1, n):
                if fabs(col(second(cs[i], cs[j]), second(cs[i], cs[k]), second(cs[j], cs[k]))) < tol: return False
                if fabs(col(cs[i], cs[j], cs[k])) < tol: return False
    return True

def clifford4(rng, N):
    worst = mpf(0); viol = 0; n = 0
    while n < N:
        cs = [C(rng) for _ in range(4)]
        if not genpos_ok(cs): continue
        p = miquel_point(cs); n += 1
        for (i, j, k) in [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]:
            o, r = circ3(second(cs[i], cs[j]), second(cs[i], cs[k]), second(cs[j], cs[k]))
            worst = max(worst, on_circle_res(p, o, r))
        # control: the point P_12 (on two of the circles, generally not on Gamma_234)
        o, r = circ3(second(cs[1], cs[2]), second(cs[1], cs[3]), second(cs[2], cs[3]))
        if on_circle_res(second(cs[0], cs[1]), o, r) > mpf('1e-20'): viol += 1
    summarize('clifford_n4 (four Gamma circles concurrent)', N, worst, viol, N)

def clifford5(rng, N):
    worst = mpf(0); viol = 0; n = 0; mins = []
    while n < N:
        cs = [C(rng) for _ in range(5)]
        if not genpos_ok(cs): continue
        pts = [miquel_point([cs[j] for j in range(5) if j != i]) for i in range(5)]
        if mindist(pts) < mpf('1e-3'): continue
        n += 1; mins.append(mindist(pts))
        worst = max(worst, circle_or_line_res(pts))
        # control: replace one point by P_12
        bad = pts[:4] + [second(cs[0], cs[1])]
        if circle_or_line_res(bad) > mpf('1e-20'): viol += 1
    summarize('clifford_n5 (five Clifford points concyclic or collinear)', N, worst, viol, N,
              dict(min_point_separation=mp.nstr(min(mins), 3)))

def clifford6(rng, N):
    worst = mpf(0); viol = 0; n = 0
    while n < N:
        cs = [C(rng) for _ in range(6)]
        if not genpos_ok(cs): continue
        circles = []
        ok = True
        for omit in range(6):
            S = [cs[j] for j in range(6) if j != omit]
            pts = [miquel_point([S[j] for j in range(5) if j != i]) for i in range(5)]
            if mindist(pts) < mpf('1e-3') or fabs(col(pts[0], pts[1], pts[2])) < mpf('1e-3'): ok = False; break
            o, r = circ3(pts[0], pts[1], pts[2])
            worst = max(worst, max(on_circle_res(p, o, r) for p in pts[3:]))
            circles.append((o, r))
        if not ok: continue
        n += 1
        # common point of the six circles: second intersection of circles 0 and 1, check on all
        (o1, r1), (o2, r2) = circles[0], circles[1]
        d = abs(o2 - o1); a = (r1**2 - r2**2 + d**2) / (2 * d); h = sqrt(max(r1**2 - a**2, mpf(0)))
        u = (o2 - o1) / d; cands = [o1 + a * u + h * u * 1j, o1 + a * u - h * u * 1j]
        best = min(cands, key=lambda q: max(on_circle_res(q, o, r) for o, r in circles))
        worst = max(worst, max(on_circle_res(best, o, r) for o, r in circles))
        # control: the other intersection point of circles 0 and 1 is not on all six
        other = cands[1] if best is cands[0] else cands[0]
        if max(on_circle_res(other, o, r) for o, r in circles) > mpf('1e-20'): viol += 1
    summarize('clifford_n6 (six five-point circles, each through its 5 points, concurrent)', N, worst, viol, N)

# ---------------------------------------------------------------- Lester
W = exp(1j * pi / 3)

def lester(rng, N):
    worst = mpf(0); viol = 0; n = 0
    while n < N:
        A, B, Cc = C(rng), C(rng), C(rng)
        s = [abs(A - B), abs(B - Cc), abs(Cc - A)]
        if min(fabs(s[0] - s[1]), fabs(s[1] - s[2]), fabs(s[0] - s[2])) < mpf('1e-2') or fabs(col(A, B, Cc)) < mpf('1e-2'):
            continue
        ccw = (cj(B - A) * (Cc - A)).imag > 0   # Lean's Ccw: Im(conj(B-A)(C-A)) > 0
        def apex(P, Q, R, out):  # apex on side QR, opposite P
            rot = (cj(W) if ccw else W) if out else (W if ccw else cj(W))
            return Q + (R - Q) * rot
        def meet(P1, Q1, P2, Q2):
            d1 = Q1 - P1; d2 = Q2 - P2; den = (cj(d1) * d2).imag
            t = (cj(P2 - P1) * d2).imag / den; return P1 + t * d1
        F1 = meet(A, apex(A, B, Cc, True), B, apex(B, Cc, A, True))
        F2 = meet(A, apex(A, B, Cc, False), B, apex(B, Cc, A, False))
        O = circ_centre(A, B, Cc); H = A + B + Cc - 2 * O; Nn = (O + H) / 2
        n += 1
        worst = max(worst, concyc_res([O, Nn, F1, F2]))
        G = (A + B + Cc) / 3
        if concyc_res([O, G, F1, F2]) > mpf('1e-20'): viol += 1  # control: centroid for nine-point centre
    summarize('lester (O, N, F1, F2 concyclic, scalene)', N, worst, viol, N)

# ---------------------------------------------------------------- Kosnita
def kosnita(rng, N):
    worst = mpf(0); viol = 0; n = 0
    while n < N:
        O = mpc(0, 0); R = mpf(1)
        A, B, Cc = [exp(1j * mpf(rng.uniform(0, 6.283))) for _ in range(3)]
        if fabs(col(A, B, Cc)) < mpf('1e-2') or min(fabs(col(O, B, Cc)), fabs(col(O, Cc, A)), fabs(col(O, A, B))) < mpf('1e-2'):
            continue
        S = abs(A - B)**2 + abs(B - Cc)**2 + abs(Cc - A)**2
        if fabs(S - 5 * R**2) < mpf('1e-2'): continue
        Oa, Ob, Oc = circ_centre(O, B, Cc), circ_centre(O, Cc, A), circ_centre(O, A, B)
        def meet(P1, Q1, P2, Q2):
            d1 = Q1 - P1; d2 = Q2 - P2; den = (cj(d1) * d2).imag
            t = (cj(P2 - P1) * d2).imag / den; return P1 + t * d1
        P = meet(A, Oa, B, Ob); n += 1
        worst = max(worst, fabs(col(Cc, Oc, P)) / abs(Oc - Cc))
        # control: replace O_c by O_a (the circumcentre of the wrong triangle OBC)
        bad = Oa
        if fabs(col(Cc, bad, P)) / abs(bad - Cc) > mpf('1e-20'): viol += 1
    summarize('kosnita (A Oa, B Ob, C Oc concurrent)', N, worst, viol, N)

# ---------------------------------------------------------------- Blundon
def blundon(rng, N):
    worst_margin = None; viol = 0; n = 0
    while n < N:
        A, B, Cc = C(rng), C(rng), C(rng)
        if fabs(col(A, B, Cc)) < mpf('1e-2'): continue
        a, b, c = abs(B - Cc), abs(Cc - A), abs(A - B); s = (a + b + c) / 2
        area = fabs(col(A, B, Cc)) / 2; R = a * b * c / (4 * area); r = area / s
        root = sqrt(R**2 - 2 * R * r)
        lo = 2 * R**2 + 10 * R * r - r**2 - 2 * (R - 2 * r) * root
        hi = 2 * R**2 + 10 * R * r - r**2 + 2 * (R - 2 * r) * root
        n += 1
        m = min(s**2 - lo, hi - s**2) / s**2
        worst_margin = m if worst_margin is None else min(worst_margin, m)
        # control: the false sharper upper bound 2R^2+10Rr-r^2 (no root term): violated when s^2 exceeds it
        if s**2 > 2 * R**2 + 10 * R * r - r**2: viol += 1
    rec(check='blundon (lo <= s^2 <= hi)', configs=N, min_relative_margin=mp.nstr(worst_margin, 3),
        note='margin >= 0 means both inequalities hold', control='upper bound without the root term',
        control_violated=viol, control_trials=N)

# ---------------------------------------------------------------- Steiner–Lehmus
def steiner_lehmus(rng, N):
    """Search triangles with equal internal bisectors: param apex angle split; check AB = AC.
    For random triangles BE != CF, so we solve for C on a curve: fix A,B, vary C along a ray and root-find
    BE - CF = 0 (bisection), then check AB = AC."""
    from mpmath import findroot
    worst = mpf(0); n = 0; tried = 0
    def feet(A, B, Cc):
        a, b, c = abs(B - Cc), abs(Cc - A), abs(A - B)
        E = A + (Cc - A) * (c / (a + c))      # bisector from B meets AC: AE/EC = AB/BC
        F = A + (B - A) * (b / (a + b))       # bisector from C meets AB: AF/FB = AC/BC
        return E, F
    while n < N and tried < 50 * N:
        tried += 1
        A = mpc(0, 0); B = mpc(1, 0); th = mpf(rng.uniform(0.3, 2.8))
        def g(t):
            Cc = t * exp(1j * th); E, F = feet(A, B, Cc); return abs(B - E) - abs(Cc - F)
        try:
            t0 = findroot(g, mpf(rng.uniform(0.3, 3)))
        except Exception:
            continue
        if not (t0 > mpf('0.05')): continue
        Cc = t0 * exp(1j * th); n += 1
        worst = max(worst, fabs(abs(A - B) - abs(A - Cc)))
    rec(check='steiner_lehmus (equal bisectors => AB = AC)', configs=n,
        worst_residual=mp.nstr(worst, 3), note='each configuration found by root-finding BE = CF')

# ---------------------------------------------------------------- five circles (Miquel pentagram)
def fivecircles(rng, N):
    worst = mpf(0); viol = 0; n = 0
    def meet(P1, Q1, P2, Q2):
        d1 = Q1 - P1; d2 = Q2 - P2; den = (cj(d1) * d2).imag
        t = (cj(P2 - P1) * d2).imag / den; return P1 + t * d1
    while n < N:
        # convex pentagon: random radii/angles around origin
        angs = sorted(rng.uniform(0, 6.283) for _ in range(5))
        if min((angs[(i + 1) % 5] - angs[i]) % 6.283 for i in range(5)) < 0.5: continue
        A = [mpf(rng.uniform(0.8, 1.2)) * exp(1j * mpf(t)) for t in angs]
        # T_i: intersection of lines A_{i-2}A_{i-1} and A_i A_{i+1}  (outer point on side A_{i-1}A_i)
        T = [meet(A[(i - 2) % 5], A[(i - 1) % 5], A[i], A[(i + 1) % 5]) for i in range(5)]
        circles = [circ3(A[(i - 1) % 5], A[i], T[i]) for i in range(5)]
        M = []
        for i in range(5):  # M_i: second intersection of circles i and i+1, other than A_i
            (o1, r1), (o2, r2) = circles[i], circles[(i + 1) % 5]
            d = o2 - o1; M.append(o1 + d * cj((A[i] - o1) / d))
        allp = A + T + M
        if mindist(allp) < mpf('1e-2'): continue
        n += 1
        worst = max(worst, circle_or_line_res(M))
        bad = M[:4] + [A[0]]
        if circle_or_line_res(bad) > mpf('1e-20'): viol += 1
    summarize('fivecircles (M_0..M_4 concyclic or collinear)', N, worst, viol, N)

# ---------------------------------------------------------------- Sawayama–Thébault
def thebault(rng, N):
    worst = mpf(0); viol = 0; n = 0
    from mpmath import findroot
    def dist_line(P, Q1, Q2): return fabs(col(Q1, Q2, P)) / abs(Q2 - Q1)
    def side(P, Q1, Q2): return col(Q1, Q2, P)
    tries = 0
    while n < N and tries < 20 * N:
        tries += 1
        A, B, Cc = C(rng), C(rng), C(rng)
        if fabs(col(A, B, Cc)) < mpf('0.5'): continue
        t = mpf(rng.uniform(0.15, 0.85)); D = B + t * (Cc - B)
        O = circ_centre(A, B, Cc); R = abs(A - O)
        a, b, c = abs(B - Cc), abs(Cc - A), abs(A - B); I = (a * A + b * B + c * Cc) / (a + b + c)
        def solve(X):
            # unknown centre P (2 real) and r: dist to AD = r, dist to BC = r, |P-O| = R - r, sides fixed
            sAD = 1 if side(X, A, D) > 0 else -1; sBC = 1 if side(A, B, Cc) > 0 else -1
            def F(x, y, r):
                P = mpc(x, y)
                return [sAD * side(P, A, D) / abs(D - A) - r, sBC * side(P, B, Cc) / abs(Cc - B) - r, abs(P - O) - (R - r)]
            g0 = (D + X + A) / 3
            sol = findroot(F, (g0.real, g0.imag, mpf('0.1') * R))
            P = mpc(sol[0], sol[1]); r = sol[2]
            ok = r > 0 and sAD * side(P, A, D) > 0 and sBC * side(P, B, Cc) > 0
            return P, ok
        try:
            P, ok1 = solve(B); Q, ok2 = solve(Cc)
        except Exception:
            continue
        if not (ok1 and ok2): continue
        n += 1
        worst = max(worst, fabs(col(P, Q, I)) / abs(Q - P)**2)
        G = (A + B + Cc) / 3
        if fabs(col(P, Q, G)) / abs(Q - P)**2 > mpf('1e-20'): viol += 1
    summarize('sawayama_thebault (P, Q, incentre collinear)', n, worst, viol, n)

if __name__ == '__main__':
    t0 = time.time()
    rec(script='paperd_numerics.py', seed=SEED, mp_dps=mp.dps, python=sys.version.split()[0])
    SCALE = float(__import__('os').environ.get('SCALE', '1'))
    jobs = [('c4', clifford4, 1000), ('c5', clifford5, 500), ('c6', clifford6, 100), ('lester', lester, 1000),
            ('kosnita', kosnita, 1000), ('blundon', blundon, 1000), ('sl', steiner_lehmus, 200),
            ('five', fivecircles, 500), ('thebault', thebault, 300)]
    only = set(sys.argv[1:])
    for k, f, N in jobs:
        if only and k not in only: continue
        f(random.Random(f'{SEED}-{k}'), max(1, int(N * SCALE)))
    rec(done=True, seconds=round(time.time() - t0, 1))
