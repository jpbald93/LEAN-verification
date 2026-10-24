#!/usr/bin/env python3
"""Paper D — the explicit examples quoted in the text (60-digit arithmetic, deterministic)."""
from mpmath import mp, mpf, mpc, sqrt, exp, pi, fabs, conj
mp.dps = 60
W = exp(1j * pi / 3)
def col(a, b, c): return ((b - a) * conj(c - a)).imag
def cc(a, b, c):
    d = 2 * (a.real * (b.imag - c.imag) + b.real * (c.imag - a.imag) + c.real * (a.imag - b.imag))
    ux = (abs(a)**2 * (b.imag - c.imag) + abs(b)**2 * (c.imag - a.imag) + abs(c)**2 * (a.imag - b.imag)) / d
    uy = (abs(a)**2 * (c.real - b.real) + abs(b)**2 * (a.real - c.real) + abs(c)**2 * (b.real - a.real)) / d
    return mpc(ux, uy)
def meet(P1, Q1, P2, Q2):
    d1 = Q1 - P1; d2 = Q2 - P2; return P1 + (conj(P2 - P1) * d2).imag / (conj(d1) * d2).imag * d1
def lester_pts(A, B, C):
    ccw = (conj(B - A) * (C - A)).imag > 0   # Lean's Ccw: Im(conj(B-A)(C-A)) > 0
    def apex(P, Q, R, out):
        rot = (conj(W) if ccw else W) if out else (W if ccw else conj(W)); return Q + (R - Q) * rot
    F1 = meet(A, apex(A, B, C, True), B, apex(B, C, A, True))
    F2 = meet(A, apex(A, B, C, False), B, apex(B, C, A, False))
    O = cc(A, B, C); N = (O + (A + B + C - 2 * O)) / 2
    return dict(O=O, N=N, F1=F1, F2=F2)
print("== Lester, isosceles A=(0,h), B=(-1,0), C=(1,0)")
for h in ['0.3', '0.5', '1', '2.5']:
    p = lester_pts(mpc(0, mpf(h)), mpc(-1, 0), mpc(1, 0)); v = list(p.values())
    sep = min(abs(a - b) for i, a in enumerate(v) for b in v[i + 1:])
    print(f" h={h}: max |x| = {mp.nstr(max(fabs(z.real) for z in v), 3)}, min separation = {mp.nstr(sep, 3)}")
print("== Lester, 120-degree isosceles A=(0,1/sqrt3)")
A = mpc(0, 1 / sqrt(3)); p = lester_pts(A, mpc(-1, 0), mpc(1, 0))
print(f" |N-A| = {mp.nstr(abs(p['N'] - A), 3)}, |F1-A| = {mp.nstr(abs(p['F1'] - A), 3)}, |F2-O| = {mp.nstr(abs(p['F2'] - p['O']), 3)}")
print("== Kosnita boundary example O=0, A=(1,0), B,C=(1/2,±sqrt3/2)")
O = mpc(0); A = mpc(1, 0); B = mpc(mpf(1) / 2, sqrt(3) / 2); C = mpc(mpf(1) / 2, -sqrt(3) / 2)
Oa, Ob, Oc = cc(O, B, C), cc(O, C, A), cc(O, A, B)
S = abs(A - B)**2 + abs(B - C)**2 + abs(C - A)**2
print(f" sides = {mp.nstr(abs(A-B),5)}, {mp.nstr(abs(B-C),5)}, {mp.nstr(abs(C-A),5)};  sum of squares - 5R^2 = {mp.nstr(S - 5, 3)}")
print(f" |Oa - A| = {mp.nstr(abs(Oa - A), 3)};  Ob = {mp.nstr(Ob, 6)}, Oc = {mp.nstr(Oc, 6)} (both x = 1/2: B Ob and C Oc are the line x = 1/2)")
print(f" non-collinear OBC, OCA, OAB: {mp.nstr(col(O,B,C),4)}, {mp.nstr(col(O,C,A),4)}, {mp.nstr(col(O,A,B),4)}")
