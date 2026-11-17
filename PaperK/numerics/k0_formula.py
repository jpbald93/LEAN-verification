"""K0: derive P_X symbolically at n=2.

Key observation: for the triple T_i, the two Apollonius circles are x0_i + r*w_i for the two
roots r of a quadratic, so the LINE through their centres is exactly the affine line
      L_i = { x0_i + r * w_i : r in R },
with x0_i and w_i RATIONAL in the data (no radicals at all). Concurrency of the four lines is
then a rank condition on 4 affine line equations, i.e. four 3x3 minors vanish.
"""
import sympy as sp

def line_of_triple(data, idx):
    """data: list of ((ax,ay), rad). Returns (x0 (2-vector), w (2-vector))."""
    (cj, rj) = data[idx[0]]
    rows, rhs = [], []
    for p in idx[1:]:
        (cp, rp) = data[p]
        d = sp.Matrix([cp[0]-cj[0], cp[1]-cj[1]])
        alpha = (cj[0]**2 + cj[1]**2 - cp[0]**2 - cp[1]**2 + rp**2 - rj**2)/2
        beta = rp - rj
        rows.append(d.T); rhs.append(sp.Matrix([alpha]) - beta*sp.Matrix([1]))
    A = sp.Matrix.vstack(*rows)          # 2x2
    b = sp.Matrix([rhs[0][0], rhs[1][0]])
    x0 = A.LUsolve(sp.Matrix([b[0], b[1]]))
    w  = A.LUsolve(sp.Matrix([-beta, -beta]))
    return sp.simplify(x0), sp.simplify(w)

def run(nsym=4):
    a = sp.symbols('a1:5'); b = sp.symbols('b1:5'); r = sp.symbols('r1:5')
    data = [((a[i], b[i]), r[i]) for i in range(4)]
    rows = []
    for i in range(4):
        idx = [j for j in range(4) if j != i]
        x0, w = line_of_triple(data, idx)
        n = sp.Matrix([-w[1], w[0]])            # normal to the line
        rows.append((n[0], n[1], -(n[0]*x0[0] + n[1]*x0[1])))
    M = sp.Matrix(rows)
    minors = []
    for rows3 in sp.utilities.subsets(range(4), 3) if hasattr(sp.utilities,'subsets') else [(0,1,2),(0,1,3),(0,2,3),(1,2,3)]:
        sub = M[list(rows3), :]
        minors.append(sp.factor(sp.cancel(sub.det())))
    return minors, M

if __name__ == "__main__":
    minors, M = run()
    for k, m in enumerate(minors):
        print(f"minor {k}:", m)
