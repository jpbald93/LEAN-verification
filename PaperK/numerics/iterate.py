"""Probe: does the concurrency point survive the Apollonius completion (iteration)?
Prop 3.1 gives P_X from the pairs (A_i, A_i'). Thm 3.4 builds B_i in Ap(A minus A_i) (the
solution that is not X_i). Extension candidate: P of the derived configuration equals P_X.
"""
import numpy as np
from apollonius import ap_spheres, point_from_lines, concurrence_residual, random_config

def solve_pair(C, R, i, tol=1e-9):
    idx=[j for j in range(len(R)) if j!=i]
    sols, disc = ap_spheres(C[idx], R[idx])
    return sols, disc

def match(sol, C, R, idx, tol=1e-8):
    for j in idx:
        if abs(sol[1]-R[j])<1e-7 and np.linalg.norm(sol[0]-C[j])<1e-7:
            return j
    return None

def px_of(C, R):
    m=len(R); n=C.shape[1]
    plus=[]; minus=[]; pairs=[]
    for i in range(m):
        sols,disc = solve_pair(C,R,i)
        if len(sols)!=2: return None, "disc/tangent-config fail"
        plus.append(sols[0][0]); minus.append(sols[1][0]); pairs.append(sols)
    P,M = point_from_lines(plus,minus)
    if P is None: return None, "P at infinity"
    return P, pairs

def step(C,R):
    """One two-step: return B, B' (arrays) using Thm 3.4."""
    m=len(R); n=C.shape[1]
    sols_all=[solve_pair(C,R,i)[0] for i in range(m)]
    A =np.array([s[0][0] for s in sols_all]); RA=np.array([s[0][1] for s in sols_all])
    Ap=np.array([s[1][0] for s in sols_all]); RAp=np.array([s[1][1] for s in sols_all])
    def derive(S, SR):
        B=[]; BR=[]
        for i in range(m):
            idx=[j for j in range(m) if j!=i]
            sols,_=ap_spheres(S[idx],SR[idx])
            if len(sols)!=2: return None,None
            k=match(sols[0],C,R,range(m)) or match(sols[1],C,R,range(m))
            if k is None: return None,None
            other = sols[1] if match(sols[0],C,R,range(m)) is not None else sols[0]
            B.append(other[0]); BR.append(other[1])
        return np.array(B), np.array(BR)
    B,BR   = derive(A,RA)
    Bp,BRp = derive(Ap,RAp)
    return B,BR,Bp,BRp

rng=np.random.default_rng(7)
n=2; m=n+2
found=0
for t in range(200):
    C,R=random_config(n,m,rng)
    P,pairs = px_of(C,R)
    if P is None: continue
    st = step(C,R)
    if st[0] is None or st[2] is None: continue
    B,BR,Bp,BRp = st
    # Thm 3.4 check: lines (B_i,B_i') through P
    r34 = concurrence_residual(P, B, Bp)
    # Extension check: P of the derived configuration {B_i}
    P2,_ = px_of(B,BR)
    if P2 is None: continue
    dP = np.linalg.norm(P2-P)
    print(f"trial {t}: P={np.round(P,4)}  |P(B)-P|={dP:.3e}  Thm3.4 residual={r34:.2e}")
    found+=1
    if found>=6: break
print("done", found)
