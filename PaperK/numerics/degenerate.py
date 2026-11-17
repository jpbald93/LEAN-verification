"""Degenerate locus: three equal circles in equilateral position + one perturbed circle.
The subset without the 4th is symmetric, so its two Apollonius cycles are concentric -> that
pair-line is undefined. Question: do the remaining three lines still meet, and does the meeting
point move continuously as the 4th circle approaches the symmetric position?"""
import numpy as np
from apollonius import ap_spheres, point_from_lines, concurrence_residual

def pairs(C,R):
    out=[]
    for i in range(len(R)):
        idx=[j for j in range(len(R)) if j!=i]
        s,_=ap_spheres(C[idx],R[idx])
        out.append(s if len(s)==2 else None)
    return out

def analyse(C,R,label):
    ps=pairs(C,R)
    ok=[p for p in ps if p is not None]
    conc=[]
    for p in ok:
        if np.linalg.norm(p[1][0]-p[0][0])<1e-9:
            conc.append(True)
        else:
            conc.append(False)
    good=[p for p,c in zip(ok,conc) if not c]
    if len(good)<2: return None
    P0=[p[0][0] for p in good]; P1=[p[1][0] for p in good]
    P,M=point_from_lines(P0,P1)
    if P is None:
        print(f"{label}: {len(ps)} pairs, {sum(conc)} concentric, remaining lines parallel/at infinity")
        return None
    res=concurrence_residual(P,P0,P1)
    print(f"{label}: pairs={len(ps)} concentric={sum(conc)}  P={np.round(P,6)}  residual={res:.2e}")
    return P

# equilateral triple of unit circles
eq=np.array([[0,0],[2,0],[1,np.sqrt(3)]],float)
for eps in [0.0, 1e-6, 1e-3, 0.1, 0.5]:
    C=np.vstack([eq,[1.0+eps, 0.4]]); R=np.array([1.,1.,1.,0.35])
    analyse(C,R,f"eps={eps:>7}: 4th circle at (1+eps,0.4) r=0.35")

print()
# n=3: regular tetrahedron of four unit spheres + a fifth
tet=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)
for eps in [0.0, 1e-3, 0.2]:
    C=np.vstack([tet,[0.1+eps,0.1,0.1]]); R=np.array([1.,1.,1.,1.,0.5])
    analyse(C,R,f"n=3 eps={eps:>6}")
