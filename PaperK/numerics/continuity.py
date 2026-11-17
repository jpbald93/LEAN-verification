"""Continuity across the symmetric locus: perturb one of the equilateral circles, follow P."""
import numpy as np
from apollonius import ap_spheres, point_from_lines, concurrence_residual

eq=np.array([[0,0],[2,0],[1,np.sqrt(3)]],float)
target=np.array([1.0, np.sqrt(3)/3])
print("target (symmetry centre) =", np.round(target,8))
for d in [1e-1, 1e-2, 1e-3, 1e-4, 1e-5]:
    C=np.vstack([eq+np.array([0,0]),[1.0,0.4]])
    C[2]=C[2]+np.array([d,0.0])          # break the symmetry
    R=np.array([1.,1.,1.,0.35])
    ps=[]
    for i in range(4):
        idx=[j for j in range(4) if j!=i]
        s,_=ap_spheres(C[idx],R[idx]); ps.append(s if len(s)==2 else None)
    good=[p for p in ps if p is not None and np.linalg.norm(p[1][0]-p[0][0])>1e-12]
    P0=[p[0][0] for p in good]; P1=[p[1][0] for p in good]
    P,M=point_from_lines(P0,P1)
    if P is None:
        print(f"d={d:.0e}: no finite P"); continue
    print(f"d={d:.0e}: |P - centre| = {np.linalg.norm(P-target):.3e}   lines used={len(good)}   residual={concurrence_residual(P,P0,P1):.1e}")
