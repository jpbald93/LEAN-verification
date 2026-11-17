"""Rectangle case: P_X at infinity. Do the common tangent lines of A_i, A_i' share a direction?"""
import numpy as np
from apollonius import ap_spheres

def common_tangents(c1,r1,c2,r2):
    """4 common tangent lines of two oriented circles, as (unit normal u, offset d) with u.x = d.
    Uses the standard formula: line with normal u at signed distance s_i = d - <u,c_i> with |s_i| = |r_i|."""
    c1=np.asarray(c1,float); c2=np.asarray(c2,float)
    dv=c2-c1; L=np.linalg.norm(dv)
    out=[]
    for s in (+1,-1):            # external / internal homothety
        # normal directions at angle theta with sin(theta) = (r1 - s*r2)/L relative to dv
        k=(r1 - s*r2)/L
        if abs(k)>1: continue
        ang=np.arcsin(k)
        base=np.arctan2(dv[1],dv[0])
        for a in (base+ang+np.pi/2, base-ang+np.pi/2):
            u=np.array([np.cos(a),np.sin(a)])
            d=u@c1 + r1*(1 if (u@dv-d)<0 else 1)   # tangent on one side; we take d = u.c1 + r1
            out.append((u, u@c1 + r1))
            out.append((u, u@c1 - r1))
    return out

C=np.array([[-1.,-1],[1,-1],[-1,1],[1,1]]); R=np.ones(4)
sols=[ap_spheres(C[[j for j in range(4) if j!=i]], R[[j for j in range(4) if j!=i]])[0] for i in range(4)]
print("square of four unit circles; per-i solution data:")
for i,s in enumerate(sols):
    if len(s)!=2: print(i,"->",len(s),"solutions"); continue
    (x0,r0),(x1,r1)=s
    print(f" i={i}: A=({np.round(x0,4)}, r={r0:.4f})  A'=({np.round(x1,4)}, r={r1:.4f})")
    print("    centre-line direction:", np.round(x1-x0,4))
