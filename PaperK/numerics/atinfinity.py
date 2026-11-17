"""Does P_X go to infinity? Scan for near-singular concurrence systems, and probe symmetric cases."""
import numpy as np
from apollonius import ap_spheres, point_from_lines, concurrence_residual

def px(C,R):
    m=len(R); plus=[]; minus=[]
    for i in range(m):
        idx=[j for j in range(m) if j!=i]
        sols,_=ap_spheres(C[idx],R[idx])
        if len(sols)!=2: return None,None
        plus.append(sols[0][0]); minus.append(sols[1][0])
    P,M=point_from_lines(plus,minus)
    return P, (None if M is None else np.linalg.cond(M))

rng=np.random.default_rng(11)
worst=0; worstP=None
for t in range(3000):
    C=rng.uniform(-2,2,size=(4,2)); R=rng.uniform(0.4,1.8,size=4)
    P,c=px(C,R)
    if P is None: continue
    if c>worst: worst, worstP = c, P
print("worst condition number over 3000 random configs:", f"{worst:.3e}", "at P =", np.round(worstP,3))

# symmetric probe: four congruent circles at the corners of a rectangle
for w in [1.0, 2.0, 5.0]:
    C=np.array([[-w,-1],[w,-1],[-w,1],[w,1]],float); R=np.ones(4)
    P,c=px(C,R)
    print(f"rectangle w={w}: P={None if P is None else np.round(P,6)} cond={None if c is None else f'{c:.2e}'}")
