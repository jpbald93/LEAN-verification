import numpy as np, itertools
c=np.array([-0.47794+0.78869j,-0.07321+0.07902j,0.55747-1.46988j,0.86761-0.36281j,-0.5299-0.05008j,-1.11315+0.13217j])
def det3(a,b,cc,d,e,f,g,h,i): return np.linalg.det(np.array([[a,b,cc],[d,e,f],[g,h,i]],dtype=complex))
def det4(*a): return np.linalg.det(np.array([list(x) for x in np.array(a).reshape(4,4)],dtype=complex))
def triP(x1,x2,x3,y1,y2,y3): return det3(1,x1,y1,1,x2,y2,1,x3,y3)
def cycP(x1,x2,x3,y1,y2,y3): return det3(x1,y1*x1,y1,x2,y2*x2,y2,x3,y3*x3,y3)
ys=np.conj(c)
worst_t=worst_c=1e9
for i,j,k in itertools.combinations(range(6),3):
    t=triP(c[i],c[j],c[k],ys[i],ys[j],ys[k]); y=cycP(c[i],c[j],c[k],ys[i],ys[j],ys[k])
    worst_t=min(worst_t,abs(t)); worst_c=min(worst_c,abs(y))
worst_tr=min(abs(ys[i]*c[j]-c[i]*ys[j]) for i,j in itertools.combinations(range(6),2))
print("min |triP| =",worst_t)
print("min |cycP| =",worst_c)
print("min |transversal| =",worst_tr)
print("min |c| =",np.abs(c).min())
print("min pairwise |c_i-c_j| =",min(abs(c[i]-c[j]) for i,j in itertools.combinations(range(6),2)))
