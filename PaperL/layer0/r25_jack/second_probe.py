import numpy as np
def KP(x,y,n):
    m=n//2
    return np.array([[((-x[k])**j*y[k]**(n-m-j)) if j<=m else -((-x[k])**(j-(m+1))*y[k]**(n-m-1-(j-(m+1)))) for j in range(n+1)] for k in range(n)],dtype=complex)
def cv(A):
    return np.array([(-1)**j*np.linalg.det(np.delete(A,j,axis=1)) for j in range(A.shape[1])],dtype=complex)
def second(c,d): return (np.conj(c)*d-c*np.conj(d))/(np.conj(c)-np.conj(d))

c=np.array([-0.47794+0.78869j,-0.07321+0.07902j,0.55747-1.46988j,0.86761-0.36281j,-0.5299-0.05008j,-1.11315+0.13217j])
V=cv(KP(c,np.conj(c),6)); print("|V|max=%.2e"%np.abs(V).max())
print("V=",np.round(V,8))
# coaxal check: do all pairs share the same second intersection?
S=np.array([[second(c[i],c[j]) for j in range(6)] for i in range(6)])
print("pairwise second points:")
print(np.round(S,6))
# validation of pipeline: conj(V[3]) == V[0] (conj_crossVec_even, n=6, m=2)
print("conj(V[3])-V[0] =",np.conj(V[3])-V[0])
