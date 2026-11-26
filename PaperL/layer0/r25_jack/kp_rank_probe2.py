import numpy as np
from scipy.optimize import minimize

def KP(x, y, n):
    m = n//2
    return np.array([[((-x[k])**j * y[k]**(n-m-j)) if j <= m
                      else -((-x[k])**(j-(m+1)) * y[k]**(n-m-1-(j-(m+1))))
                      for j in range(n+1)] for k in range(n)], dtype=complex)

def crossVec(A):
    return np.array([(-1)**j*np.linalg.det(np.delete(A,j,axis=1)) for j in range(A.shape[1])], dtype=complex)

def unpack(p):
    h=len(p)//2; return p[:h]+1j*p[h:]

def f(p):
    c=unpack(p); A=KP(c,np.conj(c),len(c)); v=crossVec(A)
    return float(np.sum(np.abs(v)**2))

def margins(c):
    n=len(c); mt=1e9
    for i in range(n):
        mt=min(mt,abs(c[i]))
        for j in range(i+1,n):
            mt=min(mt,abs(np.conj(c[i])*c[j]-c[i]*np.conj(c[j])))
            mt=min(mt,abs(c[i]-c[j]))
    return mt

n=6
rng=np.random.default_rng(11)
hits=[]
best=None
for trial in range(120):
    p0=rng.normal(size=2*n)*1.2
    r=minimize(f,p0,method='BFGS',options={'maxiter':6000,'gtol':1e-13})
    p=r.x; c=unpack(p); A=KP(c,np.conj(c),n)
    s=np.linalg.svd(A,compute_uv=False); rat=s[-1]/s[0]
    mg=margins(c)
    rec=(f(p),rat,mg,c.copy())
    if best is None or rec[0]<best[0]: best=rec
    if f(p)<1e-16:
        hits.append(rec)
        print("trial",trial,"f=%.2e"%f(p),"smin/smax=%.1e"%rat,"minmargin=%.2e"%mg)
        print("  c=",np.round(c,4))
print("---- hits:",len(hits),"of",trial+1)
if not hits:
    print("best f=%.3e"%best[0],"ratio=%.2e"%best[1],"margin=%.2e"%best[2]); print("c=",np.round(best[3],4))
