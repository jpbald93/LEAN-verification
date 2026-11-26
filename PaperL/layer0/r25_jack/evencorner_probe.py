import numpy as np
from scipy.optimize import minimize
np.set_printoptions(precision=6, suppress=False)

def KP(x,y,n):
    m=n//2
    return np.array([[((-x[k])**j*y[k]**(n-m-j)) if j<=m else -((-x[k])**(j-(m+1))*y[k]**(n-m-1-(j-(m+1)))) for j in range(n+1)] for k in range(n)],dtype=complex)

def cv(A):
    return np.array([(-1)**j*np.linalg.det(np.delete(A,j,axis=1)) for j in range(A.shape[1])],dtype=complex)

def unpack(p):
    h=len(p)//2; return p[:h]+1j*p[h:]

def f(p):
    c=unpack(p); return float(np.sum(np.abs(cv(KP(c,np.conj(c),len(c))))**2))

def margins(c):
    n=len(c); mt=1e9
    for i in range(n):
        mt=min(mt,abs(c[i]))
        for j in range(i+1,n):
            mt=min(mt,abs(np.conj(c[i])*c[j]-c[i]*np.conj(c[j])),abs(c[i]-c[j]))
    return mt

def collinearity_err(pts):
    # best-fit line, max perpendicular distance
    P=np.array([[z.real,z.imag] for z in pts])
    P0=P-P.mean(0)
    u,s,vt=np.linalg.svd(P0)
    # direction = vt[0]; distances = |P0 . vt[1]|
    d=np.abs(P0@vt[1])
    return d.max(), s

n=6
rng=np.random.default_rng(11)
found=[]
for trial in range(120):
    p0=rng.normal(size=2*n)*1.2
    r=minimize(f,p0,method='BFGS',options={'maxiter':6000,'gtol':1e-13})
    c=unpack(r.x)
    if f(r.x)<1e-16 and margins(c)>5e-3:
        found.append((f(r.x),margins(c),c.copy()))

print("candidate configs (V=0, no near-zero centre, all distinct):",len(found))
for (fv,mg,c) in found[:6]:
    print("---- f=%.2e margin=%.2e"%(fv,mg)); print(" c=",np.round(c,5))
    V=cv(KP(c,np.conj(c),6)); print(" |V|=%.2e"%np.abs(V).max())
    for i in range(3):
        d=c[np.arange(6)!=i]
        P0=cv(KP(d,np.conj(d),5))[0]
        pts=[]; mids=[]; ok=True
        for j in range(5):
            g=d[np.arange(5)!=j]
            v=cv(KP(g,np.conj(g),4))
            mid=v[2]
            mids.append(abs(mid))
            if abs(mid)<1e-6: ok=False
            pts.append(-v[-1]/mid)
        if ok and abs(P0)>8e-3:
            err,s=collinearity_err(pts)
            print("  i=%d P0=%.3f  all mids>0  collinear err=%.2e (|scale|=%.1f)"%(i,abs(P0),err,np.abs(pts).max()))
        else:
            print("  i=%d P0=%.3f skipped (mid degenerate=%s)"%(i,abs(P0),not ok))
