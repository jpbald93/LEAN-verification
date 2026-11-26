import numpy as np
from scipy.optimize import minimize

def KP(x, y, n):
    m = n//2
    rows=[]
    for k in range(n):
        row=[]
        for j in range(n+1):
            if j <= m:
                row.append((-x[k])**j * y[k]**(n-m-j))
            else:
                row.append(-((-x[k])**(j-(m+1)) * y[k]**(n-m-1-(j-(m+1)))))
        rows.append(row)
    return np.array(rows, dtype=complex)

def crossVec(A):
    n, m1 = A.shape
    return np.array([(-1)**j * np.linalg.det(np.delete(A, j, axis=1)) for j in range(m1)], dtype=complex)

def unpack(p):
    z = p[:len(p)//2] + 1j*p[len(p)//2:]
    return z

def f(p):
    c = unpack(p)
    A = KP(c, np.conj(c), len(c))
    v = crossVec(A)
    return float(np.sum(np.abs(v)**2))

def genpos_ok(c):
    n=len(c)
    for i in range(n):
        for j in range(i+1,n):
            if abs(np.conj(c[i])*c[j] - c[i]*np.conj(c[j])) < 1e-9: return False
            if abs(c[i]-c[j])<1e-9: return False
    return True

n=6
rng=np.random.default_rng(7)
best=None
for trial in range(60):
    p0=rng.normal(size=2*n)*1.3
    r=minimize(f,p0,method='BFGS',options={'maxiter':4000,'gtol':1e-12})
    p=r.x
    c=unpack(p)
    A=KP(c,np.conj(c),n)
    s=np.linalg.svd(A,compute_uv=False)
    rat=s[-1]/s[0]
    if best is None or f(p)<best[0]:
        best=(f(p),rat,c.copy(),s.copy())
    if f(p)<1e-18 and genpos_ok(c):
        print("HIT trial",trial,"f=",f(p),"sigma_min/sigma_max=",rat,"genpos_ok=",genpos_ok(c))
        print("c=",repr(c))
        break
else:
    print("no exact hit; best f=",best[0],"sigma ratio",best[1])
    print("best c=",repr(best[2]))
    print("s=",best[3])
