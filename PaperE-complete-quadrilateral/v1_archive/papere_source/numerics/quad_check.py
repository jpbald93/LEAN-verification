# Complete quadrilateral: numeric sanity check of the candidate Paper E statements (60 digits, seed 20261014).
from mpmath import mp, mpf, mpc, conj, fabs, matrix, det
import random, itertools
mp.dps=60; rng=random.Random(20261014)
def cr(a,b): return (conj(a)*b).imag          # cross product
def meet(L1,L2):                                # line = (point, direction)
    p,d=L1; q,e=L2; t=cr(q-p,e)/cr(d,e); return p+t*d
def col(a,b,c): return fabs(cr(b-a,c-a))
def circ(a,b,c):
    u=b-a; w=c-a
    return a+(abs(u)**2*w-abs(w)**2*u)/(conj(u)*w-u*conj(w))   # circumcentre
def ortho(a,b,c): o=circ(a,b,c); return a+b+c-2*o
def foot(p,L): q,d=L; return q+d*((conj(d)*(p-q)).real/abs(d)**2)
def concyc(a,b,c,d):
    M=matrix([[abs(z)**2,z.real,z.imag,1] for z in (a,b,c,d)]); return fabs(det(M))
W={k:mpf(0) for k in ['newton','orthocol','coax','miquel','steinercirc','simson','steinerpar','perp']}
for _ in range(300):
    L=[(mpc(rng.uniform(-3,3),rng.uniform(-3,3)),mpc(rng.uniform(-1,1),rng.uniform(-1,1))) for _ in range(4)]
    V={(i,j):meet(L[i],L[j]) for i,j in itertools.combinations(range(4),2)}
    v=lambda i,j: V[(min(i,j),max(i,j))]
    diags=[(v(0,1),v(2,3)),(v(0,2),v(1,3)),(v(0,3),v(1,2))]
    mids=[(a+b)/2 for a,b in diags]; W['newton']=max(W['newton'],col(*mids))
    tris=[[k for k in range(4) if k!=m] for m in range(4)]
    def tri(m): i,j,k=tris[m]; return v(i,j),v(i,k),v(j,k)
    H=[ortho(*tri(m)) for m in range(4)]; O=[circ(*tri(m)) for m in range(4)]
    W['orthocol']=max(W['orthocol'],col(H[0],H[1],H[2]),col(H[0],H[1],H[3]))
    pw=lambda z,dg: abs(z-(dg[0]+dg[1])/2)**2-abs(dg[0]-dg[1])**2/4   # power wrt circle on diagonal
    for h in H: W['coax']=max(W['coax'],fabs(pw(h,diags[0])-pw(h,diags[1])),fabs(pw(h,diags[1])-pw(h,diags[2])))
    # Miquel point: second intersection of circumcircles 0 and 1 (they share vertex v common to both triangles)
    a,b,c=tri(0); o0,o1=O[0],O[1]; common=[p for p in tri(0) if min(abs(p-q) for q in tri(1))<mpf(10)**-40][0]
    M=2*foot(common,(o0,o1-o0))-common       # reflection of common point in line of centres
    W['miquel']=max(W['miquel'],*[fabs(abs(M-O[m])-abs(tri(m)[0]-O[m])) for m in range(4)])
    W['steinercirc']=max(W['steinercirc'],concyc(O[0],O[1],O[2],O[3]),concyc(O[0],O[1],O[2],M))
    F=[foot(M,Lk) for Lk in L]; W['simson']=max(W['simson'],col(F[0],F[1],F[2]),col(F[0],F[1],F[3]))
    W['steinerpar']=max(W['steinerpar'],fabs(cr(F[1]-F[0],H[1]-H[0])))
    W['perp']=max(W['perp'],fabs(((mids[1]-mids[0])*conj(H[1]-H[0])).real))
for k,x in W.items(): print(f"{k:12s} worst residual {mp.nstr(x,3)}")
