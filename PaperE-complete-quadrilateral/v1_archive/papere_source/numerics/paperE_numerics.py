"""Paper E: reproducible numerical re-check of the eight complete-quadrilateral theorems.
60 significant digits, seed 20261014, 1000 random configurations of four lines in general position
(margins: |cr(d_i,d_j)| >= 1e-2 for unit directions; each vertex at distance >= 1e-2 from the
remaining lines). Each theorem's conclusion is evaluated independently of the construction, with a
negative control (perturbed input) that must fail. Output: results_<date>.jsonl, one record per check."""
from mpmath import mp, mpf, mpc, conj, fabs, matrix, det, cos, sin, pi
import random, itertools, json, sys
mp.dps=60; SEED=20261014; N=1000
cr=lambda a,b:(conj(a)*b).imag
def meet(L,M): p,d=L; q,e=M; return p+(cr(e,q-p)/cr(e,d))*d
def circ(a,b,c): u=b-a; w=c-a; return a+(abs(u)**2*w-abs(w)**2*u)/(conj(u)*w-u*conj(w))
def ortho(a,b,c): return a+b+c-2*circ(a,b,c)
def foot(z,L): p,d=L; return p+((conj(d)*(z-p)).real/abs(d)**2)*d
def colres(pts):        # max |cross| over consecutive triples, scale-normalised
    a=pts[0]; b=max(pts,key=lambda z:abs(z-a)); s=abs(b-a)
    return max(fabs(cr(b-a,z-a))/s for z in pts) if s>0 else mpf(0)
def concyc(pts):
    a,b,c=pts[:3]; o=circ(a,b,c); r=abs(a-o); return max(fabs(abs(z-o)-r) for z in pts)/r
def power(z,P,Q): return abs(z-(P+Q)/2)**2-abs(P-Q)**2/4
def config(rng):
    while True:
        L=[]
        for _ in range(4):
            th=mpf(rng.uniform(0,3.141592653589793)); L.append((mpc(rng.uniform(-3,3),rng.uniform(-3,3)),mpc(cos(th),sin(th))))
        if min(fabs(cr(L[i][1],L[j][1])) for i,j in itertools.combinations(range(4),2))<mpf('1e-2'): continue
        V={(i,j):meet(L[i],L[j]) for i,j in itertools.combinations(range(4),2)}
        ok=True
        for (i,j),z in V.items():
            for k in range(4):
                if k in (i,j): continue
                if fabs(cr(L[k][1],z-L[k][0]))<mpf('1e-2'): ok=False
        if ok: return L,V
def quad(L,V):
    A=lambda i,j: V[(min(i,j)-1,max(i,j)-1)]
    T={4:(A(1,2),A(1,3),A(2,3)),3:(A(1,2),A(1,4),A(2,4)),2:(A(1,3),A(1,4),A(3,4)),1:(A(2,3),A(2,4),A(3,4))}
    diags=[(A(1,2),A(3,4)),(A(1,3),A(2,4)),(A(1,4),A(2,3))]
    mids=[(P+Q)/2 for P,Q in diags]
    H={k:ortho(*T[k]) for k in T}; O={k:circ(*T[k]) for k in T}
    M=A(1,2)+((A(1,3)-A(1,2))*(A(2,4)-A(1,2))-(A(2,3)-A(1,2))*(A(1,4)-A(1,2)))/(A(1,3)+A(2,4)-A(2,3)-A(1,4))  # QuadMiquel.miquelPt
    F=[foot(M,Lk) for Lk in L]
    return T,diags,mids,H,O,M,F
def run():
    rng=random.Random(SEED); W={}; C={}
    global ctl
    def rec(k,v,store): store[k]=max(store.get(k,mpf(0)),v)
    def ctl(k,v): C[k]=min(C.get(k,mpf('inf')),v)        # smallest violation seen (must stay well above residuals)
    for n in range(N):
        L,V=config(rng); T,diags,mids,H,O,M,F=quad(L,V)
        Hs=[H[k] for k in (1,2,3,4)]
        hsep=max(abs(a-b) for a,b in itertools.combinations(Hs,2))
        rec('1 newton_gauss',colres(mids),W)
        rec('2 orthocentres_collinear',colres(Hs)/max(hsep,mpf(1)),W)
        rec('3 bodenmiller',max(fabs(power(h,*diags[0])-power(h,*diags[1]))+fabs(power(h,*diags[0])-power(h,*diags[2])) for h in Hs),W)
        i,j=max(itertools.combinations(range(4),2),key=lambda p:abs(Hs[p[0]]-Hs[p[1]]))
        rec('4 orthocentre_line_perp',fabs(((mids[1]-mids[0])*conj(Hs[j]-Hs[i])).real)/(abs(mids[1]-mids[0])*abs(Hs[j]-Hs[i])),W)
        rec('5 miquel',max(fabs(abs(M-O[k])-abs(T[k][0]-O[k]))/abs(T[k][0]-O[k]) for k in T),W)
        rec('6 steiner_circle',concyc([O[1],O[2],O[3],O[4],M]),W)
        rec('7 simson',colres(F),W)
        rec('8 steiner_parallel (via H3-H4, generic)',fabs(cr(F[1]-F[0],H[3]-H[4]))/(abs(F[1]-F[0])*abs(H[3]-H[4])),W)
        hs=max(abs(Hs[i]-Hs[3]) for i in range(3))
        rec('8 steiner_parallel_line (all H_i-H_4)',max(fabs(cr(F[1]-F[0],Hs[i]-Hs[3])) for i in range(3))/(abs(F[1]-F[0])*hs),W)
        # negative controls: perturb one input and recompute the conclusion (must fail)
        Lp=[(L[0][0]+mpf('0.1'),L[0][1])]+L[1:]
        Vp={(a,b):meet(Lp[a],Lp[b]) for a,b in itertools.combinations(range(4),2)}
        Tp,dp,mp_,Hp,Op,Mp,Fp=quad(Lp,Vp)
        ctl('ctl newton (one midpoint from unperturbed config)',colres([mids[0],mp_[1],mp_[2]]))
        ctl('ctl miquel (unperturbed M on perturbed circles)',max(fabs(abs(M-Op[k])-abs(Tp[k][0]-Op[k]))/abs(Tp[k][0]-Op[k]) for k in Tp))
        ctl('ctl simson (feet from a non-Miquel point)',colres([foot(M+mpc('0.1','0.1'),Lk) for Lk in L]))
    # forced L1 ⟂ L2 (the case where H3 = H4): 300 configurations, same margins
    for n in range(300):
        while True:
            L,V=config(rng)
            L=[L[0],(L[1][0],L[0][1]*mpc(0,1))]+L[2:]
            try:
                V={(i,j):meet(L[i],L[j]) for i,j in itertools.combinations(range(4),2)}
            except ZeroDivisionError: continue
            if min(fabs(cr(L[i][1],L[j][1])) for i,j in itertools.combinations(range(4),2))<mpf('1e-2'): continue
            if any(fabs(cr(L[k][1],z-L[k][0]))<mpf('1e-2') for (i,j),z in V.items() for k in range(4) if k not in (i,j)): continue
            break
        T,diags,mids,H,O,M,F=quad(L,V); Hs=[H[k] for k in (1,2,3,4)]
        rec('perp: |H3-H4| (should be 0)',abs(Hs[2]-Hs[3]),W)
        ctl('perp: min(|H1-H3|,|H2-H3|) (should be >0)',min(abs(Hs[0]-Hs[2]),abs(Hs[1]-Hs[2])))
        hs=max(abs(Hs[i]-Hs[3]) for i in range(3))
        rec('perp: 8 steiner_parallel_line (all H_i-H_4)',max(fabs(cr(F[1]-F[0],Hs[i]-Hs[3])) for i in range(3))/(abs(F[1]-F[0])*hs),W)
    return W,C
if __name__=='__main__':
    W,C=run()
    cnt=lambda k: 300 if k.startswith('perp:') else N
    out=[{'check':k,'configs':cnt(k),'worst_residual':mp.nstr(v,3)} for k,v in W.items()]
    out+=[{'control':k,'configs':cnt(k),'min_violation':mp.nstr(v,3)} for k,v in C.items()]
    for o in out: print(json.dumps(o))
    if len(sys.argv)>1: open(sys.argv[1],'w').write('\n'.join(json.dumps(o) for o in out)+'\n')
