import sys, random
sys.path.insert(0,'AFM/PaperL/layer13/s1_counterexample')
from fractions import Fraction as F
from itertools import combinations, product
from verify_hp import common_points, on_gcircle, coll3_mp, to_mp, dist2, sub, cross, col3
import mpmath as mp
mp.mp.dps=50

def level5_objects(cfg5):
    """all generalised circles meeting each P4 set of the five deletions (natural candidates)."""
    sets=[]
    for drop in range(5):
        sub_cfg=[cfg5[j] for j in range(5) if j!=drop]
        pts,k=common_points(sub_cfg)
        if not pts: return []
        sets.append(pts)
    out=[]
    for choice in product(*sets):
        fin=[p for p in choice if p!='inf']
        if 'inf' in choice:
            if len(fin)<=1 or all(coll3_mp(fin[0],fin[1],q) for q in fin[2:]):
                if len(fin)>=2:
                    # line through two finite points
                    a,b=to_mp(fin[0]),to_mp(fin[1])
                    if dist2(a,b)>mp.mpf(10)**-20: out.append(('line',a,b))
                else:
                    out.append(('line_anyinf',))
        else:
            if on_gcircle(fin):
                finmp=[to_mp(p) for p in fin]
                if len(finmp)>=3 and not all(coll3_mp(finmp[0],finmp[1],q) for q in finmp[2:]):
                    ax,ay=finmp[0]; bx,by=finmp[1]; cx,cy=finmp[2]
                    d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
                    if abs(d)<mp.mpf(10)**-40: continue
                    ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
                    uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
                    U=(ux,uy); r2=dist2(finmp[0],U)
                    out.append(('circle',U,r2,finmp))
                elif len(finmp)==2:
                    out.append(('circ2',finmp[0],finmp[1],finmp))
    return out

def contains(obj,p,tol=mp.mpf(10)**-25):
    if obj[0]=='line_anyinf': return p=='inf'
    if obj[0]=='line':
        a,b=obj[1],obj[2]; d=sub(b,a); L=mp.sqrt(dist2(a,b))
        return abs(cross(sub(to_mp(p),a),d))/L <= tol*max(mp.mpf(1),L)
    if obj[0]=='circle':
        U,r2,_=obj[1],obj[2],obj[3]
        return abs(dist2(to_mp(p),U)-r2) <= tol*max(mp.mpf(1),r2)
    if obj[0]=='circ2': return True   # only two points: any circle through them
    return False

def level6_ok(cfg6):
    objs=[]
    for drop in range(6):
        sub_cfg=[cfg6[j] for j in range(6) if j!=drop]
        L=level5_objects(sub_cfg)
        if not L: return False,"no level-5 object for deletion %d"%drop
        objs.append(L)
    # candidate points: finite intersections between first two families
    cands=[]
    for o1 in objs[0]:
        for o2 in objs[1]:
            if o1[0]=='line' and o2[0]=='line':
                a,b=o1[1],o1[2]; c,d=o2[1],o2[2]
                d1=sub(b,a); d2=sub(d,c); dd=cross(d1,d2)
                if abs(dd)>mp.mpf(10)**-30:
                    t=cross(sub(c,a),d2)/dd; cands.append(add(a,mul(t,d1)))
            elif o1[0]=='circle' and o2[0]=='circle':
                U1,r1=o1[1],o1[2]; U2,r2=o2[1],o2[2]
                dv=sub(U2,U1); d=mp.sqrt(dist2(U1,U2))
                if d<mp.mpf(10)**-30: continue
                aa=(r1-r2+d*d)/(2*d); h2=r1-aa*aa
                if h2< -mp.mpf(10)**-30: continue
                h=mp.sqrt(max(h2,mp.mpf(0)))
                base=add(U1,scal(aa/d,dv)); n=(-dv[1]/d,dv[0]/d)
                cands.append(add(base,scal(h,n)))
                if h>mp.mpf(10)**-25: cands.append(add(base,scal(-h,n)))
            elif o1[0]=='line' and o2[0]=='circle':
                # project
                a,b=o1[1],o1[2]; U,r2=o2[1],o2[2]
                d=sub(b,a); t=dot_(sub(U,a),d)/dist2(a,b) if False else None
            # mixed line/circle handled below by direct sampling is skipped
    for p in cands:
        if all(any(contains(o,p) for o in fam) for fam in objs):
            return True,p
    # also test infinity
    if all(any(o[0] in ('line','line_anyinf') for o in fam) for fam in objs):
        return True,'inf'
    return False,"no common point among %d candidates"%len(cands)

def mul(t,a): return (t*a[0],t*a[1])
def scal(t,a): return mul(t,a)
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def dot_(a,b): return a[0]*b[0]+a[1]*b[1]

if __name__=="__main__":
    from search import genpos
    random.seed(9)
    t=0;f=0;ex=[]
    for _ in range(60):
        cs=set()
        while len(cs)<6:
            c=(F(random.randint(-40,40),4),F(random.randint(-40,40),4))
            if c!=(0,0): cs.add(c)
        cs=list(cs)
        if not genpos(cs): continue
        t+=1
        ok,why=level6_ok(cs)
        if not ok:
            f+=1
            if len(ex)<2: ex.append((cs,why))
    print("n=6 genpos configs:",t,"failures:",f)
    for cs,why in ex: print(why,[tuple(str(x) for x in c) for c in cs])
