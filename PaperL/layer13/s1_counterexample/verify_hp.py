"""High-precision re-check of a candidate counterexample (mpmath, 60 digits)."""
import sys
from fractions import Fraction as F
from itertools import combinations, product
import mpmath as mp
mp.mp.dps=60

def _mp(x):
    if isinstance(x, mp.mpf): return x
    return mp.mpf(x.numerator)/x.denominator
def to_mp(c): return (_mp(c[0]), _mp(c[1]))
def coll3_mp(a,b,c,tol=mp.mpf(10)**-30):
    a,b,c=to_mp(a),to_mp(b),to_mp(c)
    cr=cross(sub(b,a),sub(c,a))
    n=mp.sqrt(dot(sub(b,a),sub(b,a)))*mp.sqrt(dot(sub(c,a),sub(c,a)))
    return abs(cr) <= tol*max(mp.mpf(1),n)
def sub(a,b): return (a[0]-b[0],a[1]-b[1])
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def dot(a,b): return a[0]*b[0]+a[1]*b[1]
def cross(a,b): return a[0]*b[1]-a[1]*b[0]
def scal(t,a): return (t*a[0],t*a[1])
def dist2(a,b):
    d=sub(a,b); return dot(d,d)

def second(c,d):   # exact rational second point
    v=(-(c[1]-d[1]),c[0]-d[0]); den=(c[0]-d[0])**2+(c[1]-d[1])**2
    if den==0: return None
    t=F(2)*dot(v,c)/den
    return scal(t,v)
def tr(c,d): return c!=d and second(c,d) not in (None,(0,0))
def col3(a,b,c): return cross(sub(b,a),sub(c,a))==0

class Obj:
    def __init__(self,pts):          # pts: exact rational tuples
        assert len(set(pts))>=2
        self.pts=pts
        if col3(*pts):
            self.kind='line'; self.a=pts[0]; self.b=pts[1]
        else:
            self.kind='circle'
            ax,ay=pts[0]; bx,by=pts[1]; cx,cy=pts[2]
            d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
            self.c=(((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d,
                    ((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d)
            self.r2=sum((p-q)**2 for p,q in zip(pts[0],self.c))
    def contains(self,z,tol=mp.mpf(10)**-40):
        if z=='inf': return self.kind=='line'
        if self.kind=='line':
            a=to_mp(self.a); b=to_mp(self.b); d=sub(b,a)
            return abs(cross(sub(z,a),d)) <= tol*max(mp.mpf(1),mp.sqrt(dot(d,d)))
        C=to_mp(self.c); r2=mp.mpf(self.r2.numerator)/self.r2.denominator
        return abs(dist2(z,C)-r2) <= tol*max(mp.mpf(1),r2)
    def approx_contains(self,z,tol=mp.mpf(10)**-25):
        if z=='inf': return self.kind=='line'
        if self.kind=='line':
            a=to_mp(self.a); b=to_mp(self.b); d=sub(b,a)
            L=mp.sqrt(dot(d,d))
            return abs(cross(sub(z,a),d))/L <= tol*max(mp.mpf(1),L)
        C=to_mp(self.c); r2=mp.mpf(self.r2.numerator)/self.r2.denominator
        return abs(dist2(z,C)-r2) <= tol*max(mp.mpf(1),r2)

def level3(cfg,drop):
    idx=[i for i in range(len(cfg)) if i!=drop]
    return Obj([second(cfg[idx[0]],cfg[idx[1]]), second(cfg[idx[0]],cfg[idx[2]]), second(cfg[idx[1]],cfg[idx[2]])])

def inter(o1,o2):
    """exact-ish intersections of two blind objects (mpf coords)."""
    A=[to_mp(o1.a)] if o1.kind=='line' else None
    if o1.kind=='line' and o2.kind=='line':
        a=to_mp(o1.a); b=to_mp(o1.b); c=to_mp(o2.a); d=to_mp(o2.b)
        d1=sub(b,a); d2=sub(d,c); dd=cross(d1,d2)
        if abs(dd)<mp.mpf(10)**-50: return []
        t=cross(sub(c,a),d2)/dd
        return [add(a,scal(t,d1))]
    if o1.kind=='line': o1,o2=o2,o1
    C=to_mp(o1.c); r2=mp.mpf(o1.r2.numerator)/o1.r2.denominator
    r=mp.sqrt(r2)
    if o2.kind=='line':
        a=to_mp(o2.a); b=to_mp(o2.b); d=sub(b,a); L2=dot(d,d)
        t=dot(sub(C,a),d)/L2; foot=add(a,scal(t,d))
        h2=r2-dist2(foot,C)
        if h2 < -mp.mpf(10)**-40: return []
        h=mp.sqrt(max(h2,mp.mpf(0)))
        n=(-d[1]/mp.sqrt(L2), d[0]/mp.sqrt(L2))
        return [add(foot,scal(h,n)), add(foot,scal(-h,n))]
    C2=to_mp(o2.c); r2b=mp.mpf(o2.r2.numerator)/o2.r2.denominator; rb=mp.sqrt(r2b)
    dv=sub(C2,C); d=mp.sqrt(dot(dv,dv))
    if d < mp.mpf(10)**-40: return []
    a=(r2-r2b+d*d)/(2*d); h2=r2-a*a
    if h2 < -mp.mpf(10)**-40: return []
    h=mp.sqrt(max(h2,mp.mpf(0)))
    base=add(C,scal(a/d,dv)); n=(-dv[1]/d,dv[0]/d)
    return [add(base,scal(h,n)), add(base,scal(-h,n))]

def common_points(cfg):
    objs=[level3(cfg,i) for i in range(4)]
    pts=['inf'] if all(o.kind=='line' for o in objs) else []
    for i,j in combinations(range(4),2):
        for p in inter(objs[i],objs[j]):
            if all(o.approx_contains(p) for o in objs):
                if not any(q!='inf' and dist2(p,q)<mp.mpf(10)**-30 for q in pts):
                    pts.append(p)
    return pts, "".join('L' if o.kind=='line' else 'C' for o in objs)

def on_gcircle(pts,tol=mp.mpf(10)**-30):
    fin=[to_mp(p) for p in pts if p!='inf']
    if len(fin)<=2: return True
    if all(coll3_mp(fin[0],fin[1],q) for q in fin[2:]): return True
    if len(fin)>=3:
        ax,ay=to_mp(fin[0]); bx,by=to_mp(fin[1]); cx,cy=to_mp(fin[2])
        d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
        if abs(d)<mp.mpf(10)**-40: return False
        ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
        uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
        U=(ux,uy); r2=dist2(fin[0],U)
        rest=fin[3:]
        return all(abs(dist2(q,U)-r2)<=tol*max(mp.mpf(1),r2) for q in rest)

def check(cs):
    cs=[(F(a),F(b)) for a,b in cs]
    sets=[]; kinds=[]
    for drop in range(len(cs)):
        sub_cfg=[cs[j] for j in range(len(cs)) if j!=drop]
        pts,k=common_points(sub_cfg); sets.append(pts); kinds.append(k)
    if any(not s for s in sets): return False,sets,kinds,None
    for choice in product(*sets):
        fin=[p for p in choice if p!='inf']
        if 'inf' in choice:
            ok = (len(fin)<=1) or all(coll3_mp(fin[0],fin[1],q) for q in fin[2:])
        else:
            ok = on_gcircle(fin)
        if ok: return True,sets,kinds,choice
    return False,sets,kinds,None

if __name__=="__main__":
    cs=[(F(-39,4),F(3)),(F(-5,2),F(11)),(F(13,2),F(-1,2)),(F(13,2),F(-25,2)),(F(15,4),F(1,2))]
    ok,sets,kinds,ch=check(cs)
    print("level5 exists:",ok)
    print("kinds per drop:",kinds)
    for i,s in enumerate(sets): print(i,s)
