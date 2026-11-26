"""Search for a counterexample to BlindN1: a BlindGenPos configuration for which no
BlindClifford object exists.  Exact rational arithmetic throughout.

Blind model (from scratch/BlindCompareFull.lean):
  BlindCircle c   := {z : |z-c| = |c|}                     (passes through 0)
  BlindSecond c d := the unique nonzero point on both circles (exists iff transversal)
  BlindGenPos c   := all pairs transversal; no common nonzero point of any three circles;
                     the three second points of every triple pairwise distinct
  BlindCliffordP 3 c X  := BlindIsGCircle X  and the three second points lie in X
  BlindCliffordP 4 c X  := X = {p} and each deletion's level-3 object contains p
So BlindN1 fails at n=4 iff some BlindGenPos c has four level-3 objects with no common
blind point.
"""
from fractions import Fraction as F
from itertools import combinations
import random

def sub(a,b): return (a[0]-b[0], a[1]-b[1])
def add(a,b): return (a[0]+b[0], a[1]+b[1])
def dot(a,b): return a[0]*b[0]+a[1]*b[1]
def cross(a,b): return a[0]*b[1]-a[1]*b[0]
def scal(t,a): return (t*a[0], t*a[1])

def second(c,d):
    """nonzero second intersection of circles through 0 centred at c,d (may be 0)."""
    v = (-(c[1]-d[1]), c[0]-d[0])          # i*(c-d)
    den = (c[0]-d[0])**2 + (c[1]-d[1])**2
    if den == 0: return None               # same centre
    t = F(2)*dot(v,c)/den
    return scal(t,v)

def on_circle(z,c):                        # |z-c|^2 == |c|^2
    return (z[0]-c[0])**2 + (z[1]-c[1])**2 == c[0]**2+c[1]**2

def transversal(c,d):
    if c==d: return False
    s = second(c,d)
    return s is not None and s!=(0,0)

def collinear(a,b,c):
    return cross(sub(b,a), sub(c,a)) == 0

def common_nonzero(c1,c2,c3):
    """is there a z != 0 on all three circles?"""
    # all centres on one line (constant dot) -> reflection of 0 across that line
    # solve: find z != 0 with dot(z,ci)=|z|^2/2 for all i  -> centres collinear,
    # and then the common point is the reflection of 0 in the line.
    if not collinear(c1,c2,c3): return None
    # line through c1,c2: check whether it passes through 0
    if cross(c1,c2)==0: return None        # line through origin: only 0 is common
    # projection of 0 onto line: p = c1 + t*(c2-c1), t = -dot(c1,d)/|d|^2
    d = sub(c2,c1)
    t = -dot(c1,d)/dot(d,d)
    p = add(c1, scal(t,d))
    q = scal(F(2),p)                       # reflection of 0
    if on_circle(q,c1) and on_circle(q,c2) and on_circle(q,c3) and q!=(0,0):
        return q
    return None

def genpos(cs):
    n=len(cs)
    for i,j in combinations(range(n),2):
        if not transversal(cs[i],cs[j]): return False
    for i,j,k in combinations(range(n),3):
        if common_nonzero(cs[i],cs[j],cs[k]) is not None: return False
        s = [second(cs[i],cs[j]), second(cs[i],cs[k]), second(cs[j],cs[k])]
        if len(set(s))<3: return False
    return True

def circumcenter(a,b,c):
    """exact rational circumcentre of three non-collinear rational points."""
    ax,ay=a; bx,by=b; cx,cy=c
    d = 2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    if d==0: return None
    ux = ((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
    uy = ((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
    return (ux,uy)

class Obj:
    """blind generalised circle: ('line',a,b) or ('circle',centre,r2)"""
    def __init__(self, pts):
        self.pts=pts
        if len(set(pts))<2:
            raise ValueError("degenerate object")
        if len(pts)==2 or collinear(*pts):
            a,b=pts[0],pts[1]
            self.kind='line'; self.a=a; self.b=b
        else:
            self.kind='circle'; self.c=circumcenter(*pts)
            self.r2=(pts[0][0]-self.c[0])**2+(pts[0][1]-self.c[1])**2
    def contains(self,z):
        if z is None: return False
        if self.kind=='line':
            if z=='inf': return True
            return cross(sub(z,self.a), sub(self.b,self.a))==0
        else:
            if z=='inf': return False
            return (z[0]-self.c[0])**2+(z[1]-self.c[1])**2 == self.r2
    def contains_approx(self,z,tol=1e-9):
        if z is None: return False
        if self.kind=='line':
            if z=='inf': return True
            d=sub(self.b,self.a)
            num=abs(float(cross(sub(z,self.a),d)))
            den=max(1e-30,float(dot(d,d))**0.5)
            return num/den < tol
        else:
            if z=='inf': return False
            dx=float(z[0])-float(self.c[0]); dy=float(z[1])-float(self.c[1])
            return abs(dx*dx+dy*dy-float(self.r2)) < tol

def level3(cs, drop=None):
    """level-3 blind object for a triple (optionally dropping index drop from 4)."""
    idx=[i for i in range(len(cs)) if i!=drop]
    s=[second(cs[idx[0]],cs[idx[1]]), second(cs[idx[0]],cs[idx[2]]), second(cs[idx[1]],cs[idx[2]])]
    return Obj(s)

def level4_point(cs):
    """return a common blind point of the four level-3 objects, or None."""
    objs=[level3(cs,drop=i) for i in range(4)]
    if all(o.kind=='line' for o in objs):
        return 'inf'                      # every blind line contains infinity
    # candidate finite points: pairwise intersections of the objects
    cands=[]
    for i,j in combinations(range(4),2):
        cands += intersections(objs[i],objs[j])
    cands=[p for p in cands if p!='inf']
    for p in cands:
        if all(o.contains_approx(p) for o in objs): return p
    return None

def intersections(o1,o2,tol=1e-9):
    """approximate intersection points (floats) of two blind objects."""
    out=[]
    if o1.kind=='line' and o2.kind=='line':
        # directions
        d1=sub(o1.b,o1.a); d2=sub(o2.b,o2.a)
        dd=cross(d1,d2)
        if dd!=0:
            t=cross(sub(o2.a,o1.a),d2)/dd
            out.append(add(o1.a,scal(t,d1)))
        return out
    if o1.kind=='line': o1,o2=o2,o1
    # o1 circle, o2 line or circle
    if o2.kind=='line':
        # project centre
        d=sub(o2.b,o2.a); t=dot(sub(o1.c,o2.a),d)/dot(d,d)
        foot=add(o2.a,scal(t,d))
        h2=float(o1.r2)-float((foot[0]-o1.c[0])**2+(foot[1]-o1.c[1])**2)
        if h2 < -tol: return []
        h=h2**0.5
        n=(float(-d[1]),float(d[0])); ln=float(dot(d,d))**0.5
        n=(n[0]/ln,n[1]/ln)
        return [(float(foot[0])+h*n[0],float(foot[1])+h*n[1]),(float(foot[0])-h*n[0],float(foot[1])-h*n[1])]
    # circle-circle
    x1,y1, r1=float(o1.c[0]),float(o1.c[1]),float(o1.r2)**0.5
    x2,y2, r2=float(o2.c[0]),float(o2.c[1]),float(o2.r2)**0.5
    dx,dy=x2-x1,y2-y1; d=(dx*dx+dy*dy)**0.5
    if d<1e-12: return []
    a=(r1*r1-r2*r2+d*d)/(2*d)
    h2=r1*r1-a*a
    if h2< -tol: return []
    h=max(h2,0)**0.5
    xm=x1+a*dx/d; ym=y1+a*dy/d
    if h<1e-14: return [(xm,ym)]
    return [(xm+h*dy/d, ym-h*dx/d),(xm-h*dy/d, ym+h*dx/d)]

if __name__=="__main__":
    random.seed(7)
    found=[]
    trials=0
    vals=[F(k,2) for k in range(-6,7)]
    grid=[(a,b) for a in vals for b in vals if (a,b)!=(0,0)]
    random.shuffle(grid)
    for _ in range(60000):
        cs=random.sample(grid,4); trials+=1
        if not genpos(cs): continue
        objs=[level3(cs,drop=i) for i in range(4)]
        kinds="".join('L' if o.kind=='line' else 'C' for o in objs)
        p=level4_point(cs)
        if p is None:
            found.append((cs,kinds))
            print("FAIL n=4", cs, kinds); break
    print("trials",trials,"failures",len(found))
