import sys
sys.path.insert(0,'AFM/PaperL/layer13/s1_counterexample')
from search import *
from itertools import combinations, product

TOL=1e-7
def fpt(p): return (float(p[0]),float(p[1]))
def coll3(a,b,c,tol=TOL):
    a,b,c=fpt(a),fpt(b),fpt(c)
    cr=(b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    n1=((b[0]-a[0])**2+(b[1]-a[1])**2)**0.5
    n2=((c[0]-a[0])**2+(c[1]-a[1])**2)**0.5
    return abs(cr)<=tol*max(1.0,n1*n2)

def circle_params(p,q,r):
    """float circle through three non-collinear points -> (cx,cy,r2) or None."""
    (ax,ay),(bx,by),(cx,cy)=fpt(p),fpt(q),fpt(r)
    d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    if abs(d)<1e-13: return None
    ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
    uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
    return (ux,uy,(ax-ux)**2+(ay-uy)**2)

def fits_circle(fin):
    """do these finite points lie on one generalised circle (circle or line)?"""
    n=len(fin)
    if n<=2: return True
    if all(coll3(fin[0],fin[1],q) for q in fin[2:]): return True
    cp=circle_params(fin[0],fin[1],fin[2])
    if cp is None: return False
    ux,uy,r2=cp
    return all(abs((fpt(q)[0]-ux)**2+(fpt(q)[1]-uy)**2-r2)<=1e-5*max(1.0,r2) for q in fin)

def common_points(cfg):
    """P at the even level: points lying in every level-(n-1) object of cfg (a 4-set).
       returns list of finite points plus 'inf' if every object is a line."""
    objs=[level3(cfg,drop=i) for i in range(4)]
    pts=[]
    if all(o.kind=='line' for o in objs): pts.append('inf')
    for i,j in combinations(range(4),2):
        for p in intersections(objs[i],objs[j]):
            if p=='inf': continue
            if all(o.contains_approx(p) for o in objs):
                if not any(abs(p[0]-q[0])<1e-7 and abs(p[1]-q[1])<1e-7 for q in pts if q!='inf'):
                    pts.append(p)
    return pts

def even_level_ok(cfg):
    return bool(common_points(cfg))

def odd_level_ok(cfg):
    """X must be a generalised circle meeting every common_points set of the (n-1)-subsets."""
    sets=[]
    for drop in range(len(cfg)):
        sub=[cfg[j] for j in range(len(cfg)) if j!=drop]
        s=common_points(sub)
        if not s: return False,sets
        sets.append(s)
    for choice in product(*sets):
        fin=[p for p in choice if p!='inf']
        if 'inf' in choice:
            # X must be a line (only a line contains the point at infinity)
            if len(fin)<=1 or all(coll3(fin[0],fin[1],q) for q in fin[2:]):
                return True,choice
        else:
            if fits_circle(fin):
                return True,choice
    return False,sets

grid=[(F(a),F(b)) for a in range(-2,3) for b in range(-2,3) if (a,b)!=(0,0)]
t4,f4,t5,f5=0,0,0,0
ex4=[];ex5=[]
for quad in combinations(grid,4):
    quad=list(quad)
    if not genpos(quad): continue
    t4+=1
    if not even_level_ok(quad):
        f4+=1
        if len(ex4)<2: ex4.append(quad)
    for extra in grid:
        if extra in quad: continue
        cs=quad+[extra]
        if not genpos(cs): continue
        t5+=1
        ok,sets=odd_level_ok(cs)
        if not ok:
            f5+=1
            if len(ex5)<2: ex5.append((cs,sets))
print("n=4:",t4,"configs, failures",f4)
print("n=5:",t5,"configs, failures",f5)
for cs in ex4: print("EX4",[(str(x),str(y)) for x,y in cs])
for cs,sets in ex5:
    print("EX5",[(str(x),str(y)) for x,y in cs]); print("   sets",sets)
