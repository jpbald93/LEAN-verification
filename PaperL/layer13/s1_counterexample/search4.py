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

def on_circle_pts(fin):
    if len(fin)<=2: return True
    if all(coll3(fin[0],fin[1],q) for q in fin[2:]): return True
    if len(fin)==2: return True
    # circle through first three (float solve) then test the rest
    (ax,ay),(bx,by),(cx,cy)=fpt(fin[0]),fpt(fin[1]),fpt(fin[2])
    d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    if abs(d)<1e-14: return False
    ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
    uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
    r2=(ax-ux)**2+(ay-uy)**2
    return all(abs((fpt(q)[0]-ux)**2+(fpt(q)[1]-uy)**2-r2)<=1e-6*max(1.0,r2) for q in fin)

def on_common_circle(points):
    fin=[p for p in points if p!='inf']
    return on_circle_pts(fin)

def common_set(cs):
    objs=[level3(cs,drop=i) for i in range(4)]
    pts=[]
    if all(o.kind=='line' for o in objs): pts.append('inf')
    for i,j in combinations(range(4),2):
        for p in intersections(objs[i],objs[j]):
            if p=='inf': continue
            if all(o.contains_approx(p) for o in objs):
                if not any(abs(p[0]-q[0])<1e-7 and abs(p[1]-q[1])<1e-7 for q in pts if q!='inf'):
                    pts.append(p)
    return pts,"".join('L' if o.kind=='line' else 'C' for o in objs)

def level_ok(cs_list, k):
    """does a blind object exist at level k for the k-point configuration cs_list?"""
    sets=[]
    for drop in range(k):
        sub=[cs_list[j] for j in range(k) if j!=drop]
        pts,kinds=common_set(sub)
        if not pts: return False,None
        sets.append(pts)
    for choice in product(*sets):
        if on_common_circle(list(choice)): return True,choice
    return False,sets

grid=[(F(a),F(b)) for a in range(-2,3) for b in range(-2,3) if (a,b)!=(0,0)]
tot4=0;fail4=0; tot5=0; fail5=0; examples=[]
for quad in combinations(grid,4):
    quad=list(quad)
    if not genpos(quad): continue
    tot4+=1
    ok,why=level_ok(quad,4)
    if not ok: fail4+=1
    for extra in grid:
        if extra in quad: continue
        cs=quad+[extra]
        if not genpos(cs): continue
        tot5+=1
        ok,why=level_ok(cs,5)
        if not ok:
            fail5+=1
            if len(examples)<3: examples.append((cs,why))
print("n=4 genpos configs:",tot4,"failures:",fail4)
print("n=5 genpos configs:",tot5,"failures:",fail5)
for cs,why in examples:
    print("----",[tuple(str(x) for x in c) for c in cs])
    for s in why: print("   ",s)
