import sys
sys.path.insert(0,'AFM/PaperL/layer13/s1_counterexample')
from search import *
from itertools import combinations, product

def common_set(cs, drop):
    """full set of blind points p with p in every level-3 object of this quadruple."""
    objs=[level3(cs,drop=i) for i in range(4)]
    pts=[]
    if all(o.kind=='line' for o in objs): pts.append('inf')
    for i,j in combinations(range(4),2):
        for p in intersections(objs[i],objs[j]):
            if p!='inf' and all(o.contains_approx(p) for o in objs):
                # dedupe
                if not any(p[0]-q[0]<1e-12 and abs(p[1]-q[1])<1e-12 if isinstance(q,tuple) else False for q in pts):
                    pts.append(p)
    return pts, "".join('L' if o.kind=='line' else 'C' for o in objs), objs

def on_common_circle(points):
    """do the chosen blind points lie on one generalised circle (finite pts on a circle or a line)?"""
    fin=[p for p in points if p!='inf']
    has_inf=('inf' in points)
    if not fin: return True
    if len(fin)==1: return True
    # collinear (a line contains all of them; also contains inf)
    if all(collinear(fin[0],fin[1],q) for q in fin[2:]): return True
    if has_inf: return False          # a line containing inf cannot hold non-collinear finite pts
    if len(fin)==2: return True       # a circle through 2 points
    cc=circumcenter(*fin[:3])
    if cc is None: return False
    r2=(fin[0][0]-cc[0])**2+(fin[0][1]-cc[1])**2
    return all((q[0]-cc[0])**2+(q[1]-cc[1])**2 == r2 for q in fin[3:])

def level5_ok(cs):
    sets=[]
    for drop in range(5):
        sub=[cs[j] for j in range(5) if j!=drop]
        pts,kinds,objs=common_set(sub,None)
        if not pts: return False, ("empty common set",drop)
        sets.append(pts)
    for choice in product(*sets):
        if on_common_circle(list(choice)): return True, ("choice",choice)
    return False, sets

grid=[(F(a),F(b)) for a in range(-2,3) for b in range(-2,3) if (a,b)!=(0,0)]
fails=[]
tested=0
quad_fail=0
for quad in combinations(grid,4):
    quad=list(quad)
    try:
        pts,kinds,_=common_set(quad,None)
    except ValueError:
        continue
    if kinds!='LLLL': continue
    # only the degenerate quadruples
    for extra in grid:
        if extra in quad: continue
        cs=quad+[extra]
        if not genpos(cs): continue
        try:
            ok,why=level5_ok(cs)
        except ValueError:
            continue
        # is the LLLL quadruple's forced point infinity only?
        tested+=1
        if not ok:
            fails.append((cs,pts,why))
            if len(fails)>=5: break
    if len(fails)>=5: break
print("LLLL quads extended & genpos:",tested,"failures:",len(fails))
for cs,pts,why in fails[:5]:
    print("----")
    print("centres:",[(str(x),str(y)) for x,y in cs])
    print("LLLL quad forced common set:",pts)
    print("why fail:",why[0] if isinstance(why,tuple) else why)
