import sys
sys.path.insert(0,'AFM/PaperL/layer13/s1_counterexample')
from search import *
from itertools import combinations

grid=[(a,b) for a in range(-2,3) for b in range(-2,3) if (a,b)!=(0,0)]
print("grid",len(grid))
cnt=0; kinds_hist={}; fails=[]
for cs in combinations(grid,4):
    cs=[(F(x),F(y)) for x,y in cs]
    if not genpos(cs): continue
    cnt+=1
    objs=[level3(cs,drop=i) for i in range(4)]
    kinds="".join('L' if o.kind=='line' else 'C' for o in objs)
    kinds_hist[kinds]=kinds_hist.get(kinds,0)+1
    p=level4_point(cs)
    if p is None: fails.append((cs,kinds))
print("genpos 4-tuples:",cnt)
print("kind patterns:",kinds_hist)
print("failures:",len(fails))
for f in fails[:5]: print(f)
