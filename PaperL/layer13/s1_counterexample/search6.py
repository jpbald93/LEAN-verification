import sys, random
sys.path.insert(0,'AFM/PaperL/layer13/s1_counterexample')
from search import *
from search5 import common_points, fits_circle, coll3, odd_level_ok
from itertools import combinations, product

# ---- sanity: the model must reproduce Morley/Clifford (4 circles concur) on genpos configs
random.seed(11)
ok_cnt=bad_cnt=0
for _ in range(3000):
    cs=[(F(random.randint(-40,40),10),F(random.randint(-40,40),10)) for _ in range(4)]
    if (0,0) in cs: continue
    if not genpos(cs): continue
    p=common_points(cs)
    if p: ok_cnt+=1
    else: bad_cnt+=1
print("sanity n=4 (genpos): concur",ok_cnt,"no-concur",bad_cnt)

# ---- known degenerate witness from BRIDGE_NOTES, extended
import math
W=[(1.0,1.0),(2.0,0.0),(1.5,math.sqrt(3)/2)]
print("second pts of witness:",[second((F(int(a)),F(0)),(F(int(b)),F(0))) if False else None for a,b in [(0,0)]])
def as_frac(c): return (F(c[0]).limit_denominator(10**6), F(c[1]).limit_denominator(10**6))

# ---- wide random search, n=4 and n=5
fails=[]
t4=t5=0
for _ in range(6000):
    cs=[]
    while len(cs)<5:
        c=(F(random.randint(-60,60),4),F(random.randint(-60,60),4))
        if c==(0,0) or c in cs: continue
        cs.append(c)
    quad=cs[:4]
    if genpos(quad):
        t4+=1
        if not common_points(quad): fails.append(("n4",quad))
    if genpos(cs):
        t5+=1
        ok,sets=odd_level_ok(cs)
        if not ok: fails.append(("n5",cs))
print("random wide: n=4",t4,"n=5",t5,"failures",len(fails))
for f in fails[:3]: print(f)
