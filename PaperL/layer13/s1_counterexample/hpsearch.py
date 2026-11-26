import sys, random
sys.path.insert(0,'AFM/PaperL/layer13/s1_counterexample')
from fractions import Fraction as F
from verify_hp import check
from search import genpos

random.seed(4242)
t=0; fails=[]
cases=[]
# the 48 low-precision suspects
cases += [[(F(-39,4),F(3)),(F(-5,2),F(11)),(F(13,2),F(-1,2)),(F(13,2),F(-25,2)),(F(15,4),F(1,2))],
          [(F(-11),F(-47,4)),(F(9),F(37,4)),(F(-7),F(-3)),(F(-15,2),F(-53,4)),(F(19,2),F(-7,2))],
          [(F(45,4),F(5)),(F(5),F(-13)),(F(-5),F(4)),(F(57,4),F(-25,2)),(F(45,4),F(23,4))]]
for _ in range(1200):
    cs=set()
    while len(cs)<5:
        c=(F(random.randint(-80,80),4),F(random.randint(-80,80),4))
        if c!=(0,0): cs.add(c)
    cases.append(list(cs))
for cs in cases:
    if not genpos(cs): continue
    t+=1
    ok,sets,kinds,ch=check(cs)
    if not ok: fails.append((cs,kinds))
print("hp-checked genpos 5-tuples:",t,"failures:",len(fails))
for f in fails[:3]: print(f)
