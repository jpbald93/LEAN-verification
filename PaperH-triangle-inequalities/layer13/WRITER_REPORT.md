# WRITER REPORT — Layer 13 blind writer (paper H)

Output: `./Blind.lean` and `arm64 machine:~/lean/reformalH/PaperHBlind.lean`; they are identical (same SHA-256:
e257c271479a928f78fd921fe07747d30285031439fe2241e8125a20a8f08cbc).

## Conventions
`A,B,C = t.points 0,1,2`; `a=|BC|, b=|CA|, c=|AB|`; O/I/R/r/excenter/exradius/orthocenter come from Mathlib;
G = `Finset.univ.centroid ℝ t.points`.
Definitions written from the prose: `BlindSemiperimeter`, `BlindArea` (½|AB||AC| sin∠BAC, exactly as given),
`BlindHeronGamma` (auxiliary; defined but not used in any statement), `BlindEquilateral` (|AB|=|BC| ∧ |BC|=|CA|),
`BlindInClosedTriangle` / `BlindStrictlyInside` (weights ≥0 / >0, summing to 1, affine combination),
`BlindDistToLine` (dist X (orthogonalProjection line[Y,Z] X)), `BlindOrientationSign` (1 if areaForm(B-A,C-A)>0 else -1),
`BlindOuterApex` (Y rotated about X by −σπ/3), `BlindApexA/B/C` (on BC, CA, AB), `BlindNapoleonA/B/C` (centroids of BCA', CAB', ABC').
The Napoleon section assumes `Fact (finrank ℝ V = 2)` plus an orientation `o`.

## Statements
| name | label | gloss |
|---|---|---|
| blind_1 | thm:euler | IO² = R² − 2Rr |
| blind_2 | thm:eulerineq | 2r ≤ R |
| blind_3 | thm:eulerineq | 2r = R ↔ equilateral |
| blind_4–6 | thm:eulerex | |I_i O|² = R² + 2R r_i for i = 0,1,2 |
| blind_7 | thm:ogh | OG² = R² − (a²+b²+c²)/9 |
| blind_8 | thm:ogh | OH² = 9R² − (a²+b²+c²) |
| blind_9 | thm:ogh | IG² = (s²+5r²−16Rr)/9 |
| blind_10 | thm:quartic | s⁴ − 2(2R²+10Rr−r²)s² + r(4R+r)³ ≤ 0 |
| blind_11 | thm:gerretsen | 16Rr − 5r² ≤ s² |
| blind_12 | thm:gerretsen | s² ≤ 4R²+4Rr+3r² |
| blind_13 | thm:gerretsen | (R−r)(R−2r) ≥ 0 |
| blind_14 | thm:kooi | s² ≤ R(4R+r)²/(2(2R−r)) |
| blind_15 | thm:kooi | R(4R+r)²/(2(2R−r)) ≤ 4R²+4Rr+3r² |
| blind_16, 17 | thm:weitz | 4√3Δ ≤ a²+b²+c²; equality ↔ equilateral |
| blind_18, 19 | thm:hf | Hadwiger–Finsler; equality ↔ equilateral |
| blind_20, 21 | thm:iso | 12√3Δ ≤ (a+b+c)²; equality ↔ equilateral |
| blind_22 | thm:leibniz | ΣXA² = 3XG² + (a²+b²+c²)/3 |
| blind_23 | thm:leibniz | ΣXA² ≥ (a²+b²+c²)/3 |
| blind_24 | thm:leibniz | equality ↔ X = G |
| blind_25 | thm:pedoe | Neuberg–Pedoe inequality (two triangles, possibly in different spaces) |
| blind_26 | thm:pedoe | equality ↔ ∃k>0, a'=ka, b'=kb, c'=kc |
| blind_27 | thm:ptolemy | AC·BD ≤ AB·CD + BC·AD |
| blind_28 | thm:ptolemyeq | for distinct points: equality ↔ (cospherical ∧ diagonals cross) ∨ (collinear in one of 8 orders) |
| blind_29–31 | thm:key | the three paired key-lemma inequalities, X in closed triangle |
| blind_32 | thm:em | 2(d_A+d_B+d_C) ≤ XA+XB+XC, X in closed triangle |
| blind_33 | thm:em | equality ↔ equilateral ∧ X = centroid |
| blind_34 | thm:barrow | Barrow, X strictly inside, U,V',W weakly between, bisector equal-angle hypotheses |
| blind_35 | thm:fermatmin | the three angles at F are 2π/3 ⇒ F minimises XA+XB+XC |
| blind_36 | thm:fermat | all angles < 2π/3 ⇒ ∃F with angles 2π/3 that minimises |
| blind_37–39 | thm:fn (o) | t_i and the opposite apex lie strictly on opposite sides of the opposite side line |
| blind_40, 41 | thm:fn (i) | AA' = BB', BB' = CC' |
| blind_42 | thm:fn (ii) | the lines AA', BB', CC' are concurrent |
| blind_43 | thm:fn (iii) | angles < 2π/3, F on AA' and BB' ⇒ the angles at F are 2π/3 |
| blind_44 | thm:fn (iii) | ... and AA' = FA+FB+FC |
| blind_45–47 | thm:fn (iv) | angle between the vectors A'−A, B'−B (and cyclically) is 2π/3 |
| blind_48, 49 | thm:napoleon | N_AN_B = N_BN_C = N_CN_A |
| blind_50 | thm:napoleon | centroid of N_A, N_B, N_C = G |

That is 50 statements in total.

## Redactions I had to reconstruct (these are interpretive)
- thm:eulerex: the body is redacted. I reconstructed |I_iO|² = R² + 2Rr_i from the proof paragraph.
- thm:ptolemyeq: items (a) and (b) are redacted. I reconstructed them from the abstract and the proof: (a) cospherical with crossing diagonals, (b) collinear in one of eight orders.
- thm:em: the equality clause is mostly redacted (the surviving fragment is "centroid ℝ t.points"). I used: equilateral ∧ X = centroid.
- thm:barrow: the bisector hypothesis is redacted. Limitations item 3 says "betweenness and equal angles", so I used ∠BXU = ∠UXC, and the same for V' and W.
- thm:fn: items (i)–(iv) are mostly redacted. I reconstructed them from the abstract, the remarks after the theorem and the proof paragraph.
- Outer apex: the rotation sentence is truncated. I used a rotation about X by −σπ/3, which is the angle given in the proof paragraph. For a counter-clockwise triangle this puts the apex outside the triangle.

## AMBIGUOUS choices
1. blind_28 (ptolemyeq): item (a) might also require non-collinearity, and "crossing" might use weak rather than strict betweenness. I rendered the "eight orders" as the 4 cyclic rotations of ABCD plus the 4 of DCBA, each written as a chain of two strict-betweenness facts.
2. blind_34 (Barrow): the redacted bisector hypotheses are rendered as unoriented equal angles at X.
3. blind_37–39 (fn (o)): my reading of the truncated "lie strictly on …" is "strictly on opposite sides of the line through the other two vertices" (`AffineSubspace.SOppSide`).
4. blind_45–47 (fn (iv)): I state that the angle between the vectors A'−A and B'−B is 2π/3. The other reading is a direct statement that the unoriented lines meet at angle π/3.
5. blind_43/44 (fn (iii)): the hypothesis is F on the lines AA' and BB', following the remark "holds for any F on the lines AA' and BB'". The other reading is F being the concurrency point of (ii).

## Compiler output
`lake env lean PaperHBlind.lean` on the arm64 machine (arm64) exited with code 0. It produced 50 messages, all `declaration uses 'sorry'` warnings (one per theorem), and 0 errors or other warnings. The file compiled on the first attempt.

## Files read
- `/tmp/blindH13/paperh_blind.txt`. I read it via `cat`; the tool persisted the output to `<session-log>`, and I read that copy, which is the same content.
- Besides that, only my own outputs: `Blind.lean` and the compiler log `out.txt`, which I counted with wc/grep. On arm64 machine I read nothing except the compiler output and a checksum of my own uploaded file.
