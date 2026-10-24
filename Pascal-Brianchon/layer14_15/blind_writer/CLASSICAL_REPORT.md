# CLASSICAL_REPORT — Paper Pascal (classical-source blind writer)

## Files read
- `/tmp/blindPascal/classical_statements.txt` (the only mathematical input).
- I listed the directory `/tmp/blindPascal` with `ls`, which showed a `brief.txt`; I did **not** open it.
- I read my own outputs (`Classical.lean`, this report) and the compiler output from jack. No other files, no web.

## Model
- Points of P²(K): `ℙ K (Fin 3 → K)` (Mathlib `Projectivization`). Lines: submodules of `K^3` of `finrank` 2.
- Conic: `q : QuadraticForm K (Fin 3 → K)`, with points `{p | q p.rep = 0}`.

## OWN DEFINITIONS
| name | meaning |
|---|---|
| `IsLine L` | `finrank K L = 2` |
| `OnLine p L` | `p.submodule ≤ L` |
| `join X Y` | `X.submodule ⊔ Y.submodule` (the line XY when X ≠ Y) |
| `IsMeet P L M` | P lies on both L and M (the intersection point, given by its defining property) |
| `CollinearPts S` | some line contains every point of S |
| `ConcurrentLines L M N` | some point lies on all three lines |
| `OnConic q p` | `q p.rep = 0` |
| `QNondeg q` | for every v ≠ 0 there is an x with q(x+v) ≠ q x. This says q is not equivalent to a form in fewer variables, works in every characteristic, and implies q ≠ 0 |
| `NondegConic q` | `QNondeg q` and the conic has at least one point |
| `IsTangentAt q A L` | L is a line through A that meets C in no other point |
| `IsTangentLine q L` | L is tangent at some point of C |
| `polarLine q p` | `ker (q.polarBilin p.rep)` (the polarity defined by C) |

## Statements (all `:= by sorry`)
- `classical_Setting_noThreeCollinear`: a non-degenerate conic contains no three collinear points (a fact the Setting states).
- `classical_Pascal1_a`: Pascal's theorem. The hypotheses are the six distinct points (`Function.Injective ![A,B,C',D,E,F]`) on a non-degenerate conic, with P, Q, R given by `IsMeet`. Conclusion: `CollinearPts {P,Q,R}`.
- `classical_Pascal2_a`: five-point form, with the tangent t_A given by `IsTangentAt`. Conclusion: the points t_A∩C'D, AB∩DE and BC'∩EA are collinear.
- `classical_Pascal2_b`: Pappus. l ≠ m are lines and O = l∩m. A, C', E are distinct points on l, B, D, F are distinct points on m, and all six differ from O.
- `classical_Pascal3_a`: Braikenridge–Maclaurin. Six distinct points, no three collinear, with collinear Pascal points, lie on some conic q with `NondegConic q`.
- `classical_Brianchon1_a`: Brianchon, assuming `ringChar K ≠ 2`. Six distinct tangent lines; conclusion: `ConcurrentLines (join V1 V4) (join V2 V5) (join V3 V6)`.
- `classical_Brianchon2_a_*` (duality, assuming char ≠ 2), split into five statements:
  - `polarIsLine`: the polar of every point is a line.
  - `tangent`: the tangent at a point A of C is exactly the polar of A.
  - `vertex`: the polar of a∩b is AB, where A, B are the points of contact.
  - `incidence`: three points are collinear iff their polars are concurrent.
  - `diagonal`: the polar of the Pascal point AB∩DE is the diagonal V1V4.
- `classical_Brianchon2_b`: pentagon form. Five distinct tangents a, c, d, e, f; V1 is the point of contact of a (the a=b case) and V2 = a∩c.

## Obligations (well-formedness only)
- `classical_Setting_join_obligation`: XY is a line when X ≠ Y.
- `classical_Pascal1_a_obligation`: each of the three intersection points exists and is unique.
- `classical_Pascal2_a_obligation`: the tangent t_A exists and is unique, and the three intersections exist and are unique.
- `classical_Pascal2_b_obligation`: l∩m exists and is unique.
- `classical_Pascal2_b_obligation'`: the three Pappus intersections exist and are unique.
- `classical_Pascal3_a_obligation`: the three intersections exist and are unique.
- `classical_Brianchon1_a_obligation`: the six vertices exist and are unique, and opposite vertices are distinct, so the diagonals are lines.
- `classical_Brianchon2_b_obligation`: the same for the pentagon form, plus a unique point of contact for a.

## AMBIGUOUS / EXTRA marks
- AMBIGUOUS (`QNondeg`): in char ≠ 2 one could instead use non-degeneracy of `polarBilin q`. I used the source's own wording ("not equivalent to a form in fewer variables"), which works in every characteristic.
- AMBIGUOUS (`IsTangentAt`): the tangent could instead be defined as the polar line. The two agree for a non-degenerate conic in char ≠ 2, and that agreement is stated as `classical_Brianchon2_a_tangent`.
- EXTRA HYPOTHESIS: none. The `ringChar K ≠ 2` in Brianchon2 (a)/(b) is not extra: Brianchon1 assumes it, and Brianchon2 is stated in that context.
- Interpretive choice: intersection points are hypotheses `IsMeet P L M`, not functions. Uniqueness goes into the obligations.

## Compiler summary
Checked on jack with `lake env lean PaperPascalClassical.lean`: 0 errors. The output is exactly 20 `declaration uses 'sorry'` warnings, one per theorem. `/tmp/blindPascal/Classical.lean` is identical to the jack copy (md5 `7b134e215bf93903bd9d45a3890ba9b3`). The only fix needed was marking `polarLine` `noncomputable`.
