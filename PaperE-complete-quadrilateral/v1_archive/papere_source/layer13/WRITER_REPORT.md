# Writer report (Layer 13, blind)

## Statements (all in Blind.lean, namespace `Blind`)
| name | paper label | gloss |
|---|---|---|
| blind_1 | thm:newton (part 1) | midpoints of the three diagonals are `Collinear ℝ` |
| blind_2 | thm:newton (part 2) | midpoints of A12A34 and A13A24 are distinct |
| blind_3 | thm:ortho (part 1) | H1..H4 collinear |
| blind_4 | thm:ortho (part 2) | H3 ≠ H4 ∨ H2 ≠ H4 |
| blind_5 | thm:boden | every H_k has equal `BlindPw` w.r.t. the three diagonal circles |
| blind_6 | thm:perp | for any H,H' among the orthocentres, Re((m2-m1)·conj(H'-H)) = 0 |
| blind_7 | thm:miquel | M lies on the circumcircle of each T1..T4 |
| blind_8 | thm:steiner | circ(T1..T4) and M are `EuclideanGeometry.Cospherical` |
| blind_9 | thm:simson | feet from M to L1..L4 collinear |
| blind_10 | thm:par | line[ℝ,F1,F2] `Parallel` affineSpan of {H1..H4} |

Defs (from prose, formulas exact): BlindCr, BlindLine (+carrier), BlindMeet, BlindGenPos, BlindCirc, BlindOrtho (a+b+c-2·circ), BlindFoot, BlindPw, BlindA12..A34, BlindT1..T4, BlindH1..H4, BlindM1..M3 (diagonal midpoints), BlindMiquel (explicit formula), BlindCircumcircle.

## AMBIGUOUS choices
- BlindGenPos "meet(L_i,L_j) ∉ L_k for the four triples": used pairs (1,2)∉L3, (1,2)∉L4, (1,3)∉L4, (2,3)∉L4 (the pair choice within a triple is immaterial given non-parallelism). Non-parallel stated as cr(d_i,d_j) ≠ 0 for all six pairs.
- Circumcircle: `Metric.sphere (circ T) (dist T.1 (circ T))` (radius from the first vertex); alternative: require equal distance to all three vertices (equivalent when circ is well-defined, which GenPos guarantees).
- Carrier/meet: cr is real-valued, coerced to ℂ in meet/foot formulas.
- thm:boden: "same power w.r.t. the three circles" stated as pw w.r.t. diagonal 1 = diagonal 2 = diagonal 3 for each H_k (not that powers agree across different k).
- thm:perp: "any two orthocentres" quantified over H,H' ∈ {H1..H4} (may be equal; paper notes this holds trivially).
- thm:par: "parallel" = `AffineSubspace.Parallel` between `line[ℝ,F1,F2]` and `affineSpan` of the set of orthocentres; the nondegeneracy facts (F1≠F2, H not all equal) are not hypotheses.
- Triangles are triples of ℂ; circ/ortho of triangle use formulas in vertex order given in the paper.
- "Cospherical" taken in Mathlib sense on ℂ (as a real inner product space).

## Compiler output
10 `declaration uses 'sorry'` warnings, 0 errors (first and final compile).

## Files read
Only ./papere_blind.txt (plus my own Blind.lean / WRITER_REPORT.md, and the compiler output of my own file on jack).
