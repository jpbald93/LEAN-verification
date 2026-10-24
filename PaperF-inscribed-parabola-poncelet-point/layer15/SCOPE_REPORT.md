# Layer 15 (part 2) — SCOPE CHECK: do the Lean hypotheses exclude cases where the classical theorem still holds?

Scripts and raw outputs: `layer15/scope/` (`geom.py` shared helpers; `scopeA.py`, `scopeA2.py`, `scopeA3.py`, `scopeA4.py`
for Part A; `scopeB.py` for Part B; `*.out` are the captured outputs). 60 digits (mpmath) plus exact rationals (sympy) for the
dual-conic ranks. Read-only on the Lean and the paper. No Lean was run. Nothing was spawned.

**Method.** The Lean formulas for `M`, `P`, `ortho`, `circ` and `meet` were NOT used as the oracle where they could be junk.
- `M` is the second intersection of two circumcircles.
- The orthocentres are `H_k`.
- The directrix is the line through the two farthest-apart genuine orthocentres.
- Tangency is the discriminant of `|z-M|² − dist(z,ℓ)²` on each line.
- The Poncelet point is cross-checked against the centre of the rectangular hyperbola through the four points, computed from 5×5 minors of the conic system.
- The parabola case is also checked exactly: the dual conic through the four lines and ℓ∞ has rank 3 iff it is a genuine parabola.
- Where a Lean-literal evaluation (Lean's `x/0=0` junk) differs from the classical one, both are reported.

Residuals ≲ 1e-58 mean "holds". Residuals of order 1 mean "fails".

## 0. Exact hypothesis lists (read from the Lean)

| Lean theorem | hypotheses (exactly) |
|---|---|
| Part A: `reflPt_mem_orthoLine`, `reflections_collinear`, `miquel_not_mem_orthoLine`, `parabola_tangent`, `tanPt_all` (`tanPt_onParabola`, `tanPt_unique`), `vertex_onParabola`, `dist_vertex`, `vertex_closest`, `newton_perp_orthoLine`, `lambert`, `miquel` | `GenPos L₁..L₄` only: `d₁..d₄ ≠ 0` (4); `cr dᵢ dⱼ ≠ 0` for the 6 pairs; `A₁₂∉L₃`, `A₁₂∉L₄`, `A₁₃∉L₄`, `A₂₃∉L₄` (the 4 triples, each once) |
| `tanPt_mem`, `vertex_mem_axis`, `axis_perp` | none |
| Part B: `poncelet_on_ninepoint` / `ninepoint_concur` / `ninepoint_unique` | `QGen` (4 `cr ≠ 0`), `d ≠ ortho a b c` |
| `ponDen_eq_zero_iff`, `orthocentric_npc_eq`, `orthocentric_ninePointCircle_eq` | `QGen` (and `d = ortho a b c` for the last two) |
| `poncelet_on_pedal_{a,b,c,d}`, `poncelet_on_pedal_c'` | `QGen`, `d ≠ ortho a b c`, `¬Cospherical {a,b,c,d}` |
| `poncelet_on_diagonal_circle` | `QGen`, `d ≠ ortho a b c`, `¬ line[a,b] ∥ line[c,d]`, `¬ line[a,c] ∥ line[b,d]`, `¬ line[a,d] ∥ line[b,c]` |
| `poncelet_S4`, `poncelet_swap_cd` | `QGen`, `d ≠ ortho a b c` |
| `poncelet_swap`, `poncelet_cyc` | none |

## 1. Part A — GenPos

### A1. Exactly two lines parallel (L3∥L4; also checked in the Lean-literal ablation for all six pairs)

Independent construction (`scopeA.out`). Only T3 and T4 exist as triangles, because T1 and T2 contain A34 at infinity.

| classical statement | status | evidence |
|---|---|---|
| C1 Miquel (circles of the two genuine triangles) | survives, but only two circles | M on both: ≤ 1.2e-61 |
| C2 Steiner (4 orthocentres collinear) | **meaningless** | only H3, H4 exist; two points are trivially collinear |
| C3 reflections of M collinear, on line H3H4 | **survives** | R_k collinear 4e-62…3e-61; R_k on line H3H4 5e-61 |
| C4 parabola with focus M, directrix = orthocentre line, M ∉ directrix | **FAILS** | `dist(M, H3H4)` = 4.8e-61, 1.5e-62, 4.1e-61 (M lies ON the line). Tangent quadratic for L3, L4 has leading coefficient 0 (they are parallel to the axis), so "exactly one common point" is not a proper tangency. |
| exact dual conic through L1..L4 and ℓ∞ | degenerate | L3∥L4 gives rank **2** (pair of points) versus rank 3 generically. Exact C* = [[1,−1/2,−1],[−1/2,0,1],[−1,1,0]]. |

Limit (`scopeA.out` A5, L4 rotated by ε from L3): `dist(M, Hline)·|A34|` → 4.713 (constant, ε = 1e-6 and 1e-8). So M → directrix like 1/|A34|, and the focus falls onto the directrix. The inscribed parabola degenerates; there is no limiting parabola statement.

Lean-literal ablation (`scopeA4.out`): the result depends on the labelling (L3∥L4, L1∥L4 and L2∥L4 keep "R collinear / R ∈ span H / Newton ⟂", while L1∥L2, L1∥L3 and L2∥L3 break them). That is an artefact of `meet` returning `L.p` for parallel lines (`x/0 = 0`). In all six cases `dist(M, span H) > 0` fails for at least one of the 5 samples (min over samples ≈ 0 or ≤ 1e-120, i.e. M on the span), and "min |lead| > 0" for the tangent quadratic fails in five of six (L1∥L2 keeps 1.1e-3 but its discriminant is ≈ 3). So no conclusion of the Lean theorem set survives uniformly.

### A2. Three lines concurrent (L1, L2, L3 through O)

Independent construction (`scopeA.out` A2, `scopeA2.out`): T4 collapses to the point O.
- The three remaining circumcircles share only O (second intersections coincide with other vertices, ≤ 3e-60). M is then not a second point; the only candidate is M = O.
- H1, H2, H3 are collinear (4e-61), and O lies on that line (6e-58, 2e-62, 4e-63, 4e-60), and R4 = refl(O, L4) is on it too (6e-58 …). So the Steiner-type statement survives, but M = O lies on the directrix (**C4 fails**).
- Exact dual conic: rank **2**, C* = [[0,0,−2],[0,0,1],[−2,1,0]]. The inscribed "parabola" is degenerate.
- The tangent discriminants at M computed from two circles are ~0.2–1.0 (the Miquel point defined from two circles is wrong for the third).

### A3. Perpendicular cases (H3 = H4, and also H1 = H2 at the same time): **confirmed covered**

- L1⊥L2: |H3−H4| = 5e-61 (H3 = H4 = A12 exactly). Circles through M ≤ 3.8e-59; R collinear 1.4e-60; R on H-line 3e-62; tangent discriminants ≤ 4.2e-60; `M_to_line` 1.9e-5 and 0.06 (M off the line, as the theorem says).
- L1⊥L2 and L3⊥L4: H3 = H4 = A12 (3e-61), H1 = H2 = A34 (3e-60), M_to_line 1.39 and 1.76. All residuals ≤ 1e-59. The directrix is still the line through the distinct orthocentres. The paper's remark at lines 239–240 and the `W ≠ 0` device are correct.

### A4. Classification (Part A)

| theorem | hypothesis | class | evidence | disclosed? |
|---|---|---|---|---|
| all of Part A | `d₁..d₄ ≠ 0` | C (a line has a direction) | meaningless otherwise | line 189 ("directions nonzero") |
| all of Part A | `cr dᵢ dⱼ ≠ 0`, 6 pairs (no two parallel) | **C and N** | classical Setting A assumes it. Dropping it: A1 (C2 meaningless, C4 false, dual conic rank 2, M → directrix). Not X: no uncovered classical statement for the parabola. A weaker X survives for C3 only (R_k collinear on the line of the two existing orthocentres, and M∈C1 two circles), but that is not the paper's theorem. | lines 72, 189 ("no two parallel") |
| all of Part A | the four "not concurrent" conditions | **C and N** | A2: Miquel fails (circles share only O), M = O lies on the directrix, rank-2 dual conic | line 72, 189 |
| Part A | the perpendicularity case H3 = H4 is NOT excluded | confirmed no excess | A3 | lines 239–240 |
| `tanPt_mem`, `vertex_mem_axis`, `axis_perp` | none | n/a | true by construction | lines 303, 314 |

Net for Part A: **no X found**. GenPos is as strong as the classical statement. The only surviving fragment (C3 for parallel or concurrent lines, with M falling ON the line) is a degenerate remainder, not a classical theorem of the same shape.

### A5. Uniqueness (C4 "classically unique")
Not an issue of scope but of content: uniqueness of the inscribed parabola is not formalised. Disclosed at lines 55 and 646–647 (Limitations). Not re-examined here. Exact check: the dual conic through the four lines and ℓ∞ has nullity 1 in the generic and both degenerate cases (A4 in `scopeA.out`), consistent with uniqueness classically.

## 2. Part B — QGen and per-theorem hypotheses

Baselines (`scopeB.out` B0): generic, convex and interior-point quadrangles all give P = hyperbola centre ≤ 2.3e-60, nine-point ≤ 5.6e-61, pedal ≤ 3.1e-61, diagonal ≤ 1.7e-61. **Convex versus one point inside the triangle of the others: no difference** (sanity passed; QGen does not care).

### B1. Orthocentric quadrangles (d = ortho a b c)

The Lean P is junk (`x/0 = 0`, so P = d + 0, with |ponDen| ~ 1e-59). Its residuals against nine-point, pedal and diagonal are 0.004, 0.64 and 1.36, so the Lean theorems would FAIL without `ho`. Hence `ho` is necessary FOR THE LEAN FORMULA.

But the classical content survives in the pencil form (3 configurations, 8 pencil members each; all members rectangular, |A+C| ≤ 9.7e-61):
- Centres of all rectangular hyperbolas through the four points lie on the common nine-point circle (≤ 8.8e-61). This is the paper's Theorem `thm:ortho` (disclosed).
- Each of the 4 pedal circles equals the common nine-point circle (centre difference ≤ 2.5e-60, radius difference ≤ 1.6e-60). Every pencil centre is on each pedal circle (≤ 4e-60).
- The circumcircle of the diagonal triangle also equals the common nine-point circle (centre difference ≤ 8.1e-61), and every pencil centre lies on it (≤ 9e-61).

So in the orthocentric case the pedal statement ("the centre lies on the pedal circles") and the diagonal-circle statement are TRUE classically, with "the Poncelet point" replaced by "every centre of the pencil". The Lean theorems exclude it through the formula and do not state it.

### B2. Concyclic quadrangles
- Nine-point and diagonal circle (the Lean theorems do NOT assume non-concyclicity): residuals ≤ 2.9e-60 and ≤ 8.8e-61 in all three concyclic tests, and P = hyperbola centre ≤ 8e-59. **The Lean needs non-concyclicity nowhere it is classically unneeded.** The pedal theorem alone carries `¬Cospherical`.
- Pedal: all 4 feet triples are collinear (1e-60…2e-61), so the pedal circle does not exist (N for the circle statement; C, since classical D3 states it).
- Surviving limiting statement (not formalised): P lies on the Simson line of each of the four vertices (≤ 1.7e-60, 12 of 12 checks). P is not on the circumcircle (|P−O|/R = 1.05…1.25).

### B3. Opposite sides parallel (AB∥CD)
- Lean-literal diagonal theorem: the point AB∩CD does not exist (`diagPt` is junk), so the hypothesis is N for the statement as written.
- The limiting statement SURVIVES (3 configurations): the "circle through the diagonal triangle" tends to a line, and **P lies on the line through the two finite diagonal points ac∩bd and ad∩bc** (residual relative to |D2−D3|: 5.2e-62, 5.9e-62, 6.0e-62). P is exact on that line, not just in the limit.
- Approach check: with CD rotated by ε = 1e-2, 1e-4, 1e-8 the circle radius is 6.9e+1, 6.9e+3, 6.9e+7 (grows like 1/ε), and the residual of P to the circle stays ≤ 1.4e-58, 2.5e-54, 2.4e-47. These are the same size as the 60-digit working error amplified by the radius, so the circle theorem keeps holding as the circle becomes the line.
- Both pairs parallel (parallelogram): P = centre of the parallelogram (|P − centre| = 0, nine-point 9e-62). The diagonal "triangle" has two vertices at infinity and is not a triangle.

So the Lean hypotheses `p1,p2,p3` exclude a case where a **projective limiting statement** ("P is on the line through the other two diagonal points") holds. This is X for a reformulated statement. The classical Setting B (D4) does not assume "no parallel opposite sides" explicitly; it is implicit in "intersection points of opposite sides".

### B4. Collinear triples (QGen fields)
- With a, b, c collinear: P = foot of d on line abc (1.7e-61, 3.7e-61, 1.5e-60) and P still lies on the nine-point circles of the three genuine triangles abd, acd, bcd (≤ 2.4e-60). Only three triangles exist, so "the four nine-point circles" is meaningless. Classical D1 assumes no three collinear (C). The four-circle statement is N; a weaker three-circle statement survives.
- QGen fields: all four are used (they give the four `ncol_*` for the four Mathlib `ninePointCircle` triangles and the `Frame`). They are not independent redundancies of the Lean formula; dropping any one removes a nondegenerate triangle.

### B5. Classification (Part B)

| theorem | hypothesis | class | evidence (configuration, residual) | disclosed in paper? (line) |
|---|---|---|---|---|
| ninepoint_concur / unique / S4 / swap_cd | QGen: `cr(b−a,c−a) ≠ 0` etc. (4) | C (and N for the 4-circle statement) | B4: collinear abc gives only 3 triangles; P = foot of d | line 56 ("no three collinear"); 205 |
| ninepoint_concur / unique | `d ≠ ortho a b c` | N for the Lean formula, **X for the classical pencil statement** | B1: the Lean P junk has residual 0.004 to 1.36. Classical statement holds for all pencil centres (≤ 8.8e-61). | partly: lines 368–375 (`thm:ortho`) and 398 ("cannot be dropped") disclose the nine-point side; the paper does not say that the pedal and diagonal statements also hold for the whole pencil in the orthocentric case |
| pedal_{a,b,c,d} | `d ≠ ortho a b c` | N for the Lean formula, **X (pencil reading)** | B1: pedal circle = common nine-point circle (≤ 2.5e-60); all pencil centres on it (≤ 4e-60) | no |
| pedal_{a,b,c,d} | `¬Cospherical {a,b,c,d}` | **C** (classical D3 assumes it) and N (feet collinear) | B2: 12 of 12 feet triples collinear ≤ 2e-60; P on Simson lines ≤ 1.7e-60 | yes, lines 407–416 and 656–657; the Simson-line statement is called not formalised |
| diagonal_circle | `d ≠ ortho a b c` | N for the Lean formula, **X (pencil reading)** | B1: diagonal circle = common nine-point circle (centre difference ≤ 8.1e-61); all pencil centres on it (≤ 9e-61) | no |
| diagonal_circle | `¬ line[a,b] ∥ line[c,d]` and the other two | **N** for the literal statement, **X for the projective limit** | B3: P on the line through the two finite diagonal points ≤ 6.0e-62; circle → line with bounded residual as ε → 0 | the hypothesis is stated and explained (lines 425–431) but not that the limit statement holds |
| diagonal_circle | none of the pairs parallel is NOT needed for the nine-point statement | confirms no excess there | B3: nine-point ≤ 2.9e-61 | n/a |
| ninepoint_concur / diagonal | non-concyclicity NOT assumed | no excess | B2: residuals ≤ 2.9e-60 | line 416 ("P itself is defined for concyclic quadrangles") |
| all | convexity / interior point: not assumed | no excess | B0: identical residuals | n/a |

## 3. Cross-check with the ablation reports

`reports/john_quadparabola_ext.md` and `john_quadrangle_ext.md`: 17 UNUSED binders each, in `circC_T4`, `circC_T3`, `circC_scaled`, `simF2`, `simF3`, `simF4` only. All are auxiliary frame lemmas inherited from the shared development. NONE is a field of `GenPos` or `QGen`, nor a hypothesis of any main theorem listed in section 0. 251 and 378 binders are NEEDED. So there is no Lean-internal excess: no main-theorem hypothesis is stronger than what the Lean proof uses. Caveat: the ablation checks a binder is used by the proof, not that the fields of `GenPos` are individually necessary for the statement. Section 1 does the latter numerically (a field-by-field Lean-literal run in `scopeA4.out` covers all 10 independent GenPos fields: parallel pairs and concurrency triples).

## 4. Summary of X findings

| id | what is excluded by the Lean but classically true | status |
|---|---|---|
| X1 | pedal theorem in the orthocentric case, as "every centre of the pencil lies on the (common) pedal circle" | not disclosed |
| X2 | diagonal-circle theorem in the orthocentric case, as "every centre of the pencil lies on the diagonal circle (= nine-point circle)" | not disclosed |
| X3 | diagonal theorem with one pair of opposite sides parallel: P lies on the line through the two finite diagonal points (projective reading of "circle") | hypothesis disclosed, the limit statement is not |
| X4 | (weak) nine-point statement with a collinear triple: P on the three genuine nine-point circles | not disclosed; mostly a degenerate remainder, no recommendation beyond one sentence |
| none | Part A: GenPos (parallel, concurrent) | no X: the parabola degenerates (dual conic rank 2, M on the directrix) |

## 5. Recommended paper changes (one per X)

1. **X1/X2.** In Section 3's discussion of Theorem `thm:ortho` (after line 375), add a remark: "In the orthocentric case the four pedal circles and the circumcircle of the diagonal triangle also coincide with the common nine-point circle (checked numerically: centres and radii agree to 1e-60), so the pedal and diagonal statements hold for every centre of the pencil of rectangular hyperbolas; Theorems `thm:pedal` and `thm:diag` do not state this, because the Lean formula for P is not meaningful there." Add to Limitations (after line 659) a bullet "Orthocentric quadrangles: the pedal and diagonal-circle statements are not formalised."
2. **X3.** After line 431 add: "If exactly one pair of opposite sides is parallel, the diagonal triangle has a vertex at infinity and its circumcircle becomes the line through the other two diagonal points; numerically P lies on that line (residual 1e-61). This limiting statement is not formalised, and `thm:diag` does not cover it." Also add to Limitations. Do not call the three non-parallelism hypotheses merely "what makes the diagonal points exist": they also exclude a true projective statement.
3. **X4.** Optional one sentence at line 205 or in Limitations: with exactly one collinear triple only three triangles exist; P (the formula) is then the foot of the fourth point and lies on the three genuine nine-point circles. Not formalised, not claimed.
4. **Part A, no X.** Add one sentence after line 72 or 191 stating why the hypotheses cannot be weakened: with two parallel lines or three concurrent lines the dual conic through the four lines and the line at infinity has rank 2, the focus M falls on the directrix, and there is no inscribed parabola of the described kind (exact check). This answers the likely reviewer question and costs nothing.
5. **Abstract (lines 55–62) and the caption of Table 1 (lines 124–127).** Both say "that are not an orthocentric system" and "plus the hypothesis named there". This is accurate. Suggested wording for the caption: "The hypotheses are those of the classical statements, except that the pedal and diagonal theorems are stated only outside the orthocentric case, and the diagonal theorem only without parallel opposite sides, whereas classically versions of both survive there (Section 3)."

## 6. Verdict

- Part A: **GenPos is exactly classical** (C). No case outside GenPos where the inscribed-parabola statement survives. The H3 = H4 case is confirmed inside GenPos.
- Part B: the hypotheses `QGen` and `¬Cospherical` for the pedal theorem are classical (C). The hypotheses `d ≠ ortho` (for pedal and diagonal) and the three non-parallelism conditions are **narrower than the classical statements in a reformulated sense** (X1–X3). The Lean theorems are correct as stated. The paper discloses the necessity for the nine-point statement and the non-parallel hypotheses, but not the surviving pencil and limiting statements.
- No Lean hypothesis is stronger than the Lean's own formula needs (17 unused binders are inherited auxiliaries).
- Limits of this check: numerics only. "Survives" is shown to 60 digits on 3 to 5 configurations per case, not proved. The A1/A2 conclusions rely on the dual-conic rank (exact) and on the numerics. The Lean-literal per-field ablation is labelling-dependent because of `x/0 = 0` and is not used as evidence for classical claims.
