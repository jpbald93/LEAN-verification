# WRITER_REPORT — Layer 13 blind writer (paper F)

## Statements (name → paper label → gloss)
Part A (`section PartA`):
- blind_1 → thm:refl → each R_k = refl(M,L_k) lies in the orthocentre line `line[ℝ,H4,H4+W]`
- blind_2 → thm:refl → {R1..R4} collinear
- blind_3 → thm:refl → cr(H_i−H4, R_k−H4)=0 for i=1,2,3, all k
- blind_4 → thm:off → cr(W, M−H4) ≠ 0
- blind_5 → thm:tangent → Tangent L M (orthocentre line) for each of the four lines (∃! point on L equidistant)
- blind_6 → thm:tanpt → tanPt L on L, on the parabola, and unique such point (for each L)
- blind_7 → thm:vertex → V on parabola; dist V M = ½ infDist M dir; V minimises infDist to directrix over the parabola
- blind_8 → thm:vertex → V on axis; Re(conj(iW)·W)=0
- blind_9 → thm:newton → ∀ x y on orthocentre line, ⟨x−y,N2−N1⟩=0 ∧ ⟨x−y,N3−N1⟩=0 (second conjunct, see AMBIGUOUS)
- blind_10 → thm:newton → ⟨W,N2−N1⟩=⟨W,N3−N1⟩=0
- blind_11 → thm:lambert → four tangencies ∧ M on circumcircle of each T_k
Part B (`section PartB`):
- blind_12 → thm:ortho → QGen ⇒ (ponDen=0 ↔ d = ortho a b c)
- blind_13 → thm:ortho → if d = ortho a b c: four nine-point centres equal and four nine-point circles equal
- blind_14 → thm:ortho → numerical example (0, 4, 1+2i, 1+3/2 i): QGen, d=ortho, ponDen=0
- blind_15 → thm:nine → P on nine-point circle of all four triangles
- blind_16 → thm:unique → point on circles of (abc),(abd),(acd) equals P
- blind_17..20 → thm:pedal → cases v=d, c, b, a (the prose's side lists): feet + P cospherical
- blind_21 → thm:diag → three diagonal points + P cospherical (non-parallel opposite sides)
- blind_22 → thm:s4 → poncelet invariant under the six listed permutations (one conjunction)
- blind_23 → thm:s4 → d = ortho(a,b,c) ↔ c = ortho(a,b,d)

Definitions: BlindCr, BlindLine (+carrier), BlindMeet, BlindCirc, BlindOrtho, BlindFoot, BlindRefl,
BlindLineThrough, BlindMid, BlindOnCircumcircle, BlindOnParabola, BlindTangent, BlindGenPos,
BlindQuadrilateral (A_ij, T_k, H_k, M, F_k, W, R_k, OrthoLine, Directrix, contact, tanPt, Axis, V, N_i),
BlindQGen, BlindPonDen, BlindPonNum, BlindPoncelet, BlindNinePt, BlindNineCircle, BlindDiagPt.

## AMBIGUOUS / chosen readings (also marked in the file where relevant)
1. **Explicit formulas not in the prose**: meet, circ and the Miquel point are "explicit formulas" the prose does not give. I used the standard formulas: meet(L,M)=p+(cr(e,q−p)/cr(e,d))·d for M=(q,e); circ(a,b,c)=a−i(|u|²v−|v|²u)/(2cr(u,v)), u=b−a, v=c−a (checked: reproduces the paper's example d=ortho(0,4,1+2i)=1+3/2 i). Miquel point = reflection of A12 in the line through circumcentres of T3 and T4 (second intersection of those circumcircles). Any of these may differ from the paper's formulas in form (not in value).
2. **Truncated theorem thm:newton**: sentence "⟨x−y,N2−N1⟩=0 and …" is cut off in the text. I guessed the missing conjunct ⟨x−y,N3−N1⟩=0 (blind_9). Other reading: only the N2−N1 conjunct.
3. **Triangles T_k**: vertex ordering for T_k is arbitrary (does not matter for orthocentre/circumcircle).
4. **Nine-point circle**: defined as the sphere around ninePt through the midpoint of side ab (the prose gives only the centre).
5. **Circumcircle membership** (thm:lambert): defined as distance to circ(T) equal to distance of a vertex to circ(T).
6. **Tangent L f S**: "exactly one point of L equidistant from f and S" = ∃! z ∈ carrier L, OnParabola f S z, with S the Mathlib `AffineSubspace` `line[ℝ,H4,H4+W]`.
7. **Orthocentre line** taken as `line[ℝ,H4,H4+W]` (as the prose states under GenPos); the hypothesis in each Part A statement is GenPos only. W is *not* separately assumed ≠ 0 (prose says it follows).
8. **Inner product** in thm:newton: Mathlib's real inner product on ℂ (`inner ℝ`), which is Re(conj x · y).
9. **Cospherical** in the pedal/diagonal theorems is `EuclideanGeometry.Cospherical` on ℂ (as a set of 4 points). Degenerate repeated points collapse the set, as in the prose's informal statement.
10. **Concyclic hypothesis** in thm:pedal: stated as `¬ Cospherical {a,b,c,d}`.
11. **Parallel** in thm:diag: `AffineSubspace.Parallel` of `line[ℝ,_,_]`, negated, exactly as in the prose.
12. thm:s4 stated as a single conjunction of the six equalities (the prose's grouping) + separate orthocentricity symmetry; permutations are given as argument lists exactly as in the prose.
13. thm:vertex: the prose's last two sentences ("vertex on axis, axis ⟂ directrix") are in blind_8; the infDist-to-"directrix" uses the orthocentre line as the paper says.
14. thm:pedal: one statement per vertex v (4 statements); thm:tangent/tanpt/lambert use ∀/conjunction over the four lines.

## Compiler output summary
Type-checked on jack (`lake env lean PaperFBlind.lean`): 23 `declaration uses 'sorry'` warnings, 0 errors.
Local ./Blind.lean and ~/reformal/PaperFBlind.lean are identical (scp'd copy).

## Files read
- ./paperf_blind.txt (only input file)
- Own files written/read back: ./Blind.lean, ./WRITER_REPORT.md; compiler output of PaperFBlind.lean on the x86 machine (stdout only).
No other file read; no web; no Lean repository.
