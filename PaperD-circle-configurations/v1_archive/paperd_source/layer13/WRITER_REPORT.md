# WRITER_REPORT (Layer 13, blind writer, paper D)

## Statements (name → paper label → gloss)
- blind_1 → thm:cliff4 → four circles (centres c : Fin 4 → ℂ), hypotheses BlindCliffordHyp; the four Γ_ijk have a common point.
- blind_2 → thm:cliff5 (existential) → ∃ P : Fin 5 → ℂ, P k common point of the four Γ of the other four circles, and the range of P lies on a circle or a line.
- blind_3 → thm:cliff5 (explicit points) → for any P with P k a common point of those four Γ, range P is on a generalized circle.
- blind_4 → thm:cliff6 → six circles; for each 5-subset S the points P_T lie on C_S (circle through the three designated points, assumed non-collinear), and the six C_S have a common point.
- blind_5 → thm:chain (n=4) → BlindCliffordChain 4.
- blind_6 → thm:chain (n=5) → BlindCliffordChain 5.
- blind_7 → thm:five → Miquel pentagram: M_0..M_4 concyclic or collinear.
- blind_8 → thm:lester → circumcentre, nine-point centre, F₁, F₂ concyclic for a scalene triangle.
- blind_9 → thm:thebault → P, Q, incentre collinear.
- blind_10 → thm:kosnita → lines AO_a, BO_b, CO_c concurrent.
- blind_11 → thm:blundon → two-sided inequality for s² (R = circumradius, r = inradius from Mathlib).
- blind_12 → thm:steiner → BE = CF ⇒ AB = AC.

That is 12 statements for the 10 theorems. cliff5 and chain each got 2 parts.

Definitions are all named `Blind...`: BlindP (the prose's formula, exact), BlindOnCircum, BlindOnGamma, BlindCliffordHyp, BlindIsCp, BlindGenCircle (+carrier), BlindOnGenCircle, BlindDesignated, BlindObj, BlindChain, BlindGeneralPosition, BlindCliffordChain, BlindPlane, BlindApex, BlindIsFermat, BlindThebaultCentre.

## AMBIGUOUS choices / judgment calls
1. **cp (blind_2, 3, 4).** The prose says cp is an "explicit point" but gives no formula. I defined cp as *any* common point of the Γ of all triples in the index set (BlindIsCp). blind_3 and blind_4 therefore quantify over every such point, which is stronger than the paper's single explicit point. If the common point is not unique, they may not be equivalent to the paper's claim.
2. **Γ.** The circle through three points is encoded as "∃ centre equidistant from the three points and the test point". I did not use Mathlib's circumsphere, because the three points might be collinear or coincident. The hypotheses exclude that case.
3. **cliff6 designated subsets.** The prose gives only S = {1..5} (the subsets {1,2,3,4}, {1,2,3,5}, {1,2,4,5}) and says "six choices are listed" in redacted text. I generalised this as "drop the three largest elements of S". The statement takes three functions a, b, d with `BlindDesignated S = {a S, b S, d S}`. This guess is probably wrong for the other five S.
4. **cliff6 conclusion.** I read "all five points P^S_T lie on C_S" as all five 4-subsets T ⊂ S.
5. **Chain predicate.**
   - It is defined by recursion on n (level 0, 1, 2 as the prose says).
   - Levels n ≥ 3 use `Fin.succAbove` to delete circle i.
   - Odd levels give a generalized circle, with the radius-0 case allowed.
   - Even levels give a point.
   - Level-1 "the circle itself" is `circle (c 0) ‖c 0‖`.
   - The prose's "pairwise transversal" is read as ¬Collinear {0, c_i, c_j}, taken from the bridge description "M, c, d not collinear".
   - General position is read as: centres of each triple not collinear AND the three P not collinear.
6. **Generalized circle.** A circle with radius ≥ 0 (radius 0 allowed, since the prose says the n=5 proof uses radius 0), or a line. In blind_7, "on one circle or one line" uses Mathlib's `Concyclic ∨ Collinear`.
7. **thm:five.** Indices are `Fin 5`, so arithmetic is mod 5. The collinearity hypothesis reads `A_{i-1}, A_i, T_{i+1}, T_{i-1}` collinear, exactly as written. The concyclic hypothesis is `A_{i-1}, A_i, T_i, M_{i-1}, M_i` concyclic.
8. **Lester.** Fermat point F is "∃ apexes Da, Db, Dc of equilateral triangles erected outward/inward (opposite/same side of the line as the vertex), with F on the three lines". Scalene means all three side lengths pairwise distinct. The nine-point centre is Mathlib's `ninePointCircle.center`. Existence of F₁ and F₂ is assumed, as in the paper.
9. **Thébault.**
   - Tangency to a line is encoded as `infDist = r`.
   - Internal tangency to the circumcircle is encoded as `dist P O = R - r`, which is the prose's definition.
   - The side conditions use `SSameSide`.
   - The incentre is Mathlib's `Simplex.incenter`.
   - The prose's "in the angle ADB" is encoded exactly as the prose's side conditions (same side of AD as B, same side of BC as A).
10. **Kosnita.**
   - "No two of A, B, C diametrically opposite" is encoded as O ≠ midpoint of each side.
   - The alternative reading is ¬Collinear {O,B,C}, etc. These are equivalent on a circle of positive radius.
   - O_a, O_b, O_c are given by equidistance from the three vertices, as the prose says.
   - "Concurrent" means a common point exists (no concurrence at infinity).
11. **Blundon.** Stated for a general real inner-product space using Mathlib's `circumradius` and `inradius`, and s as half the sum of the side distances. The prose writes the sqrt term as `√(R²−2Rr)`, which I kept literally.
12. **Steiner–Lehmus.** "Internal bisector foot" is encoded as E in `affineSegment A C` with ∠ABE = ∠EBC (unoriented angles), and the same for F. Non-degenerate means `AffineIndependent`. The theorem holds in any real inner product space, which I used.

## Compiler output summary
`lake env lean PaperDBlind.lean` on the x86 machine: **12 `declaration uses 'sorry'` warnings, 0 errors**. There are no other warnings. The first compile had 2 errors (an inductive nested through `∃`, and an `AddCommMonoid P` instance). I fixed them by rewriting `BlindChain` as a recursive def and switching to `affineSegment`.

Local `Blind.lean` and `~/reformal/PaperDBlind.lean` are byte-identical (checked with `cmp`).

## Files read
- `./paperd_blind.txt` (the only input).
- I wrote `/tmp/t.lean`, a 5-line probe of `#check` on Mathlib names (incenter, inradius, orthocenter, ninePointCircle). I copied it to `~/reformal/PaperDBlindProbe.lean` on the x86 machine and compiled it there, then deleted the remote copy.
- No other files were read. I did not search the web, spawn subagents, or look at any Lean repository. The only other thing I read on the x86 machine was the compiler output for my own files.
