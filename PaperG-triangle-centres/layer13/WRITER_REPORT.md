# WRITER REPORT — Layer 13 blind writer (paper G)

Output: `./Blind.lean` is identical to `the arm64 machine:~/lean/reformalG/PaperGBlind.lean` (md5 5e7f738874f1606fb9c6b1e64199de9d).
Setting: `V` a real inner product space, `P` a metric space that is a normed torsor over `V`, `t : Affine.Triangle ℝ P`, with A,B,C = `t.points 0,1,2`.

## Definitions (Blind…)
BlindSideA/B/C (a=|BC|, b=|CA|, c=|AB|), BlindSemiperimeter, BlindCentroid, BlindNagelPoint (weights (s-a)/s,…),
BlindGergonnePoint (1/(s-a),… normalised), BlindSpiekerCentre (= `t.medial.incenter`), BlindDeLongchampsPoint (H+2(O-H)),
BlindAnticomplementary (`t.map (homothety G (-2))`), BlindSymmedianPoint (a²:b²:c² over a²+b²+c²),
BlindFirstBrocard (1/b²,1/c²,1/a² over 1/a²+1/b²+1/c²), BlindSecondBrocard (1/c²,1/a²,1/b²), BlindArea (½|AB||AC| sin∠BAC),
BlindLemoinePoint : Fin 6 → P (the six exact parametric formulas), BlindPedalFootA/B/C (orthogonal projections onto the side lines),
BlindPedalCentroid.

## Statements
Section NagelLine
- blind_1 → thm:gergonne — Gergonne point ∈ line[A_i, touchpoint ∅ i], for each i
- blind_2 → thm:gergonne — the three incircle cevians have a common point
- blind_3 → thm:nagel — Nagel point ∈ line[A_i, touchpoint {i} i], for each i
- blind_4 → thm:nagel — the three excircle cevians have a common point
- blind_5 → thm:nagel — touchpoint {i} i strictly between the other two vertices (Sbtw)
- blind_6 → thm:nagelline — N − G = −2(I − G) (reconstructed main statement)
- blind_7 → thm:nagelline — I, G, N collinear
- blind_8 → thm:spieker — incentre of medial triangle = midpoint(I, N)
- blind_9 → thm:spieker — Spieker centre, I, N collinear
- blind_10 → thm:delong (i) — O = midpoint(H, L)
- blind_11 → thm:delong (ii) — L, O, H collinear
- blind_12 → thm:delong (iii) — G, O, L collinear
- blind_13 → thm:delong (iv) — L = orthocentre of anticomplementary triangle
- blind_14 → thm:medialnagel — Nagel point of the medial triangle = I (reconstructed)
- blind_15 → thm:isotomic — midpoint(touchpoint ∅ i, touchpoint {i} i) = midpoint of side, all three sides (conjunction)
- blind_16 → thm:anti — N = incentre of anticomplementary triangle
- blind_17 → thm:radical — power of S_p w.r.t. exsphere {i} = w.r.t. exsphere {j}
- blind_18 → thm:radical — common value = ¼(s² + (s-a)(s-b)(s-c)/s) = (s² + r²)/4 (r = `t.inradius`)

Section Brocard
- blind_19 → thm:symmedian — the six angle equalities
- blind_20 → thm:symmedian — K is an affine combination with positive weights
- blind_21 → thm:pedal (i) — pedal centroid of K is K
- blind_22 → thm:pedal (ii) — finrank V = 2, pedal centroid of X = X ⇒ X = K
- blind_23 → thm:brocard — ∠ΩAB = ∠ΩBC = ∠ΩCA
- blind_24 → thm:brocard — ∠Ω'BA = ∠Ω'CB = ∠Ω'AC
- blind_25 → thm:cot — cot ω = Σ cot of vertex angles = (a²+b²+c²)/(4Δ)
- blind_26 → thm:cot — 0 < ω ≤ π/6
- blind_27 → thm:isogonal — three isogonality angle equalities
- blind_28 → thm:isogonal — |OΩ| = |OΩ'|
- blind_29 → thm:brocardcircle — O, K, Ω, Ω' at distance ½|OK| from midpoint(O,K)
- blind_30 → thm:brocardcircle — ⟨O−Ω, K−Ω⟩ = 0 and ⟨O−Ω', K−Ω'⟩ = 0
- blind_31 → thm:brocardcircle — ∠OΩK = ∠OΩ'K = π/2
- blind_32 → thm:degenerate — (Ω=O ∨ Ω=K ∨ Ω'=O ∨ Ω'=K ∨ K=O) ↔ t.Equilateral
- blind_33 → thm:degenerate — equilateral ⇒ Ω = Ω' = K = O
- blind_34 → thm:lemoine — six Lemoine points equidistant from midpoint(O,K)
- blind_35 → thm:lemoine — Lemoine points cospherical
- blind_36 → thm:droz — Droz-Farny (finrank V = 2, ⟨d₁,d₂⟩=0, six non-direction hyps, X_k,Y_k on side k and on line through H with direction d₁/d₂ ⇒ midpoints collinear)

## AMBIGUOUS choices
1. Spieker centre definition is redacted: taken as `t.medial.incenter` (Theorem thm:spieker's own wording). Other reading: barycentric (b+c):(c+a):(a+b).
2. thm:nagelline main statement redacted: reconstructed as N − G = −2(I − G). Other reading: e.g. |GN| = 2|GI| or some other relation; the collinearity part (blind_7) is unaffected.
3. thm:medialnagel statement fully redacted: reconstructed as "Nagel point of medial triangle = I". Other reading: unknown; the paper's remark that the statement "is written [NAME] because [NAME] returns a …" suggests a coercion/type subtlety that may change its form.
4. Pedal feet definition redacted: orthogonal projections onto side lines BC, CA, AB (`EuclideanGeometry.orthogonalProjection line[…]`). Other reading: Mathlib face-projection API (should coincide).
5. thm:brocardcircle centre redacted: taken as midpoint of OK (circle with diameter OK, per abstract).
(Minor: in blind_22 "dim V = 2" is `Module.finrank ℝ V = 2`; Droz-Farny lines through H are `AffineSubspace.mk' H (ℝ ∙ d)`, following the visible fragment "orthocenter (ℝ ∙ dᵢ)".)

## Compiler output summary
`lake env lean PaperGBlind.lean`: 36 `declaration uses 'sorry'` warnings, 0 errors, no other messages.
(Two earlier iterations fixed inner-product notation: `open scoped RealInnerProductSpace` and `⟪·,·⟫`.)

## Files read
- ./paperg_blind.txt (the only input read)
- My own files: ./Blind.lean and a scratch ./Probe.lean (written by me to #check Mathlib API names, compiled on the arm64 machine as PaperGBlind.lean, since deleted)
- Compiler output from the arm64 machine (and my local copy of it, ./out.txt)
No other files, no web, no Lean repository.
