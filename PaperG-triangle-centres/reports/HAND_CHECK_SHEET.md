# Paper G — hand check sheet (for Josh)

**Completed by the author on 27 October 2026: all rows agree.**

**What to do:** for each theorem, read the paper's theorem (top) and the Lean statement(s) under it. For each Lean statement tick **☐ agrees** if it says the same thing as the paper: same objects, every hypothesis in the paper is in the Lean and the other way round, same conclusion. Tick **☐ differs** and write a note if anything looks different, even slightly. You do not need to read any proofs; they are replaced by `…`. Each Lean statement has a one-line plain-English gloss. The gloss is only there to help you read it: check the Lean itself, not the gloss.

The Lean statements are copied verbatim, by script, from the sources at the published commits: `paperg_nagel` @ `e40ee54f20588f5181d348767f3f31be20406cc1` (files `Basic`, `Main`, `Extensions`, `Inradius`, `L14`, `L15Classical`) and `paperg_brocard` @ `ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d` (files `Basic`, `Lemmas`, `Main`, `Extensions`, `ExtLemmas`, `L14`, `L15Classical`). Both working trees were clean at those commits. The repositories are public; every link below points to the exact line at those commits.

Theorem numbers are the ones printed in the compiled paper (`paperg.pdf`): Theorems 1–18 (definitions are numbered separately). The main-theorem list is Table 1 of the paper. The paper's theorem texts were copied from the PDF with `pdftotext`; display formulas, which `pdftotext` garbles, were re-typed in LaTeX from the PDF.

**Counts:** 18 numbered theorems (Part 1 and Part 2), 67 Lean statements in total (numbered theorems plus ★ Layer-15 rows), 134 tick boxes (two per Lean statement).

## Builder notes (read first)

The builder checked every row: does the Lean statement say what the paper's theorem says, with the same hypotheses and conclusion? **No Lean statement was found to contradict its paper theorem, and every file:line the paper cites is the line of the `theorem` keyword at the commits above** (the cited Main/Extensions/Inradius line numbers all agree). Nothing in the paper or the code was changed. Points found:

1. **The compiled PDF is older than `paperg.tex`** (not a statement mismatch). In Theorem 9 the PDF prints the reference for `inradius_sq` / `spiekerCenter_power_exsphere_eq_inradius` as "(Inradius:1)". The current `paperg.tex` (line 321) says `Inradius:19, line 40`, and a fresh compile of the current tex prints "Inradius:19, line 40", which is correct (19 and 40 are the two theorem lines). The tex was saved 15 s after the PDF. Recompile before the hand check, so that you read the version that will be submitted. Theorem numbering is the same in both builds.
2. **Mojibake in the PDF** (typesetting, not a mismatch). In Definition 2, Table 1 and the "Lean:" line after Theorem 12, the subscripts in `brocardPoint₁` and `brocardPoint₂` print as `brocardPointâĆĄ` / `brocardPointâĆĆ`; this is visible in the rendered page as well. The `\decl` macro (monospace font) does not handle the Unicode subscripts.
3. **Theorem 10, "the three symmedians pass through K":** the library proves this only as the six angle equalities. The paper presents it as a consequence ("So …"), not as a separate Lean statement. The "interior" claim is proved as "K is an affine combination with positive weights" (`symmedianPoint_mem_interior`). The paper explicitly equates the two ("that is"), but the Lean does not mention `interior`. The literal versions (symmedians concurrent and K in `interior (convexHull …)`) are the ★ row `cov_S1a`.
4. **Theorem 14, "isogonal":** the library proves only the three angle equalities, and the paper says so explicitly ("no isogonal-conjugation map is defined"). The classical form (isogonal conjugates by reflection in the bisectors) is ★ `cov_S4`. Consistent.
5. **Statements whose triangle comes from a `section` variable:** `sbtw_touchpoint_singleton_zero/one/two` (Theorem 2) and `spiekerCenter_power_exsphere_eq` (Theorem 9) have no `(t : Triangle ℝ P)` in their first line. The triangle `t` comes from `variable (t : Triangle ℝ P)` earlier in the file (Main.lean:46, Extensions.lean:53), so it is still an explicit argument and still the only hypothesis.
6. **Theorem 9:** the paper's $r_i$ is "the radius of `t.exsphere {i}`", but the Lean writes `t.exradius {i}`. In Mathlib, `exradius signs` is defined as `(exsphere signs).radius` (Incenter.lean:413 in the pinned Mathlib), so the two are the same by definition. The first form of the value is written with `semiperimeter t` and `sideA t` etc. (s and a, b, c). Not a mismatch.
7. **Theorem 16:** the paper's "Ω = Ω′ = K = O" appears in Lean as three equalities with O (Ω = O, Ω′ = O, K = O); "equilateral" appears as `dist A B = dist B C ∧ dist B C = dist C A`. Equivalent.
8. **★ rows with an extra non-degeneracy hypothesis:** `cov_N4` and `cov_N8` (`hM`: the three midpoints are not collinear) and `cov_N6b` and `cov_N7` (`hT`: the anticomplementary vertices are not collinear). These hypotheses come from the classical writer's file. The `L15Classical.lean` header says they are redundant, with new proofs `medial_indep` and `anti_indep`, but the paper does not mention this. Not a mismatch, since the hypotheses are always true for a real triangle.
9. **★ `cov_S3d`** writes angle B as `∠ C B A` while the paper and the library use `∠ A B C`. The two are the same angle (the unoriented angle is symmetric). **★ `cov_N5`** covers only side BC, as the classical file did; `cov_N5_all` (an addition in the library, not one of the 23 classical statements) gives all three sides.
10. **★ counting:** the classical file gives 10 Nagel statements (N1, N2a, N2b, N3, N4, N5, N6a, N6b, N7, N8) and 13 Brocard statements (S1a, S1b, S2a, S2b, S3a–S3e, S4, S5, S6, S7) = 23, matching the paper's "23 Lean statements" and "All ten Nagel-family statements". `cov_N5_all` is the extra 24th row here.
11. **Meaning of "starred" in Paper G:** in Table 1 a star marks a theorem from the *extension files* (`Extensions.lean`): Theorems 5–9 and 16–20. This is unlike Paper F, where starred rows were the Layer-15 statements. On this sheet the ★ section is the Layer-15 classical statements, as the task asked. The Table-1-starred theorems are ordinary numbered sections.

**Dictionary** (the paper's Section 2 defines most of these):

*General setting (both libraries):*
- `t : Triangle ℝ P` / `Affine.Triangle ℝ P` = a non-degenerate triangle (three points not on one line) in a real inner product space of any dimension. `t.points 0`, `t.points 1`, `t.points 2` = A, B, C. The vertex index `i` ranges over 0, 1, 2 (`Fin 3`); "`∀ i,`" = "for each vertex".
- `V` = the space of vectors, `P` = the space of points. `X -ᵥ Y` = the vector from Y to X (that is, X − Y). `v +ᵥ Y` = the point Y moved by v. `(2 : ℝ) • v` = 2·v.
- `dist X Y` = distance |XY|. `midpoint ℝ X Y` = midpoint of X and Y.
- `line[ℝ, X, Y]` = the line through X and Y. `Z ∈ line[…]` = Z is on that line. `(line[ℝ, X, Y]).direction` = its direction (the set of vectors parallel to it); `d ∉ … .direction` = d is not parallel to that line.
- `AffineSubspace.mk' H (ℝ ∙ d)` = the line through H with direction d (`ℝ ∙ d` = all multiples of d; `Submodule.span ℝ {u}` is the same thing).
- `Collinear ℝ {X, Y, Z}` = "X, Y, Z lie on one line". `Cospherical S` / `EuclideanGeometry.Cospherical S` = "the points of S lie on one circle" (on one sphere in higher dimensions). `Set.range f` = the set of all values of f.
- `Sbtw ℝ X Y Z` = "Y lies strictly between X and Z" (on the segment, and different from both ends). `Wbtw ℝ X Y Z` = "Y lies on the segment XZ" (ends allowed).
- `Finset.univ.centroid ℝ t.points` = the centroid G. `Finset.univ.centroid ℝ ![X, Y, Z]` = the centroid (X+Y+Z)/3 of the three points X, Y, Z.
- `Finset.univ.affineCombination ℝ t.points w` = the point w₀A + w₁B + w₂C (the weights summing to 1). `∑ i, w i = 1` = the weights sum to 1.
- `t.incenter` = I; `t.circumcenter` = O; `t.orthocenter` = H (all Mathlib).
- `t.medial` = Mathlib's medial triangle (vertices = midpoints of the sides). `t.medial.incenter` = its incentre.
- `t.touchpoint ∅ i` = Mathlib's contact point of the incircle with the side opposite vertex i. `t.touchpoint {i} i` = the contact point of the excircle opposite vertex i with that same side (the paper proves `excenter {i}` is the excentre opposite vertex i).
- `t.exsphere {i}` = Mathlib's excircle opposite vertex i; `(t.exsphere {i}).center` = its centre Jᵢ; `t.exradius {i}` = its radius rᵢ; `t.inradius` = the inradius r.
- `orthogonalProjection line[ℝ, B, C] X` = the foot of the perpendicular from X to line BC (`(… : P)` only turns it back into a point).
- `∠ X Y Z` = the (unoriented) angle at Y, between 0 and π. `Real.pi` = π; `Real.cot` = cotangent. `⟪u, v⟫` and `inner ℝ u v` = dot product (= 0 means perpendicular).
- `[Fact (Module.finrank ℝ V = 2)]` = "the space is a plane (dimension 2)".
- `let A := t.points 0; …` = local abbreviations; read "where A is t.points 0", and so on.
- `∃ X : P, …` = "there is a point X such that"; `∃!` = "there is exactly one"; `∀ X ∈ S,` = "for every X in S"; `∧` = and; `∨` = or; `↔` = if and only if; `→` = implies; `¬` / `∉` / `≠` = not, not in, not equal.

*Nagel library (`NagelLine/Basic.lean`, `NagelLine/Extensions.lean`):*
- `sideA t`, `sideB t`, `sideC t` = a = |BC|, b = |CA|, c = |AB|. `semiperimeter t` = s = (a+b+c)/2.
- `t.nagelPoint` = N, weights (s−a, s−b, s−c)/s. `Triangle.nagelPoint t.medial` = the Nagel point of the medial triangle (same as `t.medial.nagelPoint`, see Theorem 6).
- `t.gergonnePoint` = the Gergonne point, weights proportional to 1/(s−a), 1/(s−b), 1/(s−c).
- `t.spiekerCenter` = S_p = the incentre of the medial triangle (by definition, `t.medial.incenter`).
- `t.deLongchampsPoint` = L = H + 2(O − H), the reflection of H in O.
- `t.anticomplementary` = the anticomplementary triangle (the image of t under the homothety with centre G and ratio −2); `.orthocenter`, `.incenter` = its orthocentre and incentre.

*Brocard library (`Brocard/Basic.lean`, `Brocard/ExtLemmas.lean`):*
- `t.symmedianPoint` = K = (a²A + b²B + c²C)/(a²+b²+c²).
- `t.brocardPoint₁` = Ω (first Brocard point; weights ∝ 1/b², 1/c², 1/a²); `t.brocardPoint₂` = Ω′ (weights ∝ 1/c², 1/a², 1/b²). In some statements they are renamed `Ω₁`, `Ω₂`.
- `t.area` = Δ = ½·|AB|·|AC|·sin∠BAC.
- `t.lemoinePoints i` (i = 0,…,5) = the six Lemoine points of Definition 2 (the parallel to BC through K gives points 0, 1; the parallel to CA gives 2, 3; the parallel to AB gives 4, 5).

*★ Layer-15 classical files (`L15Classical.lean`, namespaces `NagelLine.Classical` and `Brocard.Classical`; definitions copied verbatim from the classical writer's file `PaperGClassical.lean`, not written by the library builders):*
- `Pt` / `EuclideanSpace ℝ (Fin 2)` = the Euclidean plane ℝ². `h : AffineIndependent ℝ ![A, B, C]` = "A, B, C are not on one line". `ClassicalTri A B C h` = the triangle ABC as a Mathlib triangle (so `(ClassicalTri A B C h).incenter` = I, `.circumcenter` = O, `.orthocenter` = H).
- `ClassicalBary A B C wA wB wC` = the point with barycentrics wA : wB : wC (normalised). `ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2)` = K (barycentrics a² : b² : c²).
- `ClassicalCentroid A B C` = G. `ClassicalSemiperimeter A B C` = s. `ClassicalArea A B C` = Δ = ½·|AB|·|AC|·sin A.
- `ClassicalInContactA/B/C A B C h` = the incircle contact point on BC / CA / AB (foot of the perpendicular from I).
- `ClassicalExcenterA A B C` = the excentre opposite A (barycentrics −a : b : c). `ClassicalExContactA A B C` = the contact point of that excircle with line BC. `ClassicalExradiusA A B C` = its radius. With the letters rotated (`B C A`, `C A B`) they are the excentre, contact point and radius opposite B and opposite C.
- `ClassicalAnticompl A B C` = B + C − A (the anticomplementary vertex opposite A). `AffineEquiv.pointReflection ℝ O H` = the reflection of H through O (= L).
- `ClassicalSymmedian A B C` = the symmedian from A (reflection of the median from A in the bisector at A). `ClassicalIsogonalConj A B C P Q` = for each vertex, the reflection of the line vertex–P in the bisector at that vertex passes through Q.
- `ClassicalFoot B C P` = the foot of the perpendicular from P to BC. `ClassicalPedalCentroid A B C P` = the centroid of the three feet of P.
- `interior (convexHull ℝ {A, B, C})` = the inside of the triangle (not including the sides).


# Part 1 — Nagel line family (repository `paperg_nagel`, link prefix `https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1`)

*(Paper, start of Section 3: "each has the triangle t as its only hypothesis". Every Lean statement below should therefore have `(t : Triangle ℝ P)` and nothing else as hypothesis.)*

---

## THEOREM 1: GERGONNE POINT (thm:gergonne) — paper says

For every triangle and every vertex $i$, the Gergonne point lies on the line through vertex $i$ and the contact point of the incircle with the opposite side (Mathlib's `t.touchpoint ∅ i`). Consequently the three cevians to the incircle contact points have a common point.

### Lean: `gergonnePoint_mem_cevian` — [NagelLine/Main.lean:290](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L290)

```lean
theorem gergonnePoint_mem_cevian (t : Triangle ℝ P) :
    ∀ i, t.gergonnePoint ∈ line[ℝ, t.points i, t.touchpoint ∅ i] := …
```

*In plain English:* for each vertex i, the Gergonne point is on the line through vertex i and the incircle contact point opposite i.

☐ agrees  ☐ differs — note: ____________________

### Lean: `gergonne_cevians_concurrent` — [NagelLine/Main.lean:328](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L328)

```lean
theorem gergonne_cevians_concurrent (t : Triangle ℝ P) :
    ∃ X : P, ∀ i, X ∈ line[ℝ, t.points i, t.touchpoint ∅ i] := …
```

*In plain English:* there is a point X lying on all three of those lines.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 2: NAGEL POINT (thm:nagel) — paper says

For every triangle and every vertex $i$, the Nagel point lies on the line through vertex $i$ and the contact point of the excircle opposite vertex $i$ with the side opposite vertex $i$ (Mathlib's `t.touchpoint {i} i`). Consequently the three cevians to the excircle contact points have a common point. Moreover each such contact point lies strictly between the two other vertices.

*(The paper cites the last sentence as `sbtw_touchpoint_singleton_zero` "and its two companions", Main:170–188. These three are stated inside a `section` whose `variable (t : Triangle ℝ P)` supplies the triangle, so no `(t …)` appears in the statement line itself.)*

### Lean: `nagelPoint_mem_cevian` — [NagelLine/Main.lean:334](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L334)

```lean
theorem nagelPoint_mem_cevian (t : Triangle ℝ P) :
    ∀ i, t.nagelPoint ∈ line[ℝ, t.points i, t.touchpoint {i} i] := …
```

*In plain English:* for each vertex i, the Nagel point is on the line through vertex i and the contact point of the excircle opposite i.

☐ agrees  ☐ differs — note: ____________________

### Lean: `nagel_cevians_concurrent` — [NagelLine/Main.lean:357](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L357)

```lean
theorem nagel_cevians_concurrent (t : Triangle ℝ P) :
    ∃ X : P, ∀ i, X ∈ line[ℝ, t.points i, t.touchpoint {i} i] := …
```

*In plain English:* there is a point X lying on all three of those lines.

☐ agrees  ☐ differs — note: ____________________

### Lean: `sbtw_touchpoint_singleton_zero` — [NagelLine/Main.lean:170](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L170)

```lean
theorem sbtw_touchpoint_singleton_zero :
    Sbtw ℝ (t.points 1) (t.touchpoint {0} 0) (t.points 2) := …
```

*In plain English:* the contact point of the excircle opposite A lies strictly between B and C.

☐ agrees  ☐ differs — note: ____________________

### Lean: `sbtw_touchpoint_singleton_one` — [NagelLine/Main.lean:179](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L179)

```lean
theorem sbtw_touchpoint_singleton_one :
    Sbtw ℝ (t.points 2) (t.touchpoint {1} 1) (t.points 0) := …
```

*In plain English:* the contact point of the excircle opposite B lies strictly between C and A.

☐ agrees  ☐ differs — note: ____________________

### Lean: `sbtw_touchpoint_singleton_two` — [NagelLine/Main.lean:188](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L188)

```lean
theorem sbtw_touchpoint_singleton_two :
    Sbtw ℝ (t.points 0) (t.touchpoint {2} 2) (t.points 1) := …
```

*In plain English:* the contact point of the excircle opposite C lies strictly between A and B.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 3: NAGEL LINE (thm:nagelline) — paper says

For every triangle, $N-G=2(G-I)$, where $I$ is Mathlib's incentre. In particular $I$, $G$, $N$ are collinear.

### Lean: `nagelPoint_vsub_centroid` — [NagelLine/Main.lean:362](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L362)

```lean
theorem nagelPoint_vsub_centroid (t : Triangle ℝ P) :
    t.nagelPoint -ᵥ Finset.univ.centroid ℝ t.points =
      (2 : ℝ) • (Finset.univ.centroid ℝ t.points -ᵥ t.incenter) := …
```

*In plain English:* the vector from G to N equals twice the vector from I to G.

☐ agrees  ☐ differs — note: ____________________

### Lean: `collinear_incenter_centroid_nagelPoint` — [NagelLine/Main.lean:373](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L373)

```lean
theorem collinear_incenter_centroid_nagelPoint (t : Triangle ℝ P) :
    Collinear ℝ {t.incenter, Finset.univ.centroid ℝ t.points, t.nagelPoint} := …
```

*In plain English:* I, G and N lie on one line.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 4: SPIEKER CENTRE (thm:spieker) — paper says

For every triangle, the incentre of the medial triangle is the midpoint of $I$ and $N$. In particular the Spieker centre, $I$ and $N$ are collinear.

### Lean: `medial_incenter_eq_midpoint` — [NagelLine/Main.lean:385](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L385)

```lean
theorem medial_incenter_eq_midpoint (t : Triangle ℝ P) :
    t.medial.incenter = midpoint ℝ t.incenter t.nagelPoint := …
```

*In plain English:* the incentre of the medial triangle is the midpoint of I and N.

☐ agrees  ☐ differs — note: ____________________

### Lean: `collinear_spiekerCenter_incenter_nagelPoint` — [NagelLine/Main.lean:408](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Main.lean#L408)

```lean
theorem collinear_spiekerCenter_incenter_nagelPoint (t : Triangle ℝ P) :
    Collinear ℝ {t.spiekerCenter, t.incenter, t.nagelPoint} := …
```

*In plain English:* the Spieker centre, I and N lie on one line (`spiekerCenter` is by definition the incentre of the medial triangle).

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 5: DE LONGCHAMPS POINT (thm:delong) — paper says

For every triangle, with $L$ the de Longchamps point: (i) $O$ is the midpoint of $H$ and $L$; (ii) $L$, $O$, $H$ are collinear; (iii) $G$, $O$, $L$ are collinear; (iv) $L$ is the orthocentre of the anticomplementary triangle.

### Lean: `midpoint_orthocenter_deLongchampsPoint` — [NagelLine/Extensions.lean:228](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L228)

```lean
theorem midpoint_orthocenter_deLongchampsPoint (t : Triangle ℝ P) :
    midpoint ℝ t.orthocenter t.deLongchampsPoint = t.circumcenter := …
```

*In plain English:* (i) the midpoint of H and L is O.

☐ agrees  ☐ differs — note: ____________________

### Lean: `collinear_deLongchampsPoint_circumcenter_orthocenter` — [NagelLine/Extensions.lean:237](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L237)

```lean
theorem collinear_deLongchampsPoint_circumcenter_orthocenter (t : Triangle ℝ P) :
    Collinear ℝ {t.deLongchampsPoint, t.circumcenter, t.orthocenter} := …
```

*In plain English:* (ii) L, O, H lie on one line.

☐ agrees  ☐ differs — note: ____________________

### Lean: `collinear_centroid_circumcenter_deLongchampsPoint` — [NagelLine/Extensions.lean:249](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L249)

```lean
theorem collinear_centroid_circumcenter_deLongchampsPoint (t : Triangle ℝ P) :
    Collinear ℝ {Finset.univ.centroid ℝ t.points, t.circumcenter, t.deLongchampsPoint} := …
```

*In plain English:* (iii) G, O, L lie on one line.

☐ agrees  ☐ differs — note: ____________________

### Lean: `anticomplementary_orthocenter` — [NagelLine/Extensions.lean:261](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L261)

```lean
theorem anticomplementary_orthocenter (t : Triangle ℝ P) :
    t.anticomplementary.orthocenter = t.deLongchampsPoint := …
```

*In plain English:* (iv) the orthocentre of the anticomplementary triangle is L.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 6: NAGEL POINT OF THE MEDIAL TRIANGLE (thm:medialnagel) — paper says

For every triangle, the Nagel point of Mathlib's medial triangle is the incentre $I$ of the triangle.

*(Paper: "The statement is written `Triangle.nagelPoint t.medial` … the term is the same" as `t.medial.nagelPoint`.)*

### Lean: `medial_nagelPoint` — [NagelLine/Extensions.lean:274](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L274)

```lean
theorem medial_nagelPoint (t : Triangle ℝ P) : Triangle.nagelPoint t.medial = t.incenter := …
```

*In plain English:* the Nagel point of the medial triangle equals the incentre of t.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 7: ISOTOMIC CONTACT POINTS (thm:isotomic) — paper says

For every triangle and each side, the midpoint of the incircle contact point and the contact point of the opposite excircle on that side is the midpoint of the side; for the side $BC$, $\operatorname{mid}(\texttt{touchpoint}\ \emptyset\ 0,\ \texttt{touchpoint}\ \{0\}\ 0)=\operatorname{mid}(B,C)$, and likewise for $CA$ and $AB$.

### Lean: `midpoint_touchpoint_zero` — [NagelLine/Extensions.lean:297](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L297)

```lean
theorem midpoint_touchpoint_zero (t : Triangle ℝ P) :
    midpoint ℝ (t.touchpoint ∅ 0) (t.touchpoint {0} 0) = midpoint ℝ (t.points 1) (t.points 2) := …
```

*In plain English:* side BC: midpoint(incircle contact, A-excircle contact) = midpoint(B, C).

☐ agrees  ☐ differs — note: ____________________

### Lean: `midpoint_touchpoint_one` — [NagelLine/Extensions.lean:308](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L308)

```lean
theorem midpoint_touchpoint_one (t : Triangle ℝ P) :
    midpoint ℝ (t.touchpoint ∅ 1) (t.touchpoint {1} 1) = midpoint ℝ (t.points 2) (t.points 0) := …
```

*In plain English:* side CA: midpoint(incircle contact, B-excircle contact) = midpoint(C, A).

☐ agrees  ☐ differs — note: ____________________

### Lean: `midpoint_touchpoint_two` — [NagelLine/Extensions.lean:319](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L319)

```lean
theorem midpoint_touchpoint_two (t : Triangle ℝ P) :
    midpoint ℝ (t.touchpoint ∅ 2) (t.touchpoint {2} 2) = midpoint ℝ (t.points 0) (t.points 1) := …
```

*In plain English:* side AB: midpoint(incircle contact, C-excircle contact) = midpoint(A, B).

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 8: ANTICOMPLEMENTARY TRIANGLE (thm:anti) — paper says

For every triangle, the Nagel point is the incentre of the anticomplementary triangle.

### Lean: `nagelPoint_eq_anticomplementary_incenter` — [NagelLine/Extensions.lean:332](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L332)

```lean
theorem nagelPoint_eq_anticomplementary_incenter (t : Triangle ℝ P) :
    t.nagelPoint = t.anticomplementary.incenter := …
```

*In plain English:* N equals the incentre of the anticomplementary triangle.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 9: SPIEKER CENTRE AS RADICAL CENTRE (thm:radical) — paper says

For every triangle and all $i,j\in\{0,1,2\}$, the power of the Spieker centre $S_p$ with respect to the excircle opposite vertex $i$ equals its power with respect to the excircle opposite vertex $j$: $|S_pJ_i|^2-r_i^2=|S_pJ_j|^2-r_j^2$, where $J_i$ and $r_i$ are the centre and radius of Mathlib's `t.exsphere {i}`. The common value is

$$\frac14\Bigl(s^2+\frac{(s-a)(s-b)(s-c)}{s}\Bigr)=\frac{s^2+r^2}{4},$$

with $r$ the inradius.

*(Display formula re-typed from the PDF, which pdftotext cannot extract cleanly. The paper cites four declarations: `spiekerCenter_power_exsphere`, `spiekerCenter_power_exsphere_eq` for the left-hand form, and `inradius_sq` and `spiekerCenter_power_exsphere_eq_inradius` for the right-hand form. `spiekerCenter_power_exsphere_eq` is stated inside a `section` with `variable (t : Triangle ℝ P)`, so its statement line has only `(i : Fin 3)`. `t.exradius {i}` is the radius of `t.exsphere {i}`.)*

### Lean: `spiekerCenter_power_exsphere` — [NagelLine/Extensions.lean:357](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L357)

```lean
theorem spiekerCenter_power_exsphere (t : Triangle ℝ P) (i j : Fin 3) :
    dist t.spiekerCenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 =
      dist t.spiekerCenter (t.exsphere {j}).center ^ 2 - t.exradius {j} ^ 2 := …
```

*In plain English:* for any two excircles i, j: (distance from Sp to the centre of excircle i)² − rᵢ² equals the same for excircle j.

☐ agrees  ☐ differs — note: ____________________

### Lean: `spiekerCenter_power_exsphere_eq` — [NagelLine/Extensions.lean:201](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Extensions.lean#L201)

```lean
theorem spiekerCenter_power_exsphere_eq (i : Fin 3) :
    dist t.spiekerCenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 =
      (semiperimeter t ^ 2 + (semiperimeter t - sideA t) * (semiperimeter t - sideB t) *
        (semiperimeter t - sideC t) / semiperimeter t) / 4 := …
```

*In plain English:* for each excircle i, that power equals (s² + (s−a)(s−b)(s−c)/s)/4: the left-hand form of the common value.

☐ agrees  ☐ differs — note: ____________________

### Lean: `inradius_sq` — [NagelLine/Inradius.lean:19](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Inradius.lean#L19)

```lean
theorem inradius_sq (t : Triangle ℝ P) :
    t.inradius ^ 2 = (semiperimeter t - sideA t) * (semiperimeter t - sideB t) *
      (semiperimeter t - sideC t) / semiperimeter t := …
```

*In plain English:* the inradius r satisfies r² = (s−a)(s−b)(s−c)/s (Heron-type formula; it links the two forms).

☐ agrees  ☐ differs — note: ____________________

### Lean: `spiekerCenter_power_exsphere_eq_inradius` — [NagelLine/Inradius.lean:40](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/Inradius.lean#L40)

```lean
theorem spiekerCenter_power_exsphere_eq_inradius (t : Triangle ℝ P) (i : Fin 3) :
    dist t.spiekerCenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 =
      (semiperimeter t ^ 2 + t.inradius ^ 2) / 4 := …
```

*In plain English:* for each excircle i, that power equals (s² + r²)/4: the right-hand form.

☐ agrees  ☐ differs — note: ____________________

# Part 2 — Symmedian and Brocard points (repository `paperg_brocard`, link prefix `https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d`)

*(Paper, start of Section 4: "The only hypothesis is the triangle t, except in Theorem 11(ii) and Theorem 18, where it is stated.")*

---

## THEOREM 10: SYMMEDIANS (thm:symmedian) — paper says

For every triangle, with $K$ the symmedian point and $M_a,M_b,M_c$ the midpoints of $BC,CA,AB$:

$\angle BAK=\angle M_aAC$, $\angle CAK=\angle M_aAB$,
$\angle CBK=\angle M_bBA$, $\angle ABK=\angle M_bBC$,
$\angle ACK=\angle M_cCB$, $\angle BCK=\angle M_cCA$.

So at each vertex the line to $K$ is the reflection of the median in the angle bisector, and the three symmedians pass through $K$. Moreover $K$ is an affine combination of $A,B,C$ with positive weights, that is, it lies in the interior of the triangle.

### Lean: `symmedian_angles` — [Brocard/Main.lean:22](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Main.lean#L22)

```lean
theorem symmedian_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let K := t.symmedianPoint
    ∠ B A K = ∠ (midpoint ℝ B C) A C ∧ ∠ C A K = ∠ (midpoint ℝ B C) A B ∧
    ∠ C B K = ∠ (midpoint ℝ C A) B A ∧ ∠ A B K = ∠ (midpoint ℝ C A) B C ∧
    ∠ A C K = ∠ (midpoint ℝ A B) C B ∧ ∠ B C K = ∠ (midpoint ℝ A B) C A := …
```

*In plain English:* the six angle equalities, exactly as listed (the midpoint of BC is M_a, and so on).

☐ agrees  ☐ differs — note: ____________________

### Lean: `symmedianPoint_mem_interior` — [Brocard/Main.lean:100](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Main.lean#L100)

```lean
theorem symmedianPoint_mem_interior (t : Affine.Triangle ℝ P) :
    ∃ w : Fin 3 → ℝ, ∑ i, w i = 1 ∧ (∀ i, 0 < w i) ∧
      t.symmedianPoint = Finset.univ.affineCombination ℝ t.points w := …
```

*In plain English:* there are three weights, all positive and summing to 1, whose affine combination of A, B, C is K.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 11: PEDAL TRIANGLE (thm:pedal) — paper says

(i) For every triangle, $K$ is the centroid of its pedal triangle: if $F_a,F_b,F_c$ are the orthogonal projections of $K$ onto the lines $BC$, $CA$, $AB$ (Mathlib's `EuclideanGeometry.orthogonalProjection` onto `line[ℝ, B, C]` etc.), then $\tfrac13(F_a+F_b+F_c)=K$. (ii) If moreover $\dim V=2$, then every point $X$ of the plane that is the centroid of its own pedal triangle is $K$.

*(Paper: (ii) has "the instance hypothesis `[Fact (Module.finrank ℝ V = 2)]`".)*

### Lean: `symmedianPoint_eq_centroid_pedal` — [Brocard/Main.lean:115](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Main.lean#L115)

```lean
theorem symmedianPoint_eq_centroid_pedal (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let K := t.symmedianPoint
    Finset.univ.centroid ℝ ![(orthogonalProjection line[ℝ, B, C] K : P),
      (orthogonalProjection line[ℝ, C, A] K : P), (orthogonalProjection line[ℝ, A, B] K : P)] = K := …
```

*In plain English:* (i) the centroid of the three feet of K on BC, CA, AB is K.

☐ agrees  ☐ differs — note: ____________________

### Lean: `eq_symmedianPoint_of_eq_centroid_pedal` — [Brocard/Main.lean:150](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Main.lean#L150)

```lean
theorem eq_symmedianPoint_of_eq_centroid_pedal [Fact (Module.finrank ℝ V = 2)]
    (t : Affine.Triangle ℝ P) (X : P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    Finset.univ.centroid ℝ ![(orthogonalProjection line[ℝ, B, C] X : P),
      (orthogonalProjection line[ℝ, C, A] X : P), (orthogonalProjection line[ℝ, A, B] X : P)] = X →
    X = t.symmedianPoint := …
```

*In plain English:* (ii) in a plane (dimension 2): if the centroid of the three feet of X equals X, then X = K.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 12: BROCARD POINTS (thm:brocard) — paper says

For every triangle, the first Brocard point satisfies $\angle\Omega AB=\angle\Omega BC=\angle\Omega CA$, and the second satisfies $\angle\Omega' BA=\angle\Omega' CB=\angle\Omega' AC$.

### Lean: `brocardPoint₁_angles` — [Brocard/Main.lean:233](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Main.lean#L233)

```lean
theorem brocardPoint₁_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let Ω := t.brocardPoint₁
    ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A := …
```

*In plain English:* ∠ΩAB = ∠ΩBC and ∠ΩBC = ∠ΩCA for the first Brocard point Ω.

☐ agrees  ☐ differs — note: ____________________

### Lean: `brocardPoint₂_angles` — [Brocard/Main.lean:280](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Main.lean#L280)

```lean
theorem brocardPoint₂_angles (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let Ω' := t.brocardPoint₂
    ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C := …
```

*In plain English:* ∠Ω′BA = ∠Ω′CB and ∠Ω′CB = ∠Ω′AC for the second Brocard point Ω′.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 13: BROCARD ANGLE (thm:cot) — paper says

For every triangle, with $\omega=\angle\Omega AB$ and the vertex angles $\angle BAC$, $\angle ABC$, $\angle ACB$:

$$\cot\omega=\cot\angle BAC+\cot\angle ABC+\cot\angle ACB=\frac{a^2+b^2+c^2}{4\Delta},\qquad 0<\omega\le\frac\pi6.$$

*(Display formula re-typed from the PDF. Here cot is Mathlib's `Real.cot`; $a=|BC|$, $b=|CA|$, $c=|AB|$, and Δ is `t.area`.)*

### Lean: `cot_brocardAngle_eq_sum_cot` — [Brocard/Main.lean:327](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Main.lean#L327)

```lean
theorem cot_brocardAngle_eq_sum_cot (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let Ω := t.brocardPoint₁
    Real.cot (∠ Ω A B) = Real.cot (∠ B A C) + Real.cot (∠ A B C) + Real.cot (∠ A C B) := …
```

*In plain English:* cot ω = cot A + cot B + cot C (with ω = ∠ΩAB).

☐ agrees  ☐ differs — note: ____________________

### Lean: `cot_brocardAngle_eq_div_area` — [Brocard/Main.lean:366](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Main.lean#L366)

```lean
theorem cot_brocardAngle_eq_div_area (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let Ω := t.brocardPoint₁
    Real.cot (∠ Ω A B) = (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (4 * t.area) := …
```

*In plain English:* cot ω = (|BC|² + |CA|² + |AB|²)/(4·area).

☐ agrees  ☐ differs — note: ____________________

### Lean: `brocardAngle_pos_le` — [Brocard/Main.lean:402](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Main.lean#L402)

```lean
theorem brocardAngle_pos_le (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1
    let Ω := t.brocardPoint₁
    0 < ∠ Ω A B ∧ ∠ Ω A B ≤ Real.pi / 6 := …
```

*In plain English:* 0 < ω and ω ≤ π/6.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 14: ISOGONAL BROCARD POINTS (thm:isogonal) — paper says

For every triangle, $\angle\Omega AB=\angle\Omega' AC$, $\angle\Omega BC=\angle\Omega' BA$ and $\angle\Omega CA=\angle\Omega' CB$; and $|O\Omega|=|O\Omega'|$.

### Lean: `brocardPoints_isogonal` — [Brocard/Extensions.lean:21](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L21)

```lean
theorem brocardPoints_isogonal (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let Ω₁ := t.brocardPoint₁; let Ω₂ := t.brocardPoint₂
    ∠ Ω₁ A B = ∠ Ω₂ A C ∧ ∠ Ω₁ B C = ∠ Ω₂ B A ∧ ∠ Ω₁ C A = ∠ Ω₂ C B := …
```

*In plain English:* the three angle equalities exactly as listed (Ω₁ = Ω, Ω₂ = Ω′).

☐ agrees  ☐ differs — note: ____________________

### Lean: `dist_circumcenter_brocardPoint` — [Brocard/Extensions.lean:85](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L85)

```lean
theorem dist_circumcenter_brocardPoint (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.brocardPoint₁ = dist t.circumcenter t.brocardPoint₂ := …
```

*In plain English:* |OΩ| = |OΩ′|.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 15: BROCARD CIRCLE (thm:brocardcircle) — paper says

For every triangle, each of $O$, $K$, $\Omega$, $\Omega'$ is at distance $\tfrac12|OK|$ from the midpoint of $OK$; so the four points are cospherical (Mathlib's `EuclideanGeometry.Cospherical`). Moreover $\langle O-\Omega,K-\Omega\rangle=0$ and $\langle O-\Omega',K-\Omega'\rangle=0$, and $\angle O\Omega K=\angle O\Omega' K=\pi/2$.

### Lean: `brocardCircle` — [Brocard/Extensions.lean:116](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L116)

```lean
theorem brocardCircle (t : Affine.Triangle ℝ P) :
    let O := t.circumcenter; let K := t.symmedianPoint
    ∀ X ∈ ({O, K, t.brocardPoint₁, t.brocardPoint₂} : Set P),
      dist X (midpoint ℝ O K) = dist O K / 2 := …
```

*In plain English:* each of O, K, Ω, Ω′ is at distance |OK|/2 from the midpoint of OK.

☐ agrees  ☐ differs — note: ____________________

### Lean: `cospherical_brocardCircle` — [Brocard/Extensions.lean:175](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L175)

```lean
theorem cospherical_brocardCircle (t : Affine.Triangle ℝ P) :
    Cospherical ({t.circumcenter, t.symmedianPoint, t.brocardPoint₁, t.brocardPoint₂} : Set P) := …
```

*In plain English:* O, K, Ω, Ω′ lie on one circle.

☐ agrees  ☐ differs — note: ____________________

### Lean: `brocardCircle_right_angles` — [Brocard/Extensions.lean:183](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L183)

```lean
theorem brocardCircle_right_angles (t : Affine.Triangle ℝ P) :
    let O := t.circumcenter; let K := t.symmedianPoint
    let Ω₁ := t.brocardPoint₁; let Ω₂ := t.brocardPoint₂
    ⟪O -ᵥ Ω₁, K -ᵥ Ω₁⟫ = 0 ∧ ⟪O -ᵥ Ω₂, K -ᵥ Ω₂⟫ = 0 ∧
    ∠ O Ω₁ K = Real.pi / 2 ∧ ∠ O Ω₂ K = Real.pi / 2 := …
```

*In plain English:* ⟨O−Ω, K−Ω⟩ = 0, ⟨O−Ω′, K−Ω′⟩ = 0, ∠OΩK = π/2 and ∠OΩ′K = π/2.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 16: DEGENERATE BROCARD CIRCLE (thm:degenerate) — paper says

For every triangle, $\Omega=O$ or $\Omega=K$ or $\Omega'=O$ or $\Omega'=K$ or $K=O$ holds if and only if the triangle is equilateral; and if the triangle is equilateral then $\Omega=\Omega'=K=O$.

*(Paper: the second declaration has "the two hypotheses $|AB|=|BC|$ and $|BC|=|CA|$".)*

### Lean: `brocardCircle_degenerate` — [Brocard/Extensions.lean:231](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L231)

```lean
theorem brocardCircle_degenerate (t : Affine.Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let O := t.circumcenter; let K := t.symmedianPoint
    let Ω₁ := t.brocardPoint₁; let Ω₂ := t.brocardPoint₂
    (Ω₁ = O ∨ Ω₁ = K ∨ Ω₂ = O ∨ Ω₂ = K ∨ K = O) ↔ (dist A B = dist B C ∧ dist B C = dist C A) := …
```

*In plain English:* (Ω = O or Ω = K or Ω′ = O or Ω′ = K or K = O) exactly when |AB| = |BC| and |BC| = |CA|.

☐ agrees  ☐ differs — note: ____________________

### Lean: `brocard_eq_circumcenter_of_equilateral` — [Brocard/Extensions.lean:314](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L314)

```lean
theorem brocard_eq_circumcenter_of_equilateral (t : Affine.Triangle ℝ P)
    (h₁ : dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2))
    (h₂ : dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)) :
    t.brocardPoint₁ = t.circumcenter ∧ t.brocardPoint₂ = t.circumcenter ∧
      t.symmedianPoint = t.circumcenter := …
```

*In plain English:* if |AB| = |BC| and |BC| = |CA| then Ω = O, Ω′ = O and K = O.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 17: LEMOINE'S FIRST CIRCLE (thm:lemoine) — paper says

For every triangle, the six Lemoine points (Definition 2) are all at the same distance from the midpoint of $OK$; in particular they are cospherical.

### Lean: `lemoineCircle` — [Brocard/Extensions.lean:353](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L353)

```lean
theorem lemoineCircle (t : Affine.Triangle ℝ P) :
    let M := midpoint ℝ t.circumcenter t.symmedianPoint
    ∀ i, dist (t.lemoinePoints i) M = dist (t.lemoinePoints 0) M := …
```

*In plain English:* every Lemoine point i (i = 0,…,5) is as far from the midpoint M of OK as Lemoine point 0 is.

☐ agrees  ☐ differs — note: ____________________

### Lean: `cospherical_lemoinePoints` — [Brocard/Extensions.lean:439](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L439)

```lean
theorem cospherical_lemoinePoints (t : Affine.Triangle ℝ P) :
    Cospherical (Set.range t.lemoinePoints) := …
```

*In plain English:* the six Lemoine points lie on one circle.

☐ agrees  ☐ differs — note: ____________________

---

## THEOREM 18: DROZ-FARNY (thm:droz) — paper says

Let $\dim V=2$, let $d_1,d_2\in V$ with $\langle d_1,d_2\rangle=0$, and suppose that neither $d_1$ nor $d_2$ lies in the direction of any of the three side lines. For $k=1,2,3$ let $X_k$ and $Y_k$ be points of the $k$-th side line ($BC$, $CA$, $AB$) lying on the line through $H$ with direction $d_1$ and $d_2$ respectively. Then the midpoints of $X_1Y_1$, $X_2Y_2$, $X_3Y_3$ are collinear.

*(Paper: "the lines through $H$ are `AffineSubspace.mk' t.orthocenter (ℝ ∙ dᵢ)`".)*

### Lean: `drozFarny` — [Brocard/Extensions.lean:449](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/Extensions.lean#L449)

```lean
theorem drozFarny [Fact (Module.finrank ℝ V = 2)] (t : Affine.Triangle ℝ P) (d₁ d₂ : V)
    (hperp : ⟪d₁, d₂⟫ = 0)
    (h₁a : d₁ ∉ (line[ℝ, t.points 1, t.points 2]).direction)
    (h₁b : d₁ ∉ (line[ℝ, t.points 2, t.points 0]).direction)
    (h₁c : d₁ ∉ (line[ℝ, t.points 0, t.points 1]).direction)
    (h₂a : d₂ ∉ (line[ℝ, t.points 1, t.points 2]).direction)
    (h₂b : d₂ ∉ (line[ℝ, t.points 2, t.points 0]).direction)
    (h₂c : d₂ ∉ (line[ℝ, t.points 0, t.points 1]).direction)
    {X₁ Y₁ X₂ Y₂ X₃ Y₃ : P}
    (hX₁ : X₁ ∈ line[ℝ, t.points 1, t.points 2]) (hX₁' : X₁ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁))
    (hY₁ : Y₁ ∈ line[ℝ, t.points 1, t.points 2]) (hY₁' : Y₁ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂))
    (hX₂ : X₂ ∈ line[ℝ, t.points 2, t.points 0]) (hX₂' : X₂ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁))
    (hY₂ : Y₂ ∈ line[ℝ, t.points 2, t.points 0]) (hY₂' : Y₂ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂))
    (hX₃ : X₃ ∈ line[ℝ, t.points 0, t.points 1]) (hX₃' : X₃ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₁))
    (hY₃ : Y₃ ∈ line[ℝ, t.points 0, t.points 1]) (hY₃' : Y₃ ∈ AffineSubspace.mk' t.orthocenter (ℝ ∙ d₂)) :
    Collinear ℝ ({midpoint ℝ X₁ Y₁, midpoint ℝ X₂ Y₂, midpoint ℝ X₃ Y₃} : Set P) := …
```

*In plain English:* in a plane: d₁ ⟂ d₂, neither parallel to any side; X_k, Y_k on side k (BC, CA, AB) and on the line through H with direction d₁, d₂ respectively; then the three midpoints of X_kY_k are on one line.

☐ agrees  ☐ differs — note: ____________________

# ★ Starred rows: Layer-15 classical statements (`NagelLine/L15Classical.lean`, namespace `NagelLine.Classical`; `Brocard/L15Classical.lean`, namespace `Brocard.Classical`)

Paper, Section 8, "Comparison with the classical statements (Layer 15)": a second fresh writer was given only textbook statements of fifteen classical results (N1–N8, S1–S7), saw neither the paper nor the code, and wrote 23 Lean statements. "All ten Nagel-family statements are covered." The library proves existence for its explicit points; the new proofs add "uniqueness of the common point of the symmedians, uniqueness of each Brocard point in the interior, and the first Lemoine circle for any six points with the defining incidences", and "the four-point collinearity of $I$, $G$, $S_p$, $N$". "No classical statement disagreed with the library." These proofs are now in the two `L15Classical.lean` files.

These statements use the classical writer's own definitions (see the ★ part of the Dictionary), not the library's. They are all in the plane `EuclideanSpace ℝ (Fin 2)`, with the triangle given as three points A, B, C plus `h : AffineIndependent ℝ ![A, B, C]` ("A, B, C are not collinear"). For each row, check that the Lean says what the textbook result named in the heading says, and what the paper's Section 8 sentence claims for it.

---

## ★ N1 GERGONNE (cov_N1) — Theorem 1 — classical statement

The three lines joining each vertex to the incircle contact point on the opposite side meet in a point.

### Lean: `cov_N1` — [NagelLine/L15Classical.lean:581](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L581)

```lean
theorem cov_N1 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ Ge : (EuclideanSpace ℝ (Fin 2)), Ge ∈ line[ℝ, A, ClassicalInContactA A B C h] ∧
      Ge ∈ line[ℝ, B, ClassicalInContactB A B C h] ∧
      Ge ∈ line[ℝ, C, ClassicalInContactC A B C h] := …
```

*In plain English:* some point Ge lies on all three lines A–(incircle contact on BC), B–(contact on CA), C–(contact on AB).

☐ agrees  ☐ differs — note: ____________________

---

## ★ N2 NAGEL (cov_N2a, cov_N2b) — Theorem 2 — classical statement

The three lines joining each vertex to the contact point of the opposite excircle with the opposite side meet in a point (N2a). The A-excircle touches BC at the point D′ with $BD'=s-c$ and $CD'=s-b$ (N2b).

### Lean: `cov_N2a` — [NagelLine/L15Classical.lean:590](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L590)

```lean
theorem cov_N2a (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ Na : (EuclideanSpace ℝ (Fin 2)), Na ∈ line[ℝ, A, ClassicalExContactA A B C] ∧
      Na ∈ line[ℝ, B, ClassicalExContactA B C A] ∧
      Na ∈ line[ℝ, C, ClassicalExContactA C A B] := …
```

*In plain English:* some point Na lies on all three vertex-to-excircle-contact lines.

☐ agrees  ☐ differs — note: ____________________

### Lean: `cov_N2b` — [NagelLine/L15Classical.lean:599](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L599)

```lean
theorem cov_N2b (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    dist B (ClassicalExContactA A B C) = ClassicalSemiperimeter A B C - dist A B ∧
      dist C (ClassicalExContactA A B C) = ClassicalSemiperimeter A B C - dist C A := …
```

*In plain English:* the A-excircle contact point D′ on BC has |BD′| = s − |AB| and |CD′| = s − |CA|.

☐ agrees  ☐ differs — note: ____________________

---

## ★ N3 NAGEL LINE (cov_N3) — Theorem 1 — classical statement

Any common point Na of the Nagel cevians lies on the line IG, with G between I and Na and $GN_a=2\,IG$.

### Lean: `cov_N3` — [NagelLine/L15Classical.lean:616](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L616)

```lean
theorem cov_N3 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) (Na : (EuclideanSpace ℝ (Fin 2)))
    (hA : Na ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hB : Na ∈ line[ℝ, B, ClassicalExContactA B C A])
    (hC : Na ∈ line[ℝ, C, ClassicalExContactA C A B]) :
    Collinear ℝ {(ClassicalTri A B C h).incenter, ClassicalCentroid A B C, Na} ∧
      Wbtw ℝ (ClassicalTri A B C h).incenter (ClassicalCentroid A B C) Na ∧
      dist (ClassicalCentroid A B C) Na =
        2 * dist (ClassicalTri A B C h).incenter (ClassicalCentroid A B C) := …
```

*In plain English:* if Na is on all three Nagel cevians then I, G, Na are collinear, G is between I and Na, and |G Na| = 2|I G|.

☐ agrees  ☐ differs — note: ____________________

---

## ★ N4 SPIEKER (cov_N4) — Theorem 2 — classical statement

The incentre of the medial triangle (Spieker centre) is the midpoint of $I$ and $N_a$; $I$, $G$, $N_a$, $S_p$ are collinear. (Paper Section 8: "the four-point collinearity of $I$, $G$, $S_p$, $N$".)

### Lean: `cov_N4` — [NagelLine/L15Classical.lean:636](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L636)

```lean
theorem cov_N4 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C])
    (hM : AffineIndependent ℝ ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B]) (Na : (EuclideanSpace ℝ (Fin 2)))
    (hA : Na ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hB : Na ∈ line[ℝ, B, ClassicalExContactA B C A])
    (hC : Na ∈ line[ℝ, C, ClassicalExContactA C A B]) :
    (ClassicalTri _ _ _ hM).incenter = midpoint ℝ (ClassicalTri A B C h).incenter Na ∧
      Collinear ℝ {(ClassicalTri A B C h).incenter, ClassicalCentroid A B C, Na,
        (ClassicalTri _ _ _ hM).incenter} := …
```

*In plain English:* given that the midpoints are not collinear (hM) and Na is on all three Nagel cevians: incentre of the medial triangle = midpoint of I and Na, and I, G, Na, that incentre are on one line.

☐ agrees  ☐ differs — note: ____________________

---

## ★ N5 ISOTOMIC CONTACT POINTS (cov_N5, cov_N5_all) — Theorem 5 — classical statement

The incircle and the A-excircle touch BC at points symmetric about the midpoint of BC. (The classical file states only side BC; `cov_N5_all` adds the other two sides and is the extra, eleventh Nagel-file statement.)

### Lean: `cov_N5` — [NagelLine/L15Classical.lean:656](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L656)

```lean
theorem cov_N5 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    midpoint ℝ (ClassicalInContactA A B C h) (ClassicalExContactA A B C) = midpoint ℝ B C := …
```

*In plain English:* midpoint(incircle contact on BC, A-excircle contact on BC) = midpoint(B, C).

☐ agrees  ☐ differs — note: ____________________

### Lean: `cov_N5_all` — [NagelLine/L15Classical.lean:663](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L663)

```lean
theorem cov_N5_all (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    midpoint ℝ (ClassicalInContactA A B C h) (ClassicalExContactA A B C) = midpoint ℝ B C ∧
    midpoint ℝ (ClassicalInContactB A B C h) (ClassicalExContactA B C A) = midpoint ℝ C A ∧
    midpoint ℝ (ClassicalInContactC A B C h) (ClassicalExContactA C A B) = midpoint ℝ A B := …
```

*In plain English:* the same for all three sides BC, CA, AB.

☐ agrees  ☐ differs — note: ____________________

---

## ★ N6 MEDIAL AND ANTICOMPLEMENTARY TRIANGLES (cov_N6a, cov_N6b) — Theorems 6 and 8 — classical statement

The Nagel point of the medial triangle is the incentre $I$ (N6a). The Nagel point is the incentre of the anticomplementary triangle (N6b).

### Lean: `cov_N6a` — [NagelLine/L15Classical.lean:672](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L672)

```lean
theorem cov_N6a (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) (X : (EuclideanSpace ℝ (Fin 2)))
    (hA : X ∈ line[ℝ, midpoint ℝ B C,
      ClassicalExContactA (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)])
    (hB : X ∈ line[ℝ, midpoint ℝ C A,
      ClassicalExContactA (midpoint ℝ C A) (midpoint ℝ A B) (midpoint ℝ B C)])
    (hC : X ∈ line[ℝ, midpoint ℝ A B,
      ClassicalExContactA (midpoint ℝ A B) (midpoint ℝ B C) (midpoint ℝ C A)]) :
    X = (ClassicalTri A B C h).incenter := …
```

*In plain English:* any point X on the three Nagel cevians of the medial triangle (vertices = midpoints of BC, CA, AB) equals the incentre I of ABC.

☐ agrees  ☐ differs — note: ____________________

### Lean: `cov_N6b` — [NagelLine/L15Classical.lean:685](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L685)

```lean
theorem cov_N6b (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C])
    (hT : AffineIndependent ℝ
      ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B])
    (Na : (EuclideanSpace ℝ (Fin 2)))
    (hA : Na ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hB : Na ∈ line[ℝ, B, ClassicalExContactA B C A])
    (hC : Na ∈ line[ℝ, C, ClassicalExContactA C A B]) :
    Na = (ClassicalTri _ _ _ hT).incenter := …
```

*In plain English:* if the anticomplementary vertices are not collinear (hT) and Na is on all three Nagel cevians of ABC, then Na is the incentre of the anticomplementary triangle.

☐ agrees  ☐ differs — note: ____________________

---

## ★ N7 DE LONGCHAMPS (cov_N7) — Theorem 3 — classical statement

The reflection $L$ of $H$ in $O$ lies on the Euler line ($O$, $G$, $H$, $L$ collinear) and is the orthocentre of the anticomplementary triangle.

### Lean: `cov_N7` — [NagelLine/L15Classical.lean:699](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L699)

```lean
theorem cov_N7 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C])
    (hT : AffineIndependent ℝ
      ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B]) :
    Collinear ℝ {(ClassicalTri A B C h).circumcenter, ClassicalCentroid A B C,
        (ClassicalTri A B C h).orthocenter,
        AffineEquiv.pointReflection ℝ (ClassicalTri A B C h).circumcenter
          (ClassicalTri A B C h).orthocenter} ∧
      AffineEquiv.pointReflection ℝ (ClassicalTri A B C h).circumcenter
          (ClassicalTri A B C h).orthocenter = (ClassicalTri _ _ _ hT).orthocenter := …
```

*In plain English:* with L = reflection of H through O: O, G, H, L are on one line, and L is the orthocentre of the anticomplementary triangle (given hT: its vertices are not collinear).

☐ agrees  ☐ differs — note: ____________________

---

## ★ N8 SPIEKER RADICAL CENTRE (cov_N8) — Theorem 7 — classical statement

The Spieker centre has equal power with respect to the three excircles.

### Lean: `cov_N8` — [NagelLine/L15Classical.lean:722](https://github.com/jpbald93/paperg_nagel/blob/e40ee54f20588f5181d348767f3f31be20406cc1/NagelLine/L15Classical.lean#L722)

```lean
theorem cov_N8 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C])
    (hM : AffineIndependent ℝ ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B]) :
    let Sp := (ClassicalTri _ _ _ hM).incenter
    dist Sp (ClassicalExcenterA A B C) ^ 2 - ClassicalExradiusA A B C ^ 2 =
        dist Sp (ClassicalExcenterA B C A) ^ 2 - ClassicalExradiusA B C A ^ 2 ∧
      dist Sp (ClassicalExcenterA B C A) ^ 2 - ClassicalExradiusA B C A ^ 2 =
        dist Sp (ClassicalExcenterA C A B) ^ 2 - ClassicalExradiusA C A B ^ 2 := …
```

*In plain English:* with Sp the incentre of the medial triangle: power of Sp w.r.t. the A-excircle = w.r.t. the B-excircle = w.r.t. the C-excircle (excentres by the textbook formula −a : b : c, radii = distance to the side).

☐ agrees  ☐ differs — note: ____________________

---

## ★ S1 LEMOINE / SYMMEDIAN POINT (cov_S1a, cov_S1b) — Theorem 8 — classical statement

The three symmedians (reflections of the medians in the angle bisectors) meet in a point inside the triangle (S1a), and that point is the point with barycentrics $a^2:b^2:c^2$ (S1b; paper: "uniqueness of the common point of the symmedians", a new proof).

### Lean: `cov_S1a` — [Brocard/L15Classical.lean:254](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L254)

```lean
theorem cov_S1a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ K : Pt, K ∈ ClassicalSymmedian A B C ∧ K ∈ ClassicalSymmedian B C A ∧
      K ∈ ClassicalSymmedian C A B ∧ K ∈ interior (convexHull ℝ {A, B, C}) := …
```

*In plain English:* some point K is on all three symmedians and in the interior of the triangle.

☐ agrees  ☐ differs — note: ____________________

### Lean: `cov_S1b` — [Brocard/L15Classical.lean:275](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L275)

```lean
theorem cov_S1b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (K : Pt)
    (hA : K ∈ ClassicalSymmedian A B C) (hB : K ∈ ClassicalSymmedian B C A)
    (hC : K ∈ ClassicalSymmedian C A B) :
    K = ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2) := …
```

*In plain English:* any point K on all three symmedians is the point with barycentrics a² : b² : c².

☐ agrees  ☐ differs — note: ____________________

---

## ★ S2 PEDAL CENTROID (cov_S2a, cov_S2b) — Theorem 9 — classical statement

The symmedian point is the centroid of its pedal triangle (S2a), and it is the only point with this property (S2b).

### Lean: `cov_S2a` — [Brocard/L15Classical.lean:691](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L691)

```lean
theorem cov_S2a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ClassicalPedalCentroid A B C (ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2)
      (dist A B ^ 2)) = ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2) := …
```

*In plain English:* the centroid of the three feet of K = (a² : b² : c²) on the sides is K.

☐ agrees  ☐ differs — note: ____________________

### Lean: `cov_S2b` — [Brocard/L15Classical.lean:696](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L696)

```lean
theorem cov_S2b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (P : Pt)
    (hP : ClassicalPedalCentroid A B C P = P) :
    P = ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2) := …
```

*In plain English:* any point P (of the plane) equal to the centroid of its own pedal triangle is K.

☐ agrees  ☐ differs — note: ____________________

---

## ★ S3 BROCARD POINTS AND ANGLE (cov_S3a … cov_S3e) — Theorems 12, 13 and 14 — classical statement

There is exactly one interior point Ω with ∠ΩAB = ∠ΩBC = ∠ΩCA (S3a) and exactly one interior Ω′ with ∠Ω′BA = ∠Ω′CB = ∠Ω′AC (S3b) (paper: "uniqueness of each Brocard point in the interior", a new proof); the two Brocard angles are equal (S3c); cot ω = cot A + cot B + cot C = (a²+b²+c²)/(4Δ) (S3d); 0 < ω ≤ π/6 (S3e).

### Lean: `cov_S3a` — [Brocard/L15Classical.lean:490](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L490)

```lean
theorem cov_S3a (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃! Ω : Pt, Ω ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A := …
```

*In plain English:* there is exactly one interior point Ω with ∠ΩAB = ∠ΩBC = ∠ΩCA.

☐ agrees  ☐ differs — note: ____________________

### Lean: `cov_S3b` — [Brocard/L15Classical.lean:497](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L497)

```lean
theorem cov_S3b (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃! Ω' : Pt, Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C := …
```

*In plain English:* there is exactly one interior point Ω′ with ∠Ω′BA = ∠Ω′CB = ∠Ω′AC.

☐ agrees  ☐ differs — note: ____________________

### Lean: `cov_S3c` — [Brocard/L15Classical.lean:504](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L504)

```lean
theorem cov_S3c (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω Ω' : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A)
    (hΩ' : Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C) :
    ∠ Ω A B = ∠ Ω' B A := …
```

*In plain English:* for any such Ω and Ω′: ∠ΩAB = ∠Ω′BA (the two Brocard angles are equal).

☐ agrees  ☐ differs — note: ____________________

### Lean: `cov_S3d` — [Brocard/L15Classical.lean:513](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L513)

```lean
theorem cov_S3d (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A) :
    Real.cot (∠ Ω A B) = Real.cot (∠ B A C) + Real.cot (∠ C B A) + Real.cot (∠ A C B) ∧
      Real.cot (∠ B A C) + Real.cot (∠ C B A) + Real.cot (∠ A C B) =
        (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (4 * ClassicalArea A B C) := …
```

*In plain English:* for any such Ω: cot ∠ΩAB = cot A + cot B + cot C, and that sum = (a²+b²+c²)/(4·area). (Angle B is written ∠CBA, which equals ∠ABC.)

☐ agrees  ☐ differs — note: ____________________

### Lean: `cov_S3e` — [Brocard/L15Classical.lean:528](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L528)

```lean
theorem cov_S3e (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A) :
    0 < ∠ Ω A B ∧ ∠ Ω A B ≤ Real.pi / 6 := …
```

*In plain English:* for any such Ω: 0 < ∠ΩAB ≤ π/6.

☐ agrees  ☐ differs — note: ____________________

---

## ★ S4 ISOGONAL BROCARD POINTS (cov_S4) — Theorem 12 — classical statement

The two Brocard points are isogonal conjugates, and they are equidistant from the circumcentre $O$.

### Lean: `cov_S4` — [Brocard/L15Classical.lean:567](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L567)

```lean
theorem cov_S4 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω Ω' : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A)
    (hΩ' : Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C) :
    ClassicalIsogonalConj A B C Ω Ω' ∧
      dist Ω (ClassicalTri A B C h).circumcenter = dist Ω' (ClassicalTri A B C h).circumcenter := …
```

*In plain English:* for the two (interior, angle-defined) Brocard points: Ω′ lies on the reflection of each vertex–Ω line in that vertex's angle bisector, and |ΩO| = |Ω′O|.

☐ agrees  ☐ differs — note: ____________________

---

## ★ S5 BROCARD CIRCLE (cov_S5) — Theorem 13 — classical statement

The Brocard points lie on the circle with diameter $OK$.

### Lean: `cov_S5` — [Brocard/L15Classical.lean:594](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L594)

```lean
theorem cov_S5 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (Ω Ω' : Pt)
    (hΩ : Ω ∈ interior (convexHull ℝ {A, B, C}) ∧ ∠ Ω A B = ∠ Ω B C ∧ ∠ Ω B C = ∠ Ω C A)
    (hΩ' : Ω' ∈ interior (convexHull ℝ {A, B, C}) ∧
      ∠ Ω' B A = ∠ Ω' C B ∧ ∠ Ω' C B = ∠ Ω' A C) :
    let O := (ClassicalTri A B C h).circumcenter
    let K := ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2)
    dist Ω (midpoint ℝ O K) = dist O K / 2 ∧ dist Ω' (midpoint ℝ O K) = dist O K / 2 := …
```

*In plain English:* for the two Brocard points: each is at distance |OK|/2 from the midpoint of OK.

☐ agrees  ☐ differs — note: ____________________

---

## ★ S6 FIRST LEMOINE CIRCLE (cov_S6) — Theorem 15 — classical statement

The lines through $K$ parallel to the sides meet the other two sides in six points, which lie on a circle centred at the midpoint of $OK$ (paper: "for any six points with the defining incidences", a new proof).

### Lean: `cov_S6` — [Brocard/L15Classical.lean:632](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L632)

```lean
theorem cov_S6 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C])
    (P₁ P₂ P₃ P₄ P₅ P₆ : Pt) :
    let K := ClassicalBary A B C (dist B C ^ 2) (dist C A ^ 2) (dist A B ^ 2)
    P₁ ∈ line[ℝ, A, B] → P₁ ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction →
    P₂ ∈ line[ℝ, A, C] → P₂ ∈ AffineSubspace.mk' K (line[ℝ, B, C]).direction →
    P₃ ∈ line[ℝ, B, C] → P₃ ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction →
    P₄ ∈ line[ℝ, B, A] → P₄ ∈ AffineSubspace.mk' K (line[ℝ, C, A]).direction →
    P₅ ∈ line[ℝ, C, A] → P₅ ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction →
    P₆ ∈ line[ℝ, C, B] → P₆ ∈ AffineSubspace.mk' K (line[ℝ, A, B]).direction →
    ∃ ρ : ℝ, ∀ P ∈ ({P₁, P₂, P₃, P₄, P₅, P₆} : Set Pt),
      dist P (midpoint ℝ (ClassicalTri A B C h).circumcenter K) = ρ := …
```

*In plain English:* any six points P₁…P₆ with these incidences (P₁∈AB, P₂∈AC on the parallel to BC through K; P₃∈BC, P₄∈BA on the parallel to CA; P₅∈CA, P₆∈CB on the parallel to AB) are all at the same distance ρ from the midpoint of OK.

☐ agrees  ☐ differs — note: ____________________

---

## ★ S7 DROZ-FARNY (cov_S7) — Theorem 16 — classical statement

Two perpendicular lines through $H$ cut off on each side line a segment; the three midpoints are collinear. (The classical writer added the non-parallel hypothesis, see the comment in the statement.)

### Lean: `cov_S7` — [Brocard/L15Classical.lean:701](https://github.com/jpbald93/paperg_brocard/blob/ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d/Brocard/L15Classical.lean#L701)

```lean
theorem cov_S7 (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) (u v : Pt)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : inner ℝ u v = 0)
    -- EXTRA HYPOTHESIS: neither line is parallel to (or equal to) a side line, i.e. each meets
    -- each side line in exactly one point. Without this, in a right triangle a line through
    -- H = the right-angle vertex can coincide with a side line, the "segment" is not
    -- determined, and the statement (read with arbitrary intersection points) is false.
    (hu₁ : u ∉ (line[ℝ, B, C]).direction) (hu₂ : u ∉ (line[ℝ, C, A]).direction)
    (hu₃ : u ∉ (line[ℝ, A, B]).direction)
    (hv₁ : v ∉ (line[ℝ, B, C]).direction) (hv₂ : v ∉ (line[ℝ, C, A]).direction)
    (hv₃ : v ∉ (line[ℝ, A, B]).direction)
    (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Pt) :
    let H := (ClassicalTri A B C h).orthocenter
    let ℓ₁ := AffineSubspace.mk' H (Submodule.span ℝ {u})
    let ℓ₂ := AffineSubspace.mk' H (Submodule.span ℝ {v})
    X₁ ∈ ℓ₁ → X₁ ∈ line[ℝ, B, C] → X₂ ∈ ℓ₂ → X₂ ∈ line[ℝ, B, C] →
    Y₁ ∈ ℓ₁ → Y₁ ∈ line[ℝ, C, A] → Y₂ ∈ ℓ₂ → Y₂ ∈ line[ℝ, C, A] →
    Z₁ ∈ ℓ₁ → Z₁ ∈ line[ℝ, A, B] → Z₂ ∈ ℓ₂ → Z₂ ∈ line[ℝ, A, B] →
    Collinear ℝ {midpoint ℝ X₁ X₂, midpoint ℝ Y₁ Y₂, midpoint ℝ Z₁ Z₂} := …
```

*In plain English:* u, v nonzero and perpendicular, neither parallel to a side; X₁,X₂ on BC, Y₁,Y₂ on CA, Z₁,Z₂ on AB, the index-1 points on the line through H with direction u, the index-2 points on the line with direction v; then the three midpoints are collinear.

☐ agrees  ☐ differs — note: ____________________

---

## Overall

- [ ] All 18 numbered theorems (Theorems 1–18) and all ★ Layer-15 rows agree (67 Lean statements). Hand check complete.

Confirmed by: ______________________, date: ______________
