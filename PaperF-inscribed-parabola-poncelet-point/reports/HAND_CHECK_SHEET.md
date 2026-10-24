# Paper F — hand check sheet (for Josh)

**Completed by the author on 22 October 2026: all rows agree.**

**What to do:** for each theorem, read the paper's theorem (top) and the Lean statement(s) (below it). Tick ✅ if the Lean says the same thing as the paper — same objects, every hypothesis in the paper appears in the Lean and vice versa, same conclusion. Write a note if anything looks different, even slightly. You do not need to read any proofs (they are replaced by `…`).

Each Lean statement links to the exact line on GitHub at the published commits: `quadparabola` @ `f85c7bbdbf527c37b940d2331e6d720f01d221db` (Part A, four lines) and `quadrangle` @ `4153ce0b11533a95060eb4f1a25e54708fa13875` (Part B, four points). Every link was checked against a clone at that commit: the linked line is the line holding the `theorem` keyword.

Theorem numbers are those in the compiled paper (Theorems 1–13).

**Dictionary** (the paper's Section 2 and the start of Sections 3–4 define these):

*Shared (file `Basic.lean`, unchanged from Paper E):*
- `Line` = a line given by a point `p` and a direction `d`; `L.carrier` = the set of points on it; `L.d` = its direction.
- `cr a b` = the cross product Im(ā·b) of two plane vectors; `cr u v = 0` means u and v are parallel (or one is zero).
- `meet L₁ L₂` = the intersection point A₁₂ of lines L₁ and L₂. The triangle Tₖ is the one whose three vertices do *not* lie on Lₖ, e.g. T₄ = (`meet L₁ L₂`, `meet L₁ L₃`, `meet L₂ L₃`), and Hₖ is its orthocentre. So `ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)` = H₄, `ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄)` = H₃, `ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄)` = H₂, `ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄)` = H₁.
- `ortho a b c` = orthocentre of triangle abc; `circ a b c` = circumcentre; `foot z L` = foot of the perpendicular from z to line L.
- `miquelPt L₁ L₂ L₃ L₄` = the Miquel point M (explicit formula).
- `GenPos L₁ L₂ L₃ L₄` = "general position": nonzero directions, no two lines parallel, no three through one point.

*Part A (files `Parabola.lean`, `ParabolaPoints.lean`):*
- `reflPt z L` = the reflection of z in line L (= 2·foot − z). Rₖ = `reflPt (miquelPt …) Lₖ`.
- `orthoLine L₁ L₂ L₃ L₄` = the orthocentre line = affine span of H₁, H₂, H₃, H₄; this is the directrix.
- `OnParabola f S z` = "z is on the parabola with focus f and directrix S": dist(z, f) = `Metric.infDist z S`.
- `Metric.infDist z S` = the distance from the point z to the set S (the shortest distance to any point of S).
- `Tangent L f S` = exactly one point of line L is on that parabola (`∃!` = "there exists exactly one"). The paper says openly that this is weaker than classical tangency; the classical version is in the starred rows.
- `foot (miquelPt …) L₂ - foot (miquelPt …) L₁` = W = F₂ − F₁, the direction of the orthocentre line. `dirW` is the same thing by name.
- `directrix` = the orthocentre line as a `Line` (through H₄, direction W); `axisLine` = the line through M with direction i·W; `vertex` = the midpoint of M and the foot of M on the directrix; `tanPt L …` = the named point of contact on L.
- `inner ℝ u v` = the ordinary dot product of u and v (zero = perpendicular). `(meet L₁ L₂ + meet L₃ L₄) / 2` = midpoint N₁ of the diagonal A₁₂A₃₄; likewise N₂ = mid A₁₃A₂₄, N₃ = mid A₁₄A₂₃.
- `Metric.sphere c r` = the circle with centre c and radius r; `dist a b` = distance.

*Part B (files `Quadrangle.lean`, `QuadrangleSym.lean`):*
- `QGen a b c d` = no three of the four points are collinear.
- `poncelet a b c d` = the Poncelet point P, given by the explicit formula d + p_N/(2 p_D) of the paper. (There is no `ponPt` in the code; the formula is `poncelet`.) `ponDen a b c d` = the denominator p_D.
- `npc x y z` = nine-point centre of triangle xyz (explicit formula).
- `tri h.ncol_abc` = Mathlib's triangle on a, b, c (built from the fact, from `QGen`, that they are not collinear); `(tri …).ninePointCircle` = Mathlib's nine-point circle of that triangle. `x ∈ (tri …).ninePointCircle` = x lies on it.
- `lineThrough p q` = the line through p and q; `diagPt a b c d` = the intersection of line ab with line cd (so `diagPt a c b d` = ac ∩ bd, `diagPt a d b c` = ad ∩ bc).
- `I` = the imaginary unit i; `1 + 3 / 2 * I` = 1 + (3/2)i.

*General Lean/Mathlib:*
- `Collinear ℝ {…}` = "on one line"; `EuclideanGeometry.Cospherical {…}` = "on one circle".
- `line[ℝ, P, Q]` = the line through P and Q; `affineSpan ℝ {…}` = the smallest line/plane containing the points; `.Parallel` / `AffineSubspace.Parallel` = parallel.
- `(x).re` = real part; `conj` = complex conjugate; `≠` = not equal; `¬` = not; `∧` = and; `∨` = or; `↔` = if and only if; `∉` = is not in; `∀ L ∈ {L₁, L₂, L₃, L₄}` = "for each of the four lines"; `(hL : L = L₁ ∨ L = L₂ ∨ L = L₃ ∨ L = L₄)` = "L is one of the four lines".

*Starred rows (file `L15Classical.lean`, namespace `QuadMiquel.Classical`; written from the classical literature, not by us):*
- `Point` = ℂ; `ALine` = a line as a Mathlib affine subspace; `PresentedLine` = a line given by two distinct points.
- `Parabola` = a focus (`P.focus`) and a directrix line (`P.directrix`) with the focus not on the directrix; `P.axis` = the line through the focus perpendicular to the directrix.
- `Tangent P L` (classical, *different from the Part A `Tangent`*) = L is a line, L is **not parallel to the axis**, and L meets the parabola in exactly one point.
- `Quadrilateral` = four lines, no two parallel, no three through a point (the classical form of `GenPos`); `Q.lines i` = the i-th line (i = 0,1,2,3); `Q.triangle i` = the triangle of the three vertices not on line i.
- `Inscribed Q P` = P is (classically) tangent to all four lines. `IsMiquelPoint Q M` = M is on all four circumcircles. `IsOrthocentreLine Q L` = L is a line containing all four orthocentres. `IsNewtonGaussLine Q N` = N is a line containing the three diagonal midpoints. `IsInscribedFocusDirectrix Q fd` = fd is (focus, directrix) of some inscribed parabola. `Q.parabola` = our parabola (focus M, directrix the orthocentre line) as a classical `Parabola`.
- `Affine.Triangle ℝ Point` = a (non-degenerate) triangle; `triangleSide t i` = its i-th side line; `OnCircumcircle t z` = z on its circumcircle.
- `Quadrangle` = four points `Q.points i` with no three collinear; `Q.triangle i` = the triangle of the other three points; `IsPonceletPoint Q P` = P is on all four nine-point circles (defined by the geometry, not by our formula).
- `pedalFeet t z` = the three feet of perpendiculars from z to the sides of t; `IsPedalCircle t z (c, r)` = a circle of positive radius r with centre c through the three feet.
- `HasFiniteDiagonalTriangle Q` = no pair of opposite sides is parallel; `Q.diagonalTriangle h` = the triangle of the three diagonal points.
- `RectangularConic` = a centred conic xy = k with perpendicular asymptotes (k = 0 allowed: a pair of perpendicular lines); `RectangularHyperbola` = the same with k ≠ 0; `OnFourPoints Q S` = all four points are in S. `IsDegenerateRectangularCenter Q P` = P is the meeting point of two perpendicular opposite sides.
- `Fin 4` = the indices 0,1,2,3; `∃ P : …,` = "there is a P such that"; `∃! fd,` = "there is exactly one fd such that".

---

## THEOREM 1: REFLECTIONS ON THE ORTHOCENTRE LINE (thm:refl) — paper says

Let $R_k=\operatorname{refl}(M,L_k)$. Then each $R_k$ lies on the orthocentre line, and $\{R_1,R_2,R_3,R_4\}$ is Collinear. Moreover, for each $k$, $\operatorname{cr}(H_i-H_4,\,R_k-H_4)=0$ for $i=1,2,3$.

*(Section 3 assumes only $\mathtt{GenPos}\,L_1\,L_2\,L_3\,L_4$ throughout.)*

### Lean: `reflPt_mem_orthoLine` — [QuadMiquel/Parabola.lean:341](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/Parabola.lean#L341)

```lean
theorem reflPt_mem_orthoLine {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    reflPt (miquelPt L₁ L₂ L₃ L₄) L₁ ∈ orthoLine L₁ L₂ L₃ L₄ ∧
    reflPt (miquelPt L₁ L₂ L₃ L₄) L₂ ∈ orthoLine L₁ L₂ L₃ L₄ ∧
    reflPt (miquelPt L₁ L₂ L₃ L₄) L₃ ∈ orthoLine L₁ L₂ L₃ L₄ ∧
    reflPt (miquelPt L₁ L₂ L₃ L₄) L₄ ∈ orthoLine L₁ L₂ L₃ L₄ := …
```

### Lean: `reflections_collinear` — [QuadMiquel/Parabola.lean:350](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/Parabola.lean#L350)

```lean
theorem reflections_collinear {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    Collinear ℝ ({reflPt (miquelPt L₁ L₂ L₃ L₄) L₁, reflPt (miquelPt L₁ L₂ L₃ L₄) L₂,
      reflPt (miquelPt L₁ L₂ L₃ L₄) L₃, reflPt (miquelPt L₁ L₂ L₃ L₄) L₄} : Set ℂ) := …
```

### Lean: `reflections_collinear_orthos` — [QuadMiquel/Parabola.lean:318](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/Parabola.lean#L318)

```lean
theorem reflections_collinear_orthos {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) (L : Line)
    (hL : L = L₁ ∨ L = L₂ ∨ L = L₃ ∨ L = L₄) :
    cr (ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄) - ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃))
      (reflPt (miquelPt L₁ L₂ L₃ L₄) L - ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)) = 0 ∧
    cr (ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) - ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃))
      (reflPt (miquelPt L₁ L₂ L₃ L₄) L - ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)) = 0 ∧
    cr (ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) - ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃))
      (reflPt (miquelPt L₁ L₂ L₃ L₄) L - ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)) = 0 := …
```

- [x] matches the paper

---

## THEOREM 2: M OFF THE ORTHOCENTRE LINE (thm:off) — paper says

$M$ is not on the orthocentre line: $\operatorname{cr}(W,M-H_4)\neq0$.

### Lean: `miquel_not_mem_orthoLine` — [QuadMiquel/Parabola.lean:396](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/Parabola.lean#L396)

```lean
theorem miquel_not_mem_orthoLine {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    miquelPt L₁ L₂ L₃ L₄ ∉ orthoLine L₁ L₂ L₃ L₄ := …
```

### Lean: `miquel_cr_ne` — [QuadMiquel/Parabola.lean:375](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/Parabola.lean#L375)

```lean
theorem miquel_cr_ne {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    cr (foot (miquelPt L₁ L₂ L₃ L₄) L₂ - foot (miquelPt L₁ L₂ L₃ L₄) L₁)
      (miquelPt L₁ L₂ L₃ L₄ - ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)) ≠ 0 := …
```

- [x] matches the paper

---

## THEOREM 3: TANGENCY (thm:tangent) — paper says

For each $L\in\{L_1,L_2,L_3,L_4\}$, $\mathtt{Tangent}\;L\;M\;(\text{orthocentre line})$: exactly one point of $L$ is equidistant from $M$ and from the orthocentre line.

### Lean: `parabola_tangent` — [QuadMiquel/Parabola.lean:428](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/Parabola.lean#L428)

```lean
theorem parabola_tangent {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) (L : Line)
    (hL : L = L₁ ∨ L = L₂ ∨ L = L₃ ∨ L = L₄) :
    Tangent L (miquelPt L₁ L₂ L₃ L₄) (orthoLine L₁ L₂ L₃ L₄) := …
```

- [x] matches the paper

---

## THEOREM 4: POINTS OF CONTACT (thm:tanpt) — paper says

For each $L\in\{L_1,\dots,L_4\}$: $\mathtt{tanPt}\;L$ is on $L$, it is on the parabola with focus $M$ and directrix the orthocentre line, and every point of $L$ on that parabola equals $\mathtt{tanPt}\;L$.

### Lean: `tanPt_all` — [QuadMiquel/ParabolaPoints.lean:151](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/ParabolaPoints.lean#L151)

```lean
theorem tanPt_all {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    ∀ L ∈ ({L₁, L₂, L₃, L₄} : Set Line),
      tanPt L L₁ L₂ L₃ L₄ ∈ L.carrier ∧
      OnParabola (miquelPt L₁ L₂ L₃ L₄) (orthoLine L₁ L₂ L₃ L₄) (tanPt L L₁ L₂ L₃ L₄) ∧
      ∀ z, z ∈ L.carrier → OnParabola (miquelPt L₁ L₂ L₃ L₄) (orthoLine L₁ L₂ L₃ L₄) z →
        z = tanPt L L₁ L₂ L₃ L₄ := …
```

- [x] matches the paper

---

## THEOREM 5: VERTEX AND AXIS (thm:vertex) — paper says

The vertex $V$ is on the parabola; $\operatorname{dist}(V,M)=\tfrac12\operatorname{infDist}(M,\text{orthocentre line})$; and for every point $z$ on the parabola, $\operatorname{infDist}(V,\text{orthocentre line})\le\operatorname{infDist}(z,\text{orthocentre line})$. The vertex is on the axis, and the axis is perpendicular to the directrix: $\operatorname{Re}\big(\overline{iW}\,W\big)=0$.

*(Paper, after the theorem: "The last two statements hold for all four lines, with no hypothesis" — so `vertex_mem_axis` and `axis_perp` correctly have no `GenPos`.)*

### Lean: `vertex_onParabola` — [QuadMiquel/ParabolaPoints.lean:224](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/ParabolaPoints.lean#L224)

```lean
theorem vertex_onParabola {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    OnParabola (miquelPt L₁ L₂ L₃ L₄) (orthoLine L₁ L₂ L₃ L₄) (vertex L₁ L₂ L₃ L₄) := …
```

### Lean: `dist_vertex` — [QuadMiquel/ParabolaPoints.lean:213](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/ParabolaPoints.lean#L213)

```lean
theorem dist_vertex {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    dist (vertex L₁ L₂ L₃ L₄) (miquelPt L₁ L₂ L₃ L₄) =
      Metric.infDist (miquelPt L₁ L₂ L₃ L₄) (orthoLine L₁ L₂ L₃ L₄ : Set ℂ) / 2 := …
```

### Lean: `vertex_closest` — [QuadMiquel/ParabolaPoints.lean:246](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/ParabolaPoints.lean#L246)

```lean
theorem vertex_closest {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) {z : ℂ}
    (hz : OnParabola (miquelPt L₁ L₂ L₃ L₄) (orthoLine L₁ L₂ L₃ L₄) z) :
    Metric.infDist (vertex L₁ L₂ L₃ L₄) (orthoLine L₁ L₂ L₃ L₄ : Set ℂ) ≤
      Metric.infDist z (orthoLine L₁ L₂ L₃ L₄ : Set ℂ) := …
```

### Lean: `vertex_mem_axis` — [QuadMiquel/ParabolaPoints.lean:185](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/ParabolaPoints.lean#L185)

```lean
theorem vertex_mem_axis (L₁ L₂ L₃ L₄ : Line) :
    vertex L₁ L₂ L₃ L₄ ∈ (axisLine L₁ L₂ L₃ L₄).carrier := …
```

### Lean: `axis_perp` — [QuadMiquel/ParabolaPoints.lean:205](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/ParabolaPoints.lean#L205)

```lean
theorem axis_perp (L₁ L₂ L₃ L₄ : Line) :
    (conj (axisLine L₁ L₂ L₃ L₄).d * (directrix L₁ L₂ L₃ L₄).d).re = 0 := …
```

- [x] matches the paper

---

## THEOREM 6: NEWTON–GAUSS LINE ⟂ DIRECTRIX (thm:newton) — paper says

Let $N_1,N_2,N_3$ be the midpoints of the diagonals $A_{12}A_{34}$, $A_{13}A_{24}$, $A_{14}A_{23}$. For all $x,y$ on the orthocentre line, $\langle x-y,\,N_2-N_1\rangle=0$ and $\langle x-y,\,N_3-N_1\rangle=0$, with Mathlib's real inner product on $\mathbb{C}$. Also $\langle W,N_2-N_1\rangle=\langle W,N_3-N_1\rangle=0$.

### Lean: `newton_perp_orthoLine` — [QuadMiquel/Parabola.lean:556](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/Parabola.lean#L556)

```lean
theorem newton_perp_orthoLine {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) {x y : ℂ}
    (hx : x ∈ orthoLine L₁ L₂ L₃ L₄) (hy : y ∈ orthoLine L₁ L₂ L₃ L₄) :
    inner ℝ (x - y) ((meet L₁ L₃ + meet L₂ L₄) / 2 - (meet L₁ L₂ + meet L₃ L₄) / 2) = 0 ∧
    inner ℝ (x - y) ((meet L₁ L₄ + meet L₂ L₃) / 2 - (meet L₁ L₂ + meet L₃ L₄) / 2) = 0 := …
```

### Lean: `newton_perp_cr` — [QuadMiquel/Parabola.lean:539](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/Parabola.lean#L539)

```lean
theorem newton_perp_cr {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    inner ℝ (foot (miquelPt L₁ L₂ L₃ L₄) L₂ - foot (miquelPt L₁ L₂ L₃ L₄) L₁)
      ((meet L₁ L₃ + meet L₂ L₄) / 2 - (meet L₁ L₂ + meet L₃ L₄) / 2) = 0 ∧
    inner ℝ (foot (miquelPt L₁ L₂ L₃ L₄) L₂ - foot (miquelPt L₁ L₂ L₃ L₄) L₁)
      ((meet L₁ L₄ + meet L₂ L₃) / 2 - (meet L₁ L₂ + meet L₃ L₄) / 2) = 0 := …
```

- [x] matches the paper

---

## THEOREM 7: LAMBERT (thm:lambert) — paper says

Each of $L_1,\dots,L_4$ is tangent to the parabola with focus $M$ and directrix the orthocentre line, and $M$ lies on the circumcircle of each of $T_1,\dots,T_4$.

### Lean: `lambert` — [QuadMiquel/ParabolaPoints.lean:264](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/ParabolaPoints.lean#L264)

```lean
theorem lambert {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    (∀ L ∈ ({L₁, L₂, L₃, L₄} : Set Line),
      Tangent L (miquelPt L₁ L₂ L₃ L₄) (orthoLine L₁ L₂ L₃ L₄)) ∧
    miquelPt L₁ L₂ L₃ L₄ ∈ Metric.sphere (circ (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄))
      (dist (meet L₂ L₃) (circ (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄))) ∧
    miquelPt L₁ L₂ L₃ L₄ ∈ Metric.sphere (circ (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄))
      (dist (meet L₁ L₃) (circ (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄))) ∧
    miquelPt L₁ L₂ L₃ L₄ ∈ Metric.sphere (circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄))
      (dist (meet L₁ L₂) (circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄))) ∧
    miquelPt L₁ L₂ L₃ L₄ ∈ Metric.sphere (circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃))
      (dist (meet L₁ L₂) (circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃))) := …
```

- [x] matches the paper

---

## THEOREM 8: ORTHOCENTRIC CASE (thm:ortho) — paper says

If $\mathtt{QGen}\;a\;b\;c\;d$, then $\mathtt{ponDen}\;a\;b\;c\;d=0$ if and only if $d=\operatorname{ortho}(a,b,c)$. In that case the four nine-point centres are equal, and the four Mathlib nine-point circles (`Affine.Simplex.ninePointCircle`) of the triangles are equal. For example $a=0$, $b=4$, $c=1+2i$, $d=1+\tfrac32i$ satisfy $\mathtt{QGen}$, $d=\operatorname{ortho}(a,b,c)$ and $\mathtt{ponDen}\;a\;b\;c\;d=0$.

### Lean: `ponDen_eq_zero_iff` — [QuadMiquel/Quadrangle.lean:571](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L571)

```lean
theorem ponDen_eq_zero_iff {a b c d : ℂ} (h : QGen a b c d) : ponDen a b c d = 0 ↔ d = ortho a b c := …
```

### Lean: `orthocentric_npc_eq` — [QuadMiquel/Quadrangle.lean:718](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L718)

```lean
theorem orthocentric_npc_eq {a b c d : ℂ} (h : QGen a b c d) (ho : d = ortho a b c) :
    npc a b d = npc a b c ∧ npc a c d = npc a b c ∧ npc b c d = npc a b c := …
```

### Lean: `orthocentric_ninePointCircle_eq` — [QuadMiquel/Quadrangle.lean:1114](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L1114)

```lean
theorem orthocentric_ninePointCircle_eq {a b c d : ℂ} (h : QGen a b c d) (ho : d = ortho a b c) :
    (tri h.ncol_abd).ninePointCircle = (tri h.ncol_abc).ninePointCircle ∧
      (tri h.ncol_acd).ninePointCircle = (tri h.ncol_abc).ninePointCircle ∧
      (tri h.ncol_bcd).ninePointCircle = (tri h.ncol_abc).ninePointCircle := …
```

### Lean: `orthocentric_example` — [QuadMiquel/Quadrangle.lean:598](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L598)

```lean
theorem orthocentric_example :
    QGen 0 4 (1 + 2 * I) (1 + 3 / 2 * I) ∧ (1 + 3 / 2 * I) = ortho 0 4 (1 + 2 * I) ∧
      ponDen 0 4 (1 + 2 * I) (1 + 3 / 2 * I) = 0 := …
```

- [x] matches the paper

---

## THEOREM 9: PONCELET POINT ON THE NINE-POINT CIRCLES (thm:nine) — paper says

If $\mathtt{QGen}\;a\;b\;c\;d$ and $d\neq\operatorname{ortho}(a,b,c)$, then $P$ lies on the Mathlib nine-point circle of each of the four triangles.

*(The four triangles are $(a,b,c)$, $(a,b,d)$, $(a,c,d)$, $(b,c,d)$. Paper, after the theorem: the local form `poncelet_on_ninepoint` states $\operatorname{dist}(P,\mathtt{npc}(\Delta))=\operatorname{dist}(m,\mathtt{npc}(\Delta))$ for one side midpoint $m$ of each triangle $\Delta$.)*

### Lean: `ninepoint_concur` — [QuadMiquel/Quadrangle.lean:679](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L679)

```lean
theorem ninepoint_concur {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c) :
    poncelet a b c d ∈ (tri h.ncol_abc).ninePointCircle ∧ poncelet a b c d ∈ (tri h.ncol_abd).ninePointCircle ∧
      poncelet a b c d ∈ (tri h.ncol_acd).ninePointCircle ∧ poncelet a b c d ∈ (tri h.ncol_bcd).ninePointCircle := …
```

### Lean: `poncelet_on_ninepoint` — [QuadMiquel/Quadrangle.lean:626](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L626)

```lean
theorem poncelet_on_ninepoint {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c) :
    dist (poncelet a b c d) (npc a b c) = dist ((a + b) / 2) (npc a b c) ∧
    dist (poncelet a b c d) (npc a b d) = dist ((a + b) / 2) (npc a b d) ∧
    dist (poncelet a b c d) (npc a c d) = dist ((a + c) / 2) (npc a c d) ∧
    dist (poncelet a b c d) (npc b c d) = dist ((b + c) / 2) (npc b c d) := …
```

- [x] matches the paper

---

## THEOREM 10: UNIQUENESS (thm:unique) — paper says

Under the same hypotheses, any point on the nine-point circles of $(a,b,c)$, $(a,b,d)$ and $(a,c,d)$ equals $P$.

### Lean: `ninepoint_unique` — [QuadMiquel/Quadrangle.lean:692](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L692)

```lean
theorem ninepoint_unique {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c) {w : ℂ}
    (h1 : w ∈ (tri h.ncol_abc).ninePointCircle) (h2 : w ∈ (tri h.ncol_abd).ninePointCircle)
    (h3 : w ∈ (tri h.ncol_acd).ninePointCircle) : w = poncelet a b c d := …
```

- [x] matches the paper

---

## THEOREM 11: PEDAL CIRCLES (thm:pedal) — paper says

If $\mathtt{QGen}\;a\;b\;c\;d$, $d\neq\operatorname{ortho}(a,b,c)$, and $\{a,b,c,d\}$ is not `EuclideanGeometry.Cospherical`, then for each of the four points $v$, the feet of the perpendiculars from $v$ to the three sides of the triangle of the other three points, together with $P$, are cospherical. (For $v=d$ the sides are $ab$, $bc$, $ca$; for $v=c$, $ab$, $bd$, $da$; for $v=b$, $ac$, $cd$, $da$; for $v=a$, $bc$, $cd$, $db$; the line through $p$ and $q$ is $\mathtt{lineThrough}\;p\;q=(p,q-p)$.)

### Lean: `poncelet_on_pedal_d` — [QuadMiquel/Quadrangle.lean:906](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L906)

```lean
theorem poncelet_on_pedal_d {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c)
    (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical ({foot d (lineThrough a b), foot d (lineThrough b c),
      foot d (lineThrough c a), poncelet a b c d} : Set ℂ) := …
```

### Lean: `poncelet_on_pedal_c` — [QuadMiquel/Quadrangle.lean:917](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L917)

```lean
theorem poncelet_on_pedal_c {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c)
    (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical ({foot c (lineThrough a b), foot c (lineThrough b d),
      foot c (lineThrough d a), poncelet a b c d} : Set ℂ) := …
```

### Lean: `poncelet_on_pedal_b` — [QuadMiquel/Quadrangle.lean:928](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L928)

```lean
theorem poncelet_on_pedal_b {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c)
    (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical ({foot b (lineThrough a c), foot b (lineThrough c d),
      foot b (lineThrough d a), poncelet a b c d} : Set ℂ) := …
```

### Lean: `poncelet_on_pedal_a` — [QuadMiquel/Quadrangle.lean:942](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L942)

```lean
theorem poncelet_on_pedal_a {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c)
    (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical ({foot a (lineThrough b c), foot a (lineThrough c d),
      foot a (lineThrough d b), poncelet a b c d} : Set ℂ) := …
```

- [x] matches the paper

---

## THEOREM 12: DIAGONAL TRIANGLE (thm:diag) — paper says

If $\mathtt{QGen}\;a\;b\;c\;d$, $d\neq\operatorname{ortho}(a,b,c)$, and none of the three pairs of opposite sides is parallel (`AffineSubspace.Parallel`: $\operatorname{line}[a,b]\not\parallel\operatorname{line}[c,d]$, $\operatorname{line}[a,c]\not\parallel\operatorname{line}[b,d]$, $\operatorname{line}[a,d]\not\parallel\operatorname{line}[b,c]$), then the three diagonal points $ab\cap cd$, $ac\cap bd$, $ad\cap bc$ and $P$ are cospherical.

### Lean: `poncelet_on_diagonal_circle` — [QuadMiquel/Quadrangle.lean:1041](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/Quadrangle.lean#L1041)

```lean
theorem poncelet_on_diagonal_circle {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c)
    (p1 : ¬ (line[ℝ, a, b]).Parallel (line[ℝ, c, d])) (p2 : ¬ (line[ℝ, a, c]).Parallel (line[ℝ, b, d]))
    (p3 : ¬ (line[ℝ, a, d]).Parallel (line[ℝ, b, c])) :
    EuclideanGeometry.Cospherical
      ({diagPt a b c d, diagPt a c b d, diagPt a d b c, poncelet a b c d} : Set ℂ) := …
```

- [x] matches the paper

---

## THEOREM 13: SYMMETRY (thm:s4) — paper says

If $\mathtt{QGen}\;a\;b\;c\;d$ and $d\neq\operatorname{ortho}(a,b,c)$, then $\mathtt{poncelet}\;a\;b\;c\;d$ equals $\mathtt{poncelet}$ applied to $(a,c,b,d)$, $(b,c,a,d)$, $(a,b,d,c)$, $(d,b,c,a)$, $(a,d,c,b)$ and $(b,c,d,a)$. The first three are the permutations $(b\,c)$, $(a\,b\,c)$, $(c\,d)$, which generate $S_4$. Moreover, under $\mathtt{QGen}\;a\;b\;c\;d$, $d=\operatorname{ortho}(a,b,c)\iff c=\operatorname{ortho}(a,b,d)$.

### Lean: `poncelet_S4` — [QuadMiquel/QuadrangleSym.lean:96](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/QuadrangleSym.lean#L96)

```lean
theorem poncelet_S4 {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c) :
    poncelet a c b d = poncelet a b c d ∧ poncelet b c a d = poncelet a b c d ∧
    poncelet a b d c = poncelet a b c d ∧ poncelet d b c a = poncelet a b c d ∧
    poncelet a d c b = poncelet a b c d ∧ poncelet b c d a = poncelet a b c d := …
```

### Lean: `poncelet_swap_cd` — [QuadMiquel/QuadrangleSym.lean:75](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/QuadrangleSym.lean#L75)

```lean
theorem poncelet_swap_cd {a b c d : ℂ} (h : QGen a b c d) (ho : d ≠ ortho a b c) :
    poncelet a b d c = poncelet a b c d := …
```

### Lean: `ortho_swap_iff` — [QuadMiquel/QuadrangleSym.lean:60](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/QuadrangleSym.lean#L60)

```lean
theorem ortho_swap_iff {a b c d : ℂ} (h : QGen a b c d) : d = ortho a b c ↔ c = ortho a b d := …
```

- [x] matches the paper

---

# Starred rows of Table 1 (Layer-15 file `QuadMiquel/L15Classical.lean`, namespace `QuadMiquel.Classical`)

These statements (and the definitions they use: see the last part of the Dictionary) were written by an independent party from the classical literature; the paper says they are reproduced verbatim. Check that each Lean statement says what the table row (and the paper sentence that cites it) says. Part A rows are in `quadparabola`, Part B rows in `quadrangle`.

## ★ TANGENCY IN THE CLASSICAL SENSE — paper says

Table: "tangency in the classical sense". Section 3: "We prove that none of the four lines is such a line [parallel to the axis] …, so for them the classical tangency (exactly one common point and not parallel to the axis) holds in full; this is stated as `QuadMiquel.Classical.l15_lines_not_parallel_axis` and `QuadMiquel.Classical.cov_classical_C4_a` in the Layer-15 file."

### Lean: `cov_classical_C4_a` — [QuadMiquel/L15Classical.lean:627](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/L15Classical.lean#L627)

```lean
theorem cov_classical_C4_a (Q : Quadrilateral) :
    ∃ P : Parabola, Inscribed Q P ∧ IsMiquelPoint Q P.focus ∧
      IsOrthocentreLine Q P.directrix.carrier := …
```

*(Also cited in the same sentence; not a table row:)*

### Lean: `l15_lines_not_parallel_axis` — [QuadMiquel/L15Classical.lean:595](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/L15Classical.lean#L595)

```lean
theorem l15_lines_not_parallel_axis (Q : Quadrilateral) (i : Fin 4) :
    ¬ AffineSubspace.Parallel (Q.lines i).carrier Q.parabola.axis := …
```

- [x] matches the paper

---

## ★ UNIQUENESS OF THE INSCRIBED PARABOLA (FOCUS, DIRECTRIX) — paper says

Table: "uniqueness of the inscribed parabola (focus, directrix)". Section 3: "… every parabola inscribed in the quadrilateral has focus $M$ and directrix the orthocentre line, so the focus–directrix pair of the inscribed parabola is unique (`cov_classical_C4_b`)".

### Lean: `cov_classical_C4_b` — [QuadMiquel/L15Classical.lean:1046](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/L15Classical.lean#L1046)

```lean
theorem cov_classical_C4_b (Q : Quadrilateral) :
    ∃! fd : Point × ALine, IsInscribedFocusDirectrix Q fd := …
```

- [x] matches the paper

---

## ★ LAMBERT FOR EVERY PARABOLA TANGENT TO A TRIANGLE — paper says

Table: "Lambert for every parabola tangent to a triangle" (`cov_classical_C6_a`, `_C6_b`). Section 3: "the focus of *any* parabola tangent, in the classical sense, to the three side lines of a triangle lies on its circumcircle (`cov_classical_C6_a`); hence every parabola inscribed in the quadrilateral has focus $M$ (`cov_classical_C6_b`)".

### Lean: `cov_classical_C6_a` — [QuadMiquel/L15Classical.lean:925](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/L15Classical.lean#L925)

```lean
theorem cov_classical_C6_a (t : Affine.Triangle ℝ Point) (P : Parabola)
    (ht : ∀ i : Fin 3, Tangent P (triangleSide t i)) :
    OnCircumcircle t P.focus := …
```

### Lean: `cov_classical_C6_b` — [QuadMiquel/L15Classical.lean:1020](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/L15Classical.lean#L1020)

```lean
theorem cov_classical_C6_b (Q : Quadrilateral) (P : Parabola) (hP : Inscribed Q P) :
    IsMiquelPoint Q P.focus := …
```

*(Also cited in that paragraph and in Section 9, not a table row: "the Newton–Gauss line is parallel to the axis of every inscribed parabola (`cov_classical_C5_b`)".)*

### Lean: `cov_classical_C5_b` — [QuadMiquel/L15Classical.lean:1059](https://github.com/jpbald93/quadparabola/blob/f85c7bbdbf527c37b940d2331e6d720f01d221db/QuadMiquel/L15Classical.lean#L1059)

```lean
theorem cov_classical_C5_b (Q : Quadrilateral) (P : Parabola) (hP : Inscribed Q P) :
    ∃ N : ALine, IsNewtonGaussLine Q N ∧ AffineSubspace.Parallel N P.axis := …
```

- [x] matches the paper

---

## ★ PEDAL, DIAGONAL CIRCLES: ORTHOCENTRIC CASE — paper says

Table: "pedal, diagonal circles: orthocentric case" (`cov_classical_D3_b`, `_D4`). Section 4: "in the orthocentric case the four pedal circles and the circumcircle of the diagonal triangle are the common nine-point circle, so every point of it lies on them. Theorems 11 and 12 do not state this; the Layer-15 file proves these branches (`cov_classical_D3_a`, `cov_classical_D3_b`, `cov_classical_D4`)." Section 9: "The library is narrower in excluding the orthocentric case from the pedal and diagonal statements; the new proofs cover it …, and show in addition that the three pedal feet are distinct, so the pedal circle exists and is unique."

*(Note: these statements do not mention the orthocentric case explicitly; they hold for any point P on all four nine-point circles, which covers the orthocentric case because there every point of the common nine-point circle qualifies. The pedal hypothesis "v not on the circumcircle of the other three" is the classical form of "not concyclic".)*

### Lean: `cov_classical_D3_b` — [QuadMiquel/L15Classical.lean:948](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/L15Classical.lean#L948)

```lean
theorem cov_classical_D3_b (Q : Quadrangle) (P : Point) (hP : IsPonceletPoint Q P)
    (i : Fin 4) (h : ¬ OnCircumcircle (Q.triangle i) (Q.points i)) :
    EuclideanGeometry.Cospherical
      (Set.range (pedalFeet (Q.triangle i) (Q.points i)) ∪ {P}) := …
```

### Lean: `cov_classical_D4` — [QuadMiquel/L15Classical.lean:964](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/L15Classical.lean#L964)

```lean
theorem cov_classical_D4 (Q : Quadrangle) (h : HasFiniteDiagonalTriangle Q)
    (P : Point) (hP : IsPonceletPoint Q P) :
    OnCircumcircle (Q.diagonalTriangle h) P := …
```

*(Also cited in the same sentence; not a table row:)*

### Lean: `cov_classical_D3_a` — [QuadMiquel/L15Classical.lean:942](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/L15Classical.lean#L942)

```lean
theorem cov_classical_D3_a (Q : Quadrangle) (P : Point) (hP : IsPonceletPoint Q P)
    (i : Fin 4) (h : ¬ OnCircumcircle (Q.triangle i) (Q.points i)) :
    ∃! cr : Point × ℝ, IsPedalCircle (Q.triangle i) (Q.points i) cr ∧
      dist P cr.1 = cr.2 := …
```

- [x] matches the paper

---

## ★ CENTRE OF A RECTANGULAR CONIC — paper says

Table: "centre of a rectangular conic" (`cov_classical_D1_c`, `_D1_d`). Section 4: "every point on the four nine-point circles is the centre of a rectangular conic through the four points (`cov_classical_D1_c`), and it is a proper rectangular hyperbola unless that point is the intersection of two perpendicular opposite sides (`cov_classical_D1_d`)."

### Lean: `cov_classical_D1_c` — [QuadMiquel/L15Classical.lean:1042](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/L15Classical.lean#L1042)

```lean
theorem cov_classical_D1_c (Q : Quadrangle) (P : Point) (hP : IsPonceletPoint Q P) :
    ∃ H : RectangularConic, H.center = P ∧ OnFourPoints Q H.locus := …
```

### Lean: `cov_classical_D1_d` — [QuadMiquel/L15Classical.lean:1146](https://github.com/jpbald93/quadrangle/blob/4153ce0b11533a95060eb4f1a25e54708fa13875/QuadMiquel/L15Classical.lean#L1146)

```lean
theorem cov_classical_D1_d (Q : Quadrangle) (P : Point) (hP : IsPonceletPoint Q P)
    (h : ¬ IsDegenerateRectangularCenter Q P) :
    ∃ H : RectangularHyperbola,
      H.toRectangularConic.center = P ∧ OnFourPoints Q H.toRectangularConic.locus := …
```

- [x] matches the paper

---

## Mismatches noticed while building this sheet

None of the 13 numbered theorems or the starred rows showed a mismatch between the paper text and the Lean statement: hypotheses, objects (including which orthocentre is $H_1,\dots,H_4$, which midpoint is $N_1,N_2,N_3$, which sides are used for each pedal circle, which diagonal points are used, the six permutations in Theorem 13, and the example $a=0$, $b=4$, $c=1+2i$, $d=1+\tfrac32 i$) and conclusions agree. Nothing has been changed. Things worth a second look (not mismatches):

- **Theorems 3, 4 and 7 use the weak `Tangent`** (exactly one common point). The paper says so openly in Section 3 and handles classical tangency in the starred rows; this is not a mismatch, but Table 1's wording "the parabola is tangent to each line" is in the weak sense.
- **Theorem 5:** `vertex_mem_axis` and `axis_perp` have no `GenPos` hypothesis. The paper says this explicitly ("hold … with no hypothesis"), so it is consistent with the text, although the section intro says each theorem "assumes only GenPos" (i.e. at most `GenPos`).
- **Theorem 2:** the paper's $\operatorname{cr}(W,M-H_4)$ appears in Lean with $W$ written out as `foot (miquelPt …) L₂ - foot (miquelPt …) L₁`; same for $W$ in Theorem 6 (`newton_perp_cr`) and in Theorem 5 (`axis_perp`, through `directrix`/`axisLine`).
- **Starred "orthocentric case" row:** `cov_classical_D3_b`/`cov_classical_D4` are stated for every Poncelet point in the classical sense (any point on all four nine-point circles), not specifically for the orthocentric case. That is more general, so it does cover the row's claim.
- **Dictionary note:** the task brief mentioned `ponPt`; that name is not in the code. The Poncelet formula is `poncelet` (with denominator `ponDen`).

## Overall

- [ ] All thirteen numbered theorems and the five starred rows match. Hand check complete.

Confirmed by: ______________________, date: ______________
