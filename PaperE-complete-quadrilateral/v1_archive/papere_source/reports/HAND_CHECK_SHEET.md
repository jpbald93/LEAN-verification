# Paper E — hand check sheet (for Josh)

**What to do:** for each row, read the paper's theorem (top) and the Lean statement (below it). Tick ✅ if the Lean says the same thing as the paper — same objects, every hypothesis in the paper appears in the Lean and vice versa, same conclusion. Write a note if anything looks different, even slightly. You do not need to read any proofs.

Each Lean statement links to the exact line on GitHub at the published commit.

**Dictionary** (the paper's Section 2 defines these):
- `meet L₁ L₂` = the intersection point A₁₂ of lines L₁ and L₂. So `meet L₁ L₂`, `meet L₁ L₃`, `meet L₂ L₃` are the vertices of triangle T₄ (the triangle *not* using L₄).
- `ortho a b c` = orthocentre of triangle abc; `circ a b c` = circumcentre; `foot z L` = foot of the perpendicular from z to line L.
- `miquelPt L₁ L₂ L₃ L₄` = the Miquel point M (explicit formula in the paper).
- `pw z P Q` = power of z with respect to the circle with diameter PQ.
- `GenPos L₁ L₂ L₃ L₄` = "general position": no two lines parallel, no three through one point.
- `Collinear ℝ {…}` = "on one line"; `Cospherical {…}` = "on one circle"; `Metric.sphere c r` = the circle with centre c, radius r; `dist a b` = distance.
- `line[ℝ, P, Q]` = the line through P and Q; `affineSpan ℝ {…}` = the smallest line/plane containing the points; `.Parallel` = parallel.
- `(x).re` = real part; `conj` / `starRingEnd ℂ` = complex conjugate; `≠` = not equal; `¬` = not; `∧` = and; `∨` = or.

---

## NEWTON-GAUSS — paper says

If $L_1,\dots,L_4$ are in general position, the midpoints of the three diagonals are collinear; and the midpoints of $A_{12}A_{34}$ and $A_{13}A_{24}$ are distinct.

### Lean: `newton_gauss` — [QuadNewton/Quad.lean:53](https://github.com/jpbald93/quadnewton/blob/48e94cf944b3dfbcca7358360a064e39b6336d98/QuadNewton/Quad.lean#L53)

```lean
theorem newton_gauss (h : GenPos L₁ L₂ L₃ L₄) :
    Collinear ℝ {(meet L₁ L₂ + meet L₃ L₄) / 2, (meet L₁ L₃ + meet L₂ L₄) / 2,
      (meet L₁ L₄ + meet L₂ L₃) / 2} := …
```

### Lean: `diag_midpoints_ne` — [QuadNewton/Quad.lean:70](https://github.com/jpbald93/quadnewton/blob/48e94cf944b3dfbcca7358360a064e39b6336d98/QuadNewton/Quad.lean#L70)

```lean
theorem diag_midpoints_ne (h : GenPos L₁ L₂ L₃ L₄) :
    (meet L₁ L₂ + meet L₃ L₄) / 2 ≠ (meet L₁ L₃ + meet L₂ L₄) / 2 := …
```

- [x] matches the paper

---

## ORTHOCENTRE LINE — paper says

If $L_1,\dots,L_4$ are in general position, the orthocentres $H_1,\dots,H_4$ of $T_1,\dots,T_4$ are collinear, and they are not all equal: $H_3\neq H_4$ or $H_2\neq H_4$.

### Lean: `orthocentres_collinear` — [QuadNewton/Quad.lean:79](https://github.com/jpbald93/quadnewton/blob/48e94cf944b3dfbcca7358360a064e39b6336d98/QuadNewton/Quad.lean#L79)

```lean
theorem orthocentres_collinear (h : GenPos L₁ L₂ L₃ L₄) :
    Collinear ℝ {ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} := …
```

### Lean: `orthocentres_not_all_eq` — [QuadNewton/Quad.lean:97](https://github.com/jpbald93/quadnewton/blob/48e94cf944b3dfbcca7358360a064e39b6336d98/QuadNewton/Quad.lean#L97)

```lean
theorem orthocentres_not_all_eq (h : GenPos L₁ L₂ L₃ L₄) :
    ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄) ≠ ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∨
    ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) ≠ ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) := …
```

- [x] matches the paper

---

## GAUSS-BODENMILLER — paper says

If $L_1,\dots,L_4$ are in general position, each orthocentre $H_k$ has the same power with respect to the three circles having the diagonals as diameters.

### Lean: `bodenmiller` — [QuadNewton/Quad.lean:135](https://github.com/jpbald93/quadnewton/blob/48e94cf944b3dfbcca7358360a064e39b6336d98/QuadNewton/Quad.lean#L135)

```lean
theorem bodenmiller (h : GenPos L₁ L₂ L₃ L₄) :
    ∀ H ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
      pw H (meet L₁ L₂) (meet L₃ L₄) = pw H (meet L₁ L₃) (meet L₂ L₄) ∧
      pw H (meet L₁ L₂) (meet L₃ L₄) = pw H (meet L₁ L₄) (meet L₂ L₃) := …
```

- [x] matches the paper

---

## PERPENDICULARITY — paper says

If $L_1,\dots,L_4$ are in general position, then for any two orthocentres $H,H'$, $\operatorname{Re}\big((m_2-m_1)\overline{(H'-H)}\big)=0$, where $m_1,m_2$ are the midpoints of $A_{12}A_{34}$ and $A_{13}A_{24}$.

### Lean: `orthocentre_line_perp` — [QuadNewton/Quad.lean:155](https://github.com/jpbald93/quadnewton/blob/48e94cf944b3dfbcca7358360a064e39b6336d98/QuadNewton/Quad.lean#L155)

```lean
theorem orthocentre_line_perp (h : GenPos L₁ L₂ L₃ L₄) :
    ∀ H₁ ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
    ∀ H₂ ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
      (((meet L₁ L₃ + meet L₂ L₄) / 2 - (meet L₁ L₂ + meet L₃ L₄) / 2) * conj (H₂ - H₁)).re = 0 := …
```

- [x] matches the paper

---

## MIQUEL POINT — paper says

If $L_1,\dots,L_4$ are in general position, $M$ lies on the circumcircle of each of $T_1,\dots,T_4$ (the circle with centre $\operatorname{circ}(T_k)$ through the vertices of $T_k$).

### Lean: `miquel` — [QuadMiquel/Miquel.lean:162](https://github.com/jpbald93/quadmiquel/blob/011c9ecd5276b7abaf2b42a8f5ba463196df123d/QuadMiquel/Miquel.lean#L162)

```lean
theorem miquel {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
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

## STEINER CIRCLE — paper says

If $L_1,\dots,L_4$ are in general position, the four circumcentres $\operatorname{circ}(T_1),\dots, \operatorname{circ}(T_4)$ and $M$ are cospherical (lie on one circle).

### Lean: `steiner_circle` — [QuadMiquel/Miquel.lean:200](https://github.com/jpbald93/quadmiquel/blob/011c9ecd5276b7abaf2b42a8f5ba463196df123d/QuadMiquel/Miquel.lean#L200)

```lean
theorem steiner_circle {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    EuclideanGeometry.Cospherical
      ({circ (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄), circ (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
        circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄), circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃),
        miquelPt L₁ L₂ L₃ L₄} : Set ℂ) := …
```

- [x] matches the paper

---

## SIMSON LINE — paper says

If $L_1,\dots,L_4$ are in general position, the feet of the perpendiculars from $M$ to $L_1,\dots,L_4$ are collinear.

### Lean: `simson` — [QuadMiquel/Simson.lean:155](https://github.com/jpbald93/quadmiquel/blob/011c9ecd5276b7abaf2b42a8f5ba463196df123d/QuadMiquel/Simson.lean#L155)

```lean
theorem simson {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    Collinear ℝ ({foot (miquelPt L₁ L₂ L₃ L₄) L₁, foot (miquelPt L₁ L₂ L₃ L₄) L₂,
      foot (miquelPt L₁ L₂ L₃ L₄) L₃, foot (miquelPt L₁ L₂ L₃ L₄) L₄} : Set ℂ) := …
```

- [x] matches the paper

---

## STEINER PARALLEL — paper says

If $L_1,\dots,L_4$ are in general position, with $F_k$ the foot of the perpendicular from $M$ to $L_k$, the line through $F_1$ and $F_2$ is parallel to the affine span of the four orthocentres $H_1,\dots,H_4$.

### Lean: `steiner_parallel_line` — [QuadMiquel/Parallel.lean:241](https://github.com/jpbald93/quadmiquel/blob/011c9ecd5276b7abaf2b42a8f5ba463196df123d/QuadMiquel/Parallel.lean#L241)

```lean
theorem steiner_parallel_line {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    line[ℝ, foot (miquelPt L₁ L₂ L₃ L₄) L₁, foot (miquelPt L₁ L₂ L₃ L₄) L₂].Parallel
      (affineSpan ℝ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
        ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
        ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
        ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ)) := …
```

- [x] matches the paper

---

## Overall

- [x] All eight match. Hand check complete.

Confirmed by Josh Bald, 15 October 2026, 22:07 ET ("The handcheck is done").
