# Sources and notes for classical_statements.txt

## Citations
- **Pascal1** — B. Pascal, *Essay pour les coniques* (1640); English transl. in D. E. Smith,
  *A Source Book in Mathematics* (1959), p. 326. Modern projective form: H. S. M. Coxeter,
  *Projective Geometry*, 2nd ed., Springer 1987, Ch. 9 (Pascal and Brianchon theorems);
  Coxeter & Greitzer, *Geometry Revisited* (1967), p. 76.
  Encyclopedic: https://en.wikipedia.org/wiki/Pascal%27s_theorem
- **Pascal2(b) (Pappus)** — same Wikipedia page ("degenerate conic of two lines with three points on each line").
- **Pascal3** — Braikenridge–Maclaurin theorem (converse), cited on the Wikipedia page above.
- **Brianchon1** — C. J. Brianchon, "Mémoire sur les surfaces courbes du second degré",
  J. École Polytechnique 6 (1806), 297–311. Coxeter, *Projective Geometry*, 2nd ed., Theorem 9.15, p. 83.
  Encyclopedic: https://en.wikipedia.org/wiki/Brianchon%27s_theorem

## Notes on hypotheses / variants
- Most common modern form: projective plane, non-degenerate conic, six distinct points
  (resp. six distinct tangents). Over a non-degenerate conic, distinct points imply no three
  collinear, so opposite sides are distinct lines and the three intersection points are well defined.
- Field: classical sources work over R (or C); the projective proof (via Pappus / cross-ratio)
  works over any (commutative) field for Pascal. Pappus's theorem itself characterises commutativity
  of the coordinate division ring.
- Brianchon in characteristic 2: all tangents of a non-degenerate conic pass through one point (the
  nucleus), so a "circumscribed hexagon" degenerates; hence the char != 2 hypothesis (the dual
  argument via the polarity needs char != 2). Pascal1 needs no such hypothesis.
- Euclidean/affine form: opposite sides may be parallel; then the Pascal line is parallel to them,
  or is the line at infinity if two (hence all three) pairs are parallel. Projective form avoids this.
- Degenerate cases (coincident consecutive vertices -> tangent line; Pappus for a line pair) are
  usually stated as corollaries/limits, not as part of the main theorem. "Signed vs unsigned" and
  "circle or line" issues do not arise for these theorems.
- Order of vertices: the hexagon may be self-intersecting; any order of the six points is allowed.
