# Sources and notes for classical_statements.txt

Statements were written from standard textbook knowledge; no formalisation
was consulted. Page/section numbers are given where known; URLs are
encyclopedic references.

## A1 Desargues's theorem
- H. S. M. Coxeter, *Projective Geometry*, 2nd ed., Springer, 1987/2003,
  §2.3 (Desargues's theorem, stated with its converse/dual).
- H. S. M. Coxeter & S. L. Greitzer, *Geometry Revisited*, MAA, 1967, §3.6
  "Perspective triangles; Desargues's theorem".
- Encyclopedic: https://en.wikipedia.org/wiki/Desargues%27s_theorem
- Original: G. Desargues, published in A. Bosse, *Manière universelle de
  M. Desargues pour pratiquer la perspective* (1648).

Notes. Holds in P^2(K) for every field K (indeed every division ring);
fails in some non-Desarguesian planes, which is why "over a field" matters.
Sources differ on non-degeneracy hypotheses: most require only that the two
triangles be non-degenerate and that corresponding sides be distinct (so
P, Q, R are defined) and corresponding vertices distinct (so AA', BB', CC'
are lines). Some also require O to be distinct from all six vertices and the
triangles to lie in "general position"; these extra conditions are not needed
for the conclusion. (b) is the converse, which is the plane dual of (a).

## A2 Monge's three circles theorem
- Encyclopedic: https://en.wikipedia.org/wiki/Monge%27s_theorem
- E. W. Weisstein, "Monge's Circle Theorem", MathWorld,
  https://mathworld.wolfram.com/MongesCircleTheorem.html
- R. A. Johnson, *Advanced Euclidean Geometry* (Dover, 1960; orig. 1929),
  chapter on homothecy / centres of similitude (§§ on "centres of similitude
  of three circles", the "axes of similitude").

Notes. Popular statement: "for three circles of distinct radii, no one inside
another, the three intersection points of the pairs of external common
tangents are collinear". The "no circle inside another" / "disjoint" condition
only ensures the tangents exist; stated via external homothety centres (as
here) the theorem needs just pairwise unequal radii (and, conventionally,
distinct centres). If radii are equal for a pair, the centre is at infinity
and the theorem holds projectively. If the centres are collinear, the
conclusion is trivial. Signed form: E_ij is the homothety centre with ratio
+r_j/r_i; I_ij with ratio -r_j/r_i. Proof: Menelaus, or homothety
composition, or 3D (cones/plane) argument. (b) is the standard companion
("axes of similitude"; four such lines in total).

## A3 Wallace–Simson line
- Coxeter & Greitzer, *Geometry Revisited*, §2.5 "The Simson line",
  Theorem 2.51 (stated with converse).
- Encyclopedic: https://en.wikipedia.org/wiki/Simson_line
- Historical: first published by William Wallace (1797/1799, *Mathematical
  Repository*); attributed to Robert Simson.

Notes. Feet are on the side *lines* (extended), not segments. Many texts
state it as the "iff" (A3(a)+(b)). If P is a vertex, two feet coincide with
that vertex and the statement holds trivially.

## A4 Napoleon's theorem
- Coxeter & Greitzer, *Geometry Revisited*, §3.3 "Napoleon triangles"
  (Theorem 3.31 and following).
- Encyclopedic: https://en.wikipedia.org/wiki/Napoleon%27s_theorem
- E. W. Weisstein, "Napoleon's Theorem", MathWorld,
  https://mathworld.wolfram.com/NapoleonsTheorem.html

Notes. Usually stated just for outward triangles (A4(a)); the inward version
(A4(b)) is commonly added. Often also stated: both Napoleon triangles share
their centre with the centroid of ABC, and their areas differ by the area of
ABC. "Centre" = centroid = circumcentre of the equilateral triangle. Some
texts phrase it for "a triangle" only (non-degenerate); the outer version
also holds by the complex-number proof for degenerate triangles.

## A5 Lami's theorem
- Encyclopedic: https://en.wikipedia.org/wiki/Lami%27s_theorem
- Original: Bernard Lamy, *Traitez de méchanique, de l'équilibre des solides
  et des liqueurs* (Paris, 1679).
- Standard engineering-mechanics texts, e.g. S. S. Bhavikatti, *Engineering
  Mechanics*, chapter on equilibrium of concurrent forces ("Lami's theorem").

Notes. Requires exactly three coplanar concurrent forces in equilibrium;
textbooks usually add "non-collinear" (if collinear, all sines are 0 and the
statement is vacuous/undefined). Angles are the unsigned angles in [0, pi]
between the force vectors (for equilibrium of three non-collinear forces
they sum to 2*pi). Equivalent to the law of sines applied to the triangle of
forces, since sin(pi - x) = sin x. Some sources phrase it multiplicatively
to avoid division: |F_1| sin(beta) = |F_2| sin(alpha), etc.
