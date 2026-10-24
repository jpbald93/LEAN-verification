# Sources and notes for the TriSimplex classical statements

Sources are standard textbooks, encyclopedias and original papers. These citations were written
from memory without fetching anything (no web lookups were made), so check the page numbers
before relying on them.

## TriSimplex1 — Carnot's theorem
- R. A. Johnson, *Advanced Euclidean Geometry* (Dover, 1960; orig. *Modern Geometry*, 1929), §§ on the circumcircle (signed-distance form; cos A + cos B + cos C = 1 + r/R), around pp. 189–190.
- Wikipedia, "Carnot's theorem (inradius, circumradius)", https://en.wikipedia.org/wiki/Carnot%27s_theorem_(inradius,_circumradius); MathWorld, "Carnot's Theorem", https://mathworld.wolfram.com/CarnotsTheorem.html.
- Original: L. N. M. Carnot, *Géométrie de position* (Paris, 1803).
- Notes: the sign convention is the standard one. A distance is negative iff the segment from O to the foot lies entirely outside the triangle; equivalently d_a = R cos A. In an obtuse triangle exactly one distance is negative; in a right triangle one distance is 0. Some sources state only the acute case with unsigned distances.

## TriSimplex2 — De Gua's theorem
- Wikipedia, "De Gua's theorem", https://en.wikipedia.org/wiki/De_Gua%27s_theorem (trirectangular tetrahedron; n-dimensional generalisation).
- D. R. Conant and W. A. Beyer, "Generalized Pythagorean theorem", *Amer. Math. Monthly* 81 (1974), 262–265 (general form for k-faces of orthogonal simplices).
- Original: J.-P. de Gua de Malves, Mémoire, *Histoire de l'Académie Royale des Sciences* (Paris, 1783). The result was known earlier to Tinseau (1774) and reportedly to Descartes and Faulhaber.
- Notes: the general simplex form is the one with an orthogonal corner (n pairwise orthogonal edges at one vertex). A broader form (Conant–Beyer) uses squared k-volumes of a k-face equal to the sum of squared coordinate projections. Not included here.

## TriSimplex3 — Viviani's theorem
- Wikipedia, "Viviani's theorem", https://en.wikipedia.org/wiki/Viviani%27s_theorem; MathWorld, "Viviani's Theorem", https://mathworld.wolfram.com/VivianisTheorem.html.
- R. Honsberger, *Episodes in Nineteenth and Twentieth Century Euclidean Geometry* (MAA, 1995), p. 37 ff.
- Original: V. Viviani (17th c.).
- Notes: the most common form says "interior point"; it extends to the closed triangle. The signed-distance version holds for all points of the plane.

## TriSimplex4 — Japanese theorem for cyclic polygons
- Wikipedia, "Japanese theorem for cyclic polygons", https://en.wikipedia.org/wiki/Japanese_theorem_for_cyclic_polygons; and "Japanese theorem for cyclic quadrilaterals", https://en.wikipedia.org/wiki/Japanese_theorem_for_cyclic_quadrilaterals.
- H. Fukagawa and D. Pedoe, *Japanese Temple Geometry Problems (Sangaku)* (Charles Babbage Research Centre, Winnipeg, 1989); R. A. Johnson, *Advanced Euclidean Geometry*, p. 193.
- M. Ahuja, W. Uegaki, K. Matsushita, "In search of the Japanese theorem", *Missouri J. Math. Sci.* 18 (2006).
- Notes: sources require a convex cyclic polygon triangulated by diagonals, with no extra vertices. The usual proof reduces the general case to the quadrilateral case via Carnot's theorem, because any two triangulations are connected by diagonal flips. The quadrilateral identity is equivalent to Carnot's theorem applied to the two triangles on each diagonal. The rectangle-of-incentres statement is a separate companion theorem.

## TriSimplex5 — Euler's triangle formula
- H. S. M. Coxeter and S. L. Greitzer, *Geometry Revisited* (MAA, 1967), §1.5, Theorem 1.51, p. 29.
- Wikipedia, "Euler's theorem in geometry", https://en.wikipedia.org/wiki/Euler%27s_theorem_in_geometry.
- Original: W. Chapple, *Miscellanea Curiosa Mathematica* 4 (1746), 117–124; L. Euler, "Solutio facilis problematum quorundam geometricorum difficillimorum", *Novi Comment. Acad. Sci. Imp. Petropol.* 11 (1765/1767), 103–123.
- Notes: holds for every non-degenerate triangle. The corollary R ≥ 2r (Euler's inequality) has equality iff the triangle is equilateral (O = I).

## TriSimplex6 — Poncelet's porism for triangles
- Wikipedia, "Poncelet's closure theorem", https://en.wikipedia.org/wiki/Poncelet%27s_closure_theorem; MathWorld, "Poncelet's Porism", https://mathworld.wolfram.com/PonceletsPorism.html.
- L. Flatto, *Poncelet's Theorem* (AMS, 2009), Ch. 1 (triangle case, Chapple–Euler); V. Dragović and M. Radnović, *Poncelet Porisms and Beyond* (Birkhäuser, 2011).
- Original: J.-V. Poncelet, *Traité des propriétés projectives des figures* (Paris, 1822).
- Notes: the general porism concerns two conics in general position and n-gons. Here it is specialised to two circles, one inside the other, and n = 3. In that case the closure condition is exactly the Chapple–Euler relation d² = R² − 2Rr; Fuss's relation is the n = 4 analogue. Some texts state the porism as "if closure happens for one starting point it happens for all"; others state it as the explicit criterion. Both are included (6a and 6b). Hypothesis variants: projective versions allow general conics, possibly complex; the circle version needs the inner circle strictly inside the outer one.
