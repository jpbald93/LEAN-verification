# Sources and notes for classical_statements.txt

## Conics1-3 (Dandelin spheres, focus-directrix)
- G. P. Dandelin, "Mémoire sur quelques propriétés remarquables de la focale parabolique",
  Nouveaux mémoires de l'Académie royale des sciences et belles-lettres de Bruxelles 2 (1822), 169-200.
- D. Hilbert & S. Cohn-Vossen, *Geometry and the Imagination* (Chelsea, 1952), §1.2, pp. 7-11
  (ellipse via two spheres; directrix via plane of tangency circle).
- Wikipedia, "Dandelin spheres": https://en.wikipedia.org/wiki/Dandelin_spheres
  (statement for ellipse, hyperbola, parabola; directrix as intersection of the
  plane of the tangency circle with the cutting plane).
- Eccentricity e = cos(beta)/cos(alpha) with beta = angle between plane and axis, alpha =
  half-angle: standard (e.g. Wikipedia "Conic section", section "Eccentricity"; also
  Hilbert-Cohn-Vossen). Some sources measure angles from the plane perpendicular to the axis;
  then e = sin(theta)/sin(phi) — the same quantity.
- Planar converse (Conics3c): Pappus (Collection VII); any analytic-geometry text, e.g.
  Wikipedia "Conic section" §"Eccentricity, focus and directrix".

Notes / variants:
- Degenerate sections (plane through apex: point, line, pair of lines) are excluded, as in
  all sources. The circle (plane ⟂ axis) has two coincident "foci" (the centre) and no
  directrix (e = 0); sources usually exclude it from the directrix statement.
- Hyperbola: most sources state the unsigned |XF1 - XF2| = const; signed form holds per branch.
- Many textbooks state only the ellipse case and remark the hyperbola is analogous.

## Conics4 (Steiner inellipse)
- Wikipedia, "Steiner inellipse": https://en.wikipedia.org/wiki/Steiner_inellipse
  (unique ellipse tangent to the sides at their midpoints; centre = centroid; maximal area
  among inscribed ellipses, area ratio pi/(3 sqrt 3)).
- D. Kalman, "An Elementary Proof of Marden's Theorem", Amer. Math. Monthly 115 (2008),
  330-338 (uniqueness of the midpoint-tangent inellipse, via affine image of the incircle
  of an equilateral triangle).
- Weisstein, MathWorld "Steiner Inellipse": https://mathworld.wolfram.com/SteinerInellipse.html
Notes: "inscribed" = tangent to the three side lines inside the triangle; uniqueness holds
already among conics tangent to the three sides at the midpoints (a conic is determined by
3 points + 3 tangents there, overdetermined, and the affine argument gives exactly one).

## Conics5 (Marden's theorem)
- J. Siebeck, "Über eine neue analytische Behandlungweise der Brennpunkte",
  J. reine angew. Math. 64 (1864), 175-182 (original).
- M. Marden, *Geometry of Polynomials*, AMS Math. Surveys 3 (2nd ed. 1966), Theorem 4.1
  (Siebeck), pp. 9-10 (approx.); also M. Marden, "A note on the zeros of the sections of a
  partial fraction", Bull. AMS 51 (1945), 935-940.
- D. Kalman, "The Most Marvelous Theorem in Mathematics", J. Online Math. Appl. 8 (2008);
  Kalman, Amer. Math. Monthly 115 (2008), 330-338.
- Wikipedia, "Marden's theorem": https://en.wikipedia.org/wiki/Marden%27s_theorem
Notes: Hypothesis is that the vertices are not collinear (Wikipedia/Kalman). Equilateral
case: double critical point = centre of the incircle (= Steiner inellipse); "foci" coincide.
Some sources add: the centroid (midpoint of the foci) is the root of p''.
