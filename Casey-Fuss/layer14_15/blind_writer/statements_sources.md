# Sources and notes

## CaseyFuss1 — Casey's theorem
- J. Casey, "On the equations and properties ... of the system of circles touching three circles in a plane", Proc. Royal Irish Academy 9 (1866) 396–423 (JSTOR 20488927); also Casey, *A Sequel to the First Six Books of Euclid*, 5th ed. (1888), p. 103.
- R. A. Johnson, *Modern Geometry* (1929) [Dover: *Advanced Euclidean Geometry*], pp. 121–127 (statement pp. 121–122; tangent-type rules p. 125).
- Encyclopedic: https://en.wikipedia.org/wiki/Casey%27s_theorem ; https://mathworld.wolfram.com/CaseysTheorem.html
- Formula t_ij = |K_iK_j| sqrt((R-R_i)(R-R_j))/R: Zacharias (1942), Jber. DMV 52, 79–89, via Bottema, *Topics in Elementary Geometry* (Springer 2008).

Notes:
- Wikipedia states the internal, non-intersecting, cyclic-order form (a) with sign pattern "+ , =". MathWorld states an "iff" with "±" signs and allows the fifth object to be "a circle or a straight line" (the line case is the limit R → ∞).
- Signed vs unsigned: Wikipedia/Johnson handle external tangency by choosing the exterior tangent for "both in or both out" and the interior tangent for "one in, one out". The signed-radius formulation (b) (rho_i = ±r_i, t_ij^2 = d_ij^2 - (rho_i - rho_j)^2) is equivalent to that rule; the sign convention for rho is mine as a compact restatement, not literally quoted. Case of a circle C_i containing Gamma (internal tangency with Gamma inside C_i) is not covered by the usual statements; excluded.
- The converse is stated in Wikipedia ("the circles are tangent to a common circle") and MathWorld ("fifth circle or a straight line").

## CaseyFuss2 — Fuss's theorem
- N. Fuss (1792), Nova Acta Acad. Sci. Petropolitanae (original).
- H. Dörrie, *100 Great Problems of Elementary Mathematics*, Dover (1965), pp. 188–193.
- P. Yiu, *Euclidean Geometry* (1998), pp. 158–164.
- Encyclopedic: https://en.wikipedia.org/wiki/Bicentric_quadrilateral (section "Fuss's theorem"); converse cited there to W. E. Byerly, Annals of Math. 10(3) (1909) 123–128.

Notes: sources require the quadrilateral convex (bicentric = convex with incircle and circumcircle). The converse requires the small circle inside the big one.

## CaseyFuss3 — Poncelet closure (quadrilateral case)
- J.-V. Poncelet, *Traité des propriétés projectives des figures* (1822; 2nd ed. 1865), pp. 311–317.
- Bos, Kers, Oort, Raven, "Poncelet's closure theorem", Expositiones Math. 5 (1987) 289–364.
- Encyclopedic: https://en.wikipedia.org/wiki/Poncelet%27s_closure_theorem ; https://en.wikipedia.org/wiki/Bicentric_quadrilateral ("every point on the circumcircle is the vertex of a bicentric quadrilateral having the same incircle and circumcircle"); MathWorld "Poncelet Transverse".

Notes: The general porism is for two conics (in the complex projective plane, any n ≥ 3); the bicentric-quadrilateral form restricts to two circles, one inside the other, n = 4. Part (b) is the standard combination "Fuss + converse + Poncelet" stated in the Wikipedia bicentric-quadrilateral article.
