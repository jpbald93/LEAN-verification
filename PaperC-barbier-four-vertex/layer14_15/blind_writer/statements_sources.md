# Sources and notes for classical_statements.txt

## C1 Barbier's theorem
- **Original:** E. Barbier, "Note sur le problème de l'aiguille et le jeu du joint couvert",
  *J. Math. Pures Appl.* (2) 5 (1860), 273–286, esp. pp. 283–285.
- **Textbook:** S. R. Lay, *Convex Sets and Their Applications*, Dover 2007, Theorem 11.11,
  pp. 81–82 (general convex sets of constant width, no smoothness).
- **Textbook (smooth form):** M. P. do Carmo, *Differential Geometry of Curves and Surfaces*,
  §1-7 (global properties of plane curves), exercises on the Cauchy–Crofton formula/
  support function: a closed convex curve of constant width a has length πa
  (exercise number from memory; not re-verified online).
- **Encyclopedic:** Wikipedia, "Barbier's theorem",
  https://en.wikipedia.org/wiki/Barbier%27s_theorem ; Martini–Montejano–Oliveros,
  *Bodies of Constant Width*, Birkhäuser 2019.
- **Notes:** The smooth form (C1a) is the differential-geometry textbook version (proof via
  support function p(θ)+p(θ+π)=w and L=∫p dθ). The general form (C1b) is the convex-geometry
  version (proofs: Minkowski sum K+(−K) is a disk of radius w with perimeter 2πw, and
  perimeter is Minkowski-additive; or Cauchy–Crofton formula). Width is sometimes defined
  only via parallel supporting lines; this is equivalent to the support-function definition.
  The degenerate case w = 0 (a point) is excluded by all sources (or trivially L = 0).

## C2 Reuleaux triangle
- Wikipedia, "Reuleaux triangle", https://en.wikipedia.org/wiki/Reuleaux_triangle
  (construction, constant width, perimeter πs, area ½(π−√3)s²).
- V. Klee & S. Wagon, *Old and New Unsolved Problems in Plane Geometry and Number Theory*,
  MAA 1991, p. 21 (intersection of three disks); M. Gardner, *Knots and Borromean Rings,
  Rep-Tiles, and Eight Queens*, CUP 2014, ch. 18, pp. 223–245.
- Notes: the area/Blaschke–Lebesgue part (C2c) is an "often stated alongside" addition, not
  part of Barbier's theorem.

## C3 Four-vertex theorem
- **Original (convex):** S. Mukhopadhyaya, "New methods in the geometry of a plane arc",
  *Bull. Calcutta Math. Soc.* 1 (1909), 21–27.
- **Original (general simple curves):** A. Kneser, "Bemerkungen über die Anzahl der
  Extreme der Krümmung auf geschlossenen Kurven und über verwandte Fragen in einer
  nichteuklidischen Geometrie", *Festschrift Heinrich Weber*, Teubner 1912, pp. 170–180.
- **Textbook:** M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, §1-7,
  "Four-Vertex Theorem": "A simple closed convex curve has at least four vertices";
  vertex defined as a point with k'(s)=0.  Also A. Pressley, *Elementary Differential
  Geometry*, 2nd ed., Springer 2010, §3.1 (four vertex theorem for simple closed curves).
- **Expository proof:** R. Osserman, "The four-or-more vertex theorem", *Amer. Math. Monthly*
  92 (1985), 332–337.
- **Encyclopedic:** Wikipedia, "Four-vertex theorem",
  https://en.wikipedia.org/wiki/Four-vertex_theorem
- **Notes on hypotheses / disagreements:**
  * Vertex: "local extremum of curvature" (Wikipedia, Osserman) vs "k'(s)=0" (do Carmo).
    With k'=0 the count is of critical points; the extremum version is stronger, giving ≥2
    maxima and ≥2 minima. On an arc of constant curvature every point is a vertex.
  * Convexity: "oval" sometimes means strictly convex (k>0); do Carmo says "convex" (k≥0
    allowed in his proof via a line meeting the curve). Kneser's version needs only simple.
  * Smoothness: C² suffices for vertices to make sense (Graustein 1937, Trans. AMS 41,
    9–23 on continuity of curvature); do Carmo works with C^∞ ("differentiable") curves,
    some texts state C³.
  * Signed vs unsigned curvature: for convex curves k has constant sign, so no difference;
    for the general simple-curve form, signed curvature is used.
  * Circle: constant curvature, every point is a vertex (theorem holds trivially).
