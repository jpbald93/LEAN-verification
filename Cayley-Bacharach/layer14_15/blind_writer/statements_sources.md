# Sources and notes for classical_statements.txt

(Compiled from standard references; no formalisations consulted. Page numbers
are given as best known; section numbers are the reliable locator.)

## CB1 Cayley–Bacharach for cubics
- D. Eisenbud, M. Green, J. Harris, "Cayley–Bacharach theorems and conjectures",
  Bull. AMS 33 (1996), 295–324, §1 (statement attributed to Chasles, labelled
  "CB3" there; their CB1 = Pappus, CB2 = Pascal). https://www.ams.org/journals/bull/1996-33-03/S0273-0979-96-00666-0/
- W. Fulton, *Algebraic Curves* (2008 online ed.), §5.6 "Applications of Noether's
  theorem", Proposition 1 and Corollaries (multiplicity form, CB1(b)).
  https://dept.math.lsa.umich.edu/~wfulton/CurveBook.pdf
- Notes: the textbook form (a) requires the nine intersection points to be
  distinct (equivalently, C1, C2 meet transversally / with no common component).
  Fulton's version allows multiplicities but needs the points to be simple on
  one curve (e.g. C1 irreducible / nonsingular there). Some sources work over
  C or an algebraically closed field; the statement as given holds over any
  field when the nine points are k-rational and distinct.

## CB2 Eight-point criterion
- M. Reid, *Undergraduate Algebraic Geometry*, LMS Student Texts 12 (CUP 1988),
  Ch. I §2 (Lemma/Proposition on dimension of cubics through 8 points: "no 4 on a
  line, no 7 on a conic" ⇒ dim = 2; Corollary: Cayley–Bacharach and Pascal).
- Eisenbud–Green–Harris (op. cit.), §1, discussion of eight points imposing
  independent conditions on cubics.
- Notes: some sources state the hypothesis only as "eight points in general
  position"; the precise condition used by Reid is "no four collinear and no
  seven on a conic". Variant hypotheses: the 8 points are 8 of the 9 points of
  a complete intersection of two cubics (then independence is automatic).

## CB3 Pascal
- H. S. M. Coxeter, *Projective Geometry* (2nd ed., Springer 1987), §9.2–9.3
  (Pascal's theorem, Braikenridge–Maclaurin converse).
- Wikipedia, "Pascal's theorem", https://en.wikipedia.org/wiki/Pascal%27s_theorem ;
  Fulton §5.6 Cor. (derived from Cayley–Bacharach).
- Notes: Pascal's original (Essay pour les coniques, 1640) was for a circle/conic
  section in the real affine plane; projective form avoids parallel-sides cases
  (in the affine plane, "meet" may be at infinity). Degenerate versions allow
  coincident vertices (side replaced by tangent) or a degenerate conic (pair of
  lines → Pappus). Most common form: six distinct points on a nondegenerate conic.

## CB4 Pappus
- Coxeter, *Projective Geometry*, §4.3 (Pappus's theorem); also H. S. M. Coxeter,
  *Introduction to Geometry*, §14.
- Wikipedia, "Pappus's hexagon theorem",
  https://en.wikipedia.org/wiki/Pappus%27s_hexagon_theorem
- Notes: original (Pappus, Collection Book VII) is affine/Euclidean; projective
  form is standard. Pappus holds in a projective plane over a field (it is
  equivalent to commutativity of the coordinatising division ring). Some
  statements omit the condition "none equal to L ∩ M"; it is needed to avoid
  degenerate (undefined) intersections.
