import Mathlib

open Complex

noncomputable section

/-! ## The model (shared by both parts) -/

/-- `cr(a,b) = Im(ā b)`. -/
def BlindCr (a b : ℂ) : ℝ := (starRingEnd ℂ a * b).im

/-- A line `L = (p,d)`: point and direction. -/
structure BlindLine where
  p : ℂ
  d : ℂ

/-- Carrier of `L = (p,d)`: `{z : cr(d, z - p) = 0}`. -/
def BlindLine.carrier (L : BlindLine) : Set ℂ := {z | BlindCr L.d (z - L.p) = 0}

/-- Intersection point of `L = (p,d)` and `M = (q,e)`: `p + (cr(e,q-p)/cr(e,d)) d`. -/
def BlindMeet (L M : BlindLine) : ℂ :=
  L.p + ((BlindCr M.d (M.p - L.p) / BlindCr M.d L.d : ℝ) : ℂ) * L.d

/-- Circumcentre by an explicit formula (the prose does not spell it out): with `u = b - a`,
`v = c - a`, centre `a - i (|u|² v - |v|² u) / (2 cr(u,v))`. -/
def BlindCirc (a b c : ℂ) : ℂ :=
  a + (-Complex.I) * ((Complex.normSq (b - a) : ℂ) * (c - a) - (Complex.normSq (c - a) : ℂ) * (b - a))
    / (2 * (BlindCr (b - a) (c - a) : ℂ))

/-- `ortho(a,b,c) = a + b + c - 2 circ(a,b,c)`. -/
def BlindOrtho (a b c : ℂ) : ℂ := a + b + c - 2 * BlindCirc a b c

/-- `foot(z,L) = p + Re(d̄ (z-p)) / |d|² · d`. -/
def BlindFoot (z : ℂ) (L : BlindLine) : ℂ :=
  L.p + (((starRingEnd ℂ L.d * (z - L.p)).re / Complex.normSq L.d : ℝ) : ℂ) * L.d

/-- `refl(z,L) = 2 foot(z,L) - z`. -/
def BlindRefl (z : ℂ) (L : BlindLine) : ℂ := 2 * BlindFoot z L - z

/-- `lineThrough p q = (p, q - p)`. -/
def BlindLineThrough (p q : ℂ) : BlindLine := ⟨p, q - p⟩

/-- Midpoint, as the average. -/
def BlindMid (a b : ℂ) : ℂ := (a + b) / 2

/-- Circumcircle membership: `z` is at distance `dist a (circ a b c)` from `circ a b c`. -/
def BlindOnCircumcircle (a b c z : ℂ) : Prop :=
  dist z (BlindCirc a b c) = dist a (BlindCirc a b c)

/-- `OnParabola f S z :⇔ dist z f = infDist z S`. -/
def BlindOnParabola (f : ℂ) (S : AffineSubspace ℝ ℂ) (z : ℂ) : Prop :=
  dist z f = Metric.infDist z (S : Set ℂ)

/-- `Tangent L f S`: exactly one point of `L` is equidistant from `f` and `S`. -/
def BlindTangent (L : BlindLine) (f : ℂ) (S : AffineSubspace ℝ ℂ) : Prop :=
  ∃! z, z ∈ L.carrier ∧ BlindOnParabola f S z

/-- General position of four lines: directions nonzero, no two parallel, no three concurrent. -/
def BlindGenPos (L1 L2 L3 L4 : BlindLine) : Prop :=
  (L1.d ≠ 0 ∧ L2.d ≠ 0 ∧ L3.d ≠ 0 ∧ L4.d ≠ 0) ∧
  (BlindCr L1.d L2.d ≠ 0 ∧ BlindCr L1.d L3.d ≠ 0 ∧ BlindCr L1.d L4.d ≠ 0 ∧
   BlindCr L2.d L3.d ≠ 0 ∧ BlindCr L2.d L4.d ≠ 0 ∧ BlindCr L3.d L4.d ≠ 0) ∧
  ((∀ z, ¬ (z ∈ L1.carrier ∧ z ∈ L2.carrier ∧ z ∈ L3.carrier)) ∧
   (∀ z, ¬ (z ∈ L1.carrier ∧ z ∈ L2.carrier ∧ z ∈ L4.carrier)) ∧
   (∀ z, ¬ (z ∈ L1.carrier ∧ z ∈ L3.carrier ∧ z ∈ L4.carrier)) ∧
   (∀ z, ¬ (z ∈ L2.carrier ∧ z ∈ L3.carrier ∧ z ∈ L4.carrier)))

/-! ## Part A: four lines / the inscribed parabola -/

section PartA

/-- Four lines (a quadrilateral). -/
structure BlindQuadrilateral where
  L1 : BlindLine
  L2 : BlindLine
  L3 : BlindLine
  L4 : BlindLine

namespace BlindQuadrilateral
variable (Q : BlindQuadrilateral)

/-- General position of the four lines. -/
def GenPos : Prop := BlindGenPos Q.L1 Q.L2 Q.L3 Q.L4

/-- Vertices `A_ij = meet(L_i, L_j)`. -/
def A12 : ℂ := BlindMeet Q.L1 Q.L2
def A13 : ℂ := BlindMeet Q.L1 Q.L3
def A14 : ℂ := BlindMeet Q.L1 Q.L4
def A23 : ℂ := BlindMeet Q.L2 Q.L3
def A24 : ℂ := BlindMeet Q.L2 Q.L4
def A34 : ℂ := BlindMeet Q.L3 Q.L4

/-- Triangles `T_k` of the three vertices not on `L_k`. -/
def T1 : ℂ × ℂ × ℂ := (Q.A23, Q.A24, Q.A34)
def T2 : ℂ × ℂ × ℂ := (Q.A13, Q.A14, Q.A34)
def T3 : ℂ × ℂ × ℂ := (Q.A12, Q.A14, Q.A24)
def T4 : ℂ × ℂ × ℂ := (Q.A12, Q.A13, Q.A23)

/-- Orthocentres `H_k` of `T_k`. -/
def H1 : ℂ := BlindOrtho Q.T1.1 Q.T1.2.1 Q.T1.2.2
def H2 : ℂ := BlindOrtho Q.T2.1 Q.T2.2.1 Q.T2.2.2
def H3 : ℂ := BlindOrtho Q.T3.1 Q.T3.2.1 Q.T3.2.2
def H4 : ℂ := BlindOrtho Q.T4.1 Q.T4.2.1 Q.T4.2.2

/-- The Miquel point. The paper only says "given by an explicit formula"; we use the second
intersection of the circumcircles of `T_3` and `T_4` (both pass through `A_12`), i.e. the
reflection of `A_12` in the line of their centres. -/
def M : ℂ :=
  BlindRefl Q.A12 ⟨BlindCirc Q.T3.1 Q.T3.2.1 Q.T3.2.2,
    BlindCirc Q.T4.1 Q.T4.2.1 Q.T4.2.2 - BlindCirc Q.T3.1 Q.T3.2.1 Q.T3.2.2⟩

/-- Feet `F_k = foot(M, L_k)`. -/
def F1 : ℂ := BlindFoot Q.M Q.L1
def F2 : ℂ := BlindFoot Q.M Q.L2
def F3 : ℂ := BlindFoot Q.M Q.L3
def F4 : ℂ := BlindFoot Q.M Q.L4

/-- `W = F_2 - F_1`, direction of the Simson line. -/
def W : ℂ := Q.F2 - Q.F1

/-- Reflections `R_k = refl(M, L_k)`. -/
def R1 : ℂ := BlindRefl Q.M Q.L1
def R2 : ℂ := BlindRefl Q.M Q.L2
def R3 : ℂ := BlindRefl Q.M Q.L3
def R4 : ℂ := BlindRefl Q.M Q.L4

/-- The orthocentre line, `line[H_4, H_4 + W]`. -/
def OrthoLine : AffineSubspace ℝ ℂ := line[ℝ, Q.H4, Q.H4 + Q.W]

/-- The directrix as a `Line`: `(H_4, W)`. -/
def Directrix : BlindLine := ⟨Q.H4, Q.W⟩

/-- `contact L W R = p + Re(W̄ (R - p)) / Re(W̄ d) · d`. -/
def contact (L : BlindLine) (W R : ℂ) : ℂ :=
  L.p + (((starRingEnd ℂ W * (R - L.p)).re / (starRingEnd ℂ W * L.d).re : ℝ) : ℂ) * L.d

/-- Point of contact `tanPt L = contact L W (refl(M, L))`. -/
def tanPt (L : BlindLine) : ℂ := contact L Q.W (BlindRefl Q.M L)

/-- The axis `(M, i W)`. -/
def Axis : BlindLine := ⟨Q.M, Complex.I * Q.W⟩

/-- The vertex `V = ½ (M + foot(M, directrix))`. -/
def V : ℂ := (1 / 2 : ℂ) * (Q.M + BlindFoot Q.M Q.Directrix)

/-- Midpoints of the diagonals `A12 A34`, `A13 A24`, `A14 A23`. -/
def N1 : ℂ := BlindMid Q.A12 Q.A34
def N2 : ℂ := BlindMid Q.A13 Q.A24
def N3 : ℂ := BlindMid Q.A14 Q.A23

end BlindQuadrilateral

open BlindQuadrilateral

-- thm:refl: "Let R_k = refl(M, L_k). Then each R_k lies on the orthocentre line, and
-- {R_1,R_2,R_3,R_4} is collinear."  (part 1: membership)
theorem blind_1 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    Q.R1 ∈ Q.OrthoLine ∧ Q.R2 ∈ Q.OrthoLine ∧ Q.R3 ∈ Q.OrthoLine ∧ Q.R4 ∈ Q.OrthoLine := by
  sorry

-- thm:refl (part 2: collinearity)
theorem blind_2 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    Collinear ℝ ({Q.R1, Q.R2, Q.R3, Q.R4} : Set ℂ) := by
  sorry

-- thm:refl (part 3: "Moreover, for each k, cr(H_i - H_4, R_k - H_4) = 0 for i = 1,2,3.")
theorem blind_3 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    ∀ r ∈ ({Q.R1, Q.R2, Q.R3, Q.R4} : Set ℂ), ∀ H ∈ ({Q.H1, Q.H2, Q.H3} : Set ℂ),
      BlindCr (H - Q.H4) (r - Q.H4) = 0 := by
  sorry

-- thm:off: "M is not on the orthocentre line: cr(W, M - H_4) ≠ 0."
theorem blind_4 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    BlindCr Q.W (Q.M - Q.H4) ≠ 0 := by
  sorry

-- thm:tangent: "For each L ∈ {L_1,...,L_4}, Tangent L M (orthocentre line): exactly one point
-- of L is equidistant from M and from the orthocentre line."
theorem blind_5 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    BlindTangent Q.L1 Q.M Q.OrthoLine ∧ BlindTangent Q.L2 Q.M Q.OrthoLine ∧
    BlindTangent Q.L3 Q.M Q.OrthoLine ∧ BlindTangent Q.L4 Q.M Q.OrthoLine := by
  sorry

-- thm:tanpt: "For each L ∈ {L_1,...,L_4}: tanPt L is on L, it is on the parabola with focus M and
-- directrix the orthocentre line, and every point of L on that parabola equals tanPt L."
theorem blind_6 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    ∀ L ∈ ({Q.L1, Q.L2, Q.L3, Q.L4} : Set BlindLine),
      Q.tanPt L ∈ L.carrier ∧ BlindOnParabola Q.M Q.OrthoLine (Q.tanPt L) ∧
      ∀ z ∈ L.carrier, BlindOnParabola Q.M Q.OrthoLine z → z = Q.tanPt L := by
  sorry

-- thm:vertex: "The vertex V is on the parabola; dist(V,M) = ½ infDist(M, orthocentre line);
-- and for every point z on the parabola, infDist(V, orthocentre line) ≤ infDist(z, orthocentre line)."
theorem blind_7 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    BlindOnParabola Q.M Q.OrthoLine Q.V ∧
    dist Q.V Q.M = (1 / 2) * Metric.infDist Q.M (Q.OrthoLine : Set ℂ) ∧
    ∀ z, BlindOnParabola Q.M Q.OrthoLine z →
      Metric.infDist Q.V (Q.OrthoLine : Set ℂ) ≤ Metric.infDist z (Q.OrthoLine : Set ℂ) := by
  sorry

-- thm:vertex (second sentence: "The vertex is on the axis, and the axis is perpendicular to the
-- directrix: Re(conj(iW) · W) = 0.")
theorem blind_8 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    Q.V ∈ Q.Axis.carrier ∧ (starRingEnd ℂ (Complex.I * Q.W) * Q.W).re = 0 := by
  sorry

-- thm:newton: "Let N_1,N_2,N_3 be the midpoints of the diagonals A_12A_34, A_13A_24, A_14A_23.
-- For all x,y on the orthocentre line, ⟨x-y, N_2-N_1⟩ = 0 and [...]"
-- AMBIGUOUS: the prose is truncated after "and"; we read the missing conjunct as
-- ⟨x-y, N_3-N_1⟩ = 0.  (Other reading: only ⟨x-y, N_2-N_1⟩ = 0.)
theorem blind_9 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    ∀ x ∈ Q.OrthoLine, ∀ y ∈ Q.OrthoLine,
      inner ℝ (x - y) (Q.N2 - Q.N1) = 0 ∧ inner ℝ (x - y) (Q.N3 - Q.N1) = 0 := by
  sorry

-- thm:newton ("Also ⟨W, N_2 - N_1⟩ = ⟨W, N_3 - N_1⟩ = 0.")
theorem blind_10 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    inner ℝ Q.W (Q.N2 - Q.N1) = 0 ∧ inner ℝ Q.W (Q.N3 - Q.N1) = 0 := by
  sorry

-- thm:lambert: "Each of L_1,...,L_4 is tangent to the parabola with focus M and directrix the
-- orthocentre line, and M lies on the circumcircle of each of T_1,...,T_4."
theorem blind_11 (Q : BlindQuadrilateral) (h : Q.GenPos) :
    (BlindTangent Q.L1 Q.M Q.OrthoLine ∧ BlindTangent Q.L2 Q.M Q.OrthoLine ∧
      BlindTangent Q.L3 Q.M Q.OrthoLine ∧ BlindTangent Q.L4 Q.M Q.OrthoLine) ∧
    (BlindOnCircumcircle Q.T1.1 Q.T1.2.1 Q.T1.2.2 Q.M ∧
     BlindOnCircumcircle Q.T2.1 Q.T2.2.1 Q.T2.2.2 Q.M ∧
     BlindOnCircumcircle Q.T3.1 Q.T3.2.1 Q.T3.2.2 Q.M ∧
     BlindOnCircumcircle Q.T4.1 Q.T4.2.1 Q.T4.2.2 Q.M) := by
  sorry

end PartA

/-! ## Part B: four points / the Poncelet point -/

section PartB

/-- `QGen a b c d`: no three collinear, via the four `cr` conditions. -/
def BlindQGen (a b c d : ℂ) : Prop :=
  BlindCr (b - a) (c - a) ≠ 0 ∧ BlindCr (b - a) (d - a) ≠ 0 ∧
  BlindCr (c - a) (d - a) ≠ 0 ∧ BlindCr (c - b) (d - b) ≠ 0

/-- `ponDen a b c d = p_D`, in the frame `x = a-d`, `y = b-d`, `z = c-d`, `X,Y,Z` their conjugates. -/
def BlindPonDen (a b c d : ℂ) : ℂ :=
  let x := a - d
  let y := b - d
  let z := c - d
  let X := starRingEnd ℂ x
  let Y := starRingEnd ℂ y
  let Z := starRingEnd ℂ z
  X ^ 2 * Y * z - X ^ 2 * Z * y - X * Y ^ 2 * z + X * Z ^ 2 * y + Y ^ 2 * Z * x - Y * Z ^ 2 * x

/-- `p_N`. -/
def BlindPonNum (a b c d : ℂ) : ℂ :=
  let x := a - d
  let y := b - d
  let z := c - d
  let X := starRingEnd ℂ x
  let Y := starRingEnd ℂ y
  let Z := starRingEnd ℂ z
  X ^ 2 * Y * z ^ 2 - X ^ 2 * Z * y ^ 2 - X * Y ^ 2 * z ^ 2 + X * Z ^ 2 * y ^ 2
    + Y ^ 2 * Z * x ^ 2 - Y * Z ^ 2 * x ^ 2

/-- The Poncelet point `P = d + p_N / (2 p_D)`. -/
def BlindPoncelet (a b c d : ℂ) : ℂ := d + BlindPonNum a b c d / (2 * BlindPonDen a b c d)

/-- Nine-point centre `½ (x + y + z - circ(x,y,z))`. -/
def BlindNinePt (x y z : ℂ) : ℂ := (1 / 2 : ℂ) * (x + y + z - BlindCirc x y z)

/-- Nine-point circle of the triangle `(a,b,c)`: centre `ninePt`, through the side midpoint of `ab`. -/
def BlindNineCircle (a b c : ℂ) : Set ℂ :=
  Metric.sphere (BlindNinePt a b c) (dist (BlindMid a b) (BlindNinePt a b c))

/-- Diagonal point `diagPt p q r s = meet (lineThrough p q) (lineThrough r s)`. -/
def BlindDiagPt (p q r s : ℂ) : ℂ := BlindMeet (BlindLineThrough p q) (BlindLineThrough r s)

-- thm:ortho: "If QGen a b c d, then ponDen a b c d = 0 if and only if d = ortho(a,b,c)."
theorem blind_12 (a b c d : ℂ) (h : BlindQGen a b c d) :
    BlindPonDen a b c d = 0 ↔ d = BlindOrtho a b c := by
  sorry

-- thm:ortho ("In that case the four nine-point centres are equal, and the four nine-point
-- circles of the triangles are equal.")
theorem blind_13 (a b c d : ℂ) (h : BlindQGen a b c d) (hd : d = BlindOrtho a b c) :
    (BlindNinePt a b c = BlindNinePt a b d ∧ BlindNinePt a b c = BlindNinePt a c d ∧
      BlindNinePt a b c = BlindNinePt b c d) ∧
    (BlindNineCircle a b c = BlindNineCircle a b d ∧ BlindNineCircle a b c = BlindNineCircle a c d ∧
      BlindNineCircle a b c = BlindNineCircle b c d) := by
  sorry

-- thm:ortho ("For example a = 0, b = 4, c = 1+2i, d = 1+(3/2)i satisfy QGen, d = ortho(a,b,c)
-- and ponDen a b c d = 0.")
theorem blind_14 :
    BlindQGen 0 4 (1 + 2 * Complex.I) (1 + (3 / 2 : ℂ) * Complex.I) ∧
    (1 + (3 / 2 : ℂ) * Complex.I) = BlindOrtho 0 4 (1 + 2 * Complex.I) ∧
    BlindPonDen 0 4 (1 + 2 * Complex.I) (1 + (3 / 2 : ℂ) * Complex.I) = 0 := by
  sorry

-- thm:nine: "If QGen a b c d and d ≠ ortho(a,b,c), then P lies on nine-point circle of each of
-- the four triangles."
theorem blind_15 (a b c d : ℂ) (h : BlindQGen a b c d) (hd : d ≠ BlindOrtho a b c) :
    BlindPoncelet a b c d ∈ BlindNineCircle a b c ∧ BlindPoncelet a b c d ∈ BlindNineCircle a b d ∧
    BlindPoncelet a b c d ∈ BlindNineCircle a c d ∧ BlindPoncelet a b c d ∈ BlindNineCircle b c d := by
  sorry

-- thm:unique: "Under the same hypotheses, any point on the nine-point circles of (a,b,c), (a,b,d)
-- and (a,c,d) equals P."
theorem blind_16 (a b c d : ℂ) (h : BlindQGen a b c d) (hd : d ≠ BlindOrtho a b c) :
    ∀ z, z ∈ BlindNineCircle a b c → z ∈ BlindNineCircle a b d → z ∈ BlindNineCircle a c d →
      z = BlindPoncelet a b c d := by
  sorry

-- thm:pedal: "If QGen a b c d, d ≠ ortho(a,b,c), and {a,b,c,d} is not concyclic, then for each of
-- the four points v, the feet of the perpendiculars from v to the three sides of the triangle of the
-- other three points, together with P, are cospherical."   (case v = d: sides ab, bc, ca)
theorem blind_17 (a b c d : ℂ) (h : BlindQGen a b c d) (hd : d ≠ BlindOrtho a b c)
    (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical
      ({BlindFoot d (BlindLineThrough a b), BlindFoot d (BlindLineThrough b c),
        BlindFoot d (BlindLineThrough c a), BlindPoncelet a b c d} : Set ℂ) := by
  sorry

-- thm:pedal (case v = c: sides ab, bd, da)
theorem blind_18 (a b c d : ℂ) (h : BlindQGen a b c d) (hd : d ≠ BlindOrtho a b c)
    (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical
      ({BlindFoot c (BlindLineThrough a b), BlindFoot c (BlindLineThrough b d),
        BlindFoot c (BlindLineThrough d a), BlindPoncelet a b c d} : Set ℂ) := by
  sorry

-- thm:pedal (case v = b: sides ac, cd, da)
theorem blind_19 (a b c d : ℂ) (h : BlindQGen a b c d) (hd : d ≠ BlindOrtho a b c)
    (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical
      ({BlindFoot b (BlindLineThrough a c), BlindFoot b (BlindLineThrough c d),
        BlindFoot b (BlindLineThrough d a), BlindPoncelet a b c d} : Set ℂ) := by
  sorry

-- thm:pedal (case v = a: sides bc, cd, db)
theorem blind_20 (a b c d : ℂ) (h : BlindQGen a b c d) (hd : d ≠ BlindOrtho a b c)
    (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical
      ({BlindFoot a (BlindLineThrough b c), BlindFoot a (BlindLineThrough c d),
        BlindFoot a (BlindLineThrough d b), BlindPoncelet a b c d} : Set ℂ) := by
  sorry

-- thm:diag: "If QGen a b c d, d ≠ ortho(a,b,c), and none of the three pairs of opposite sides is
-- parallel, then the three diagonal points ab∩cd, ac∩bd, ad∩bc and P are cospherical."
theorem blind_21 (a b c d : ℂ) (h : BlindQGen a b c d) (hd : d ≠ BlindOrtho a b c)
    (h1 : ¬ (line[ℝ, a, b]).Parallel (line[ℝ, c, d]))
    (h2 : ¬ (line[ℝ, a, c]).Parallel (line[ℝ, b, d]))
    (h3 : ¬ (line[ℝ, a, d]).Parallel (line[ℝ, b, c])) :
    EuclideanGeometry.Cospherical
      ({BlindDiagPt a b c d, BlindDiagPt a c b d, BlindDiagPt a d b c,
        BlindPoncelet a b c d} : Set ℂ) := by
  sorry

-- thm:s4: "If QGen a b c d and d ≠ ortho(a,b,c), then poncelet a b c d equals poncelet applied to
-- (a,c,b,d), (b,c,a,d), (a,b,d,c), (d,b,c,a), (a,d,c,b) and (b,c,d,a)."
theorem blind_22 (a b c d : ℂ) (h : BlindQGen a b c d) (hd : d ≠ BlindOrtho a b c) :
    BlindPoncelet a b c d = BlindPoncelet a c b d ∧
    BlindPoncelet a b c d = BlindPoncelet b c a d ∧
    BlindPoncelet a b c d = BlindPoncelet a b d c ∧
    BlindPoncelet a b c d = BlindPoncelet d b c a ∧
    BlindPoncelet a b c d = BlindPoncelet a d c b ∧
    BlindPoncelet a b c d = BlindPoncelet b c d a := by
  sorry

-- thm:s4 ("Moreover, under QGen a b c d, d = ortho(a,b,c) ⇔ c = ortho(a,b,d).")
theorem blind_23 (a b c d : ℂ) (h : BlindQGen a b c d) :
    d = BlindOrtho a b c ↔ c = BlindOrtho a b d := by
  sorry

end PartB

end
