import Mathlib

open Affine EuclideanGeometry

noncomputable section

/-! ## Clifford's chain in the complex model: n = 4, 5, 6 -/
section Clifford

/-- Second intersection point `P_ij` of the circles through `0` with centres `ci`, `cj`
(formula exactly as in the prose). -/
def BlindP (ci cj : ℂ) : ℂ :=
  ((starRingEnd ℂ) ci * cj - ci * (starRingEnd ℂ) cj) / ((starRingEnd ℂ) ci - (starRingEnd ℂ) cj)

/-- `z` lies on the circumcircle of `a, b, c` (the centre is equidistant from all four). -/
def BlindOnCircum (a b c z : ℂ) : Prop :=
  ∃ o : ℂ, dist o a = dist o b ∧ dist o b = dist o c ∧ dist o z = dist o a

/-- `z` lies on `Γ_ijk`, the circumcircle of `P_ij, P_ik, P_jk`. -/
def BlindOnGamma {n : ℕ} (c : Fin n → ℂ) (i j k : Fin n) (z : ℂ) : Prop :=
  BlindOnCircum (BlindP (c i) (c j)) (BlindP (c i) (c k)) (BlindP (c j) (c k)) z

/-- The hypotheses shared by the Clifford theorems: every `P_ij ≠ M = 0` and no triple
`P_ij, P_ik, P_jk` is collinear. -/
def BlindCliffordHyp {n : ℕ} (c : Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, i < j → BlindP (c i) (c j) ≠ 0) ∧
  (∀ i j k : Fin n, i < j → j < k →
    ¬ Collinear ℝ ({BlindP (c i) (c j), BlindP (c i) (c k), BlindP (c j) (c k)} : Set ℂ))

/-- `z` is a common point (`cp`) of the circles `Γ` of all triples inside the index set `T`. -/
def BlindIsCp {n : ℕ} (c : Fin n → ℂ) (T : Finset (Fin n)) (z : ℂ) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T, i < j → j < k → BlindOnGamma c i j k z

/-- A generalized circle: a Euclidean circle (radius `≥ 0`, radius `0` allowed) or a line. -/
inductive BlindGenCircle
  | circle (o : ℂ) (r : ℝ) (hr : 0 ≤ r)
  | line (p v : ℂ) (hv : v ≠ 0)

def BlindGenCircle.carrier : BlindGenCircle → Set ℂ
  | .circle o r _ => Metric.sphere o r
  | .line p v _ => {z | ∃ t : ℝ, z = p + t * v}

/-- The set `S` lies on one generalized circle (a circle or a line). -/
def BlindOnGenCircle (S : Set ℂ) : Prop := ∃ g : BlindGenCircle, S ⊆ g.carrier

-- thm:cliff4: "Let four circles pass through a common point M, with centres c_1,…,c_4."
-- (conclusion: Γ_123, Γ_124, Γ_134, Γ_234 have a common point)
theorem blind_1 (c : Fin 4 → ℂ) (h : BlindCliffordHyp c) :
    ∃ z : ℂ, BlindIsCp c Finset.univ z := by sorry

-- thm:cliff5 (existential part): "Let five circles pass through M, with every P_ij ≠ M and no
-- triple P_ij,P_ik,P_jk collinear."  There exist five points P_k, each on the four Γ of the
-- four circles other than k, lying on one circle or one line.
theorem blind_2 (c : Fin 5 → ℂ) (h : BlindCliffordHyp c) :
    ∃ P : Fin 5 → ℂ, (∀ k, BlindIsCp c (Finset.univ.erase k) (P k)) ∧
      BlindOnGenCircle (Set.range P) := by sorry

-- thm:cliff5 (explicit points): same hypotheses; P_k = cp of the four circles other than k.
-- The prose does not give the formula of cp, so every common point of the four Γ is allowed.
-- AMBIGUOUS: cp is the paper's single explicit point; here any common point is quantified over.
theorem blind_3 (c : Fin 5 → ℂ) (h : BlindCliffordHyp c)
    (P : Fin 5 → ℂ) (hP : ∀ k, BlindIsCp c (Finset.univ.erase k) (P k)) :
    BlindOnGenCircle (Set.range P) := by sorry

/-- The three designated 4-subsets `T ⊂ S` whose points define `C_S`: for `S = {a<b<c<d<e}`
the subsets obtained by dropping `e`, `d`, `c`.  (For `S = {1..5}` these are `{1,2,3,4}`,
`{1,2,3,5}`, `{1,2,4,5}`.) -/
def BlindDesignated (S : Finset (Fin 6)) : Finset (Finset (Fin 6)) :=
  (S.sort (· ≤ ·)).reverse.take 3 |>.toFinset.image (fun x => S.erase x)

-- thm:cliff6: "Let six circles pass through M, with every P_ij ≠ M and no triple P_ij,P_ik,P_jk
-- collinear."  For each 5-subset S, the cp-points of the five 4-subsets T ⊂ S lie on C_S (circle
-- through the three designated ones, assumed non-collinear), and the six C_S have a common point.
-- AMBIGUOUS: the choice of the three designated subsets for S ≠ {1,..,5} is redacted in the
-- prose; "drop the three largest elements" is the pattern fitting the one example given.
-- AMBIGUOUS: cp not given by formula; any common point of the four Γ is quantified over.
theorem blind_4 (c : Fin 6 → ℂ) (h : BlindCliffordHyp c)
    (P : Finset (Fin 6) → ℂ) (hP : ∀ T : Finset (Fin 6), T.card = 4 → BlindIsCp c T (P T))
    (a b d : Finset (Fin 6) → Finset (Fin 6))
    (hdes : ∀ S : Finset (Fin 6), S.card = 5 → BlindDesignated S = {a S, b S, d S})
    (hnc : ∀ S : Finset (Fin 6), S.card = 5 →
      ¬ Collinear ℝ ({P (a S), P (b S), P (d S)} : Set ℂ)) :
    (∀ S : Finset (Fin 6), S.card = 5 → ∀ T ⊆ S, T.card = 4 →
        BlindOnCircum (P (a S)) (P (b S)) (P (d S)) (P T)) ∧
      ∃ z : ℂ, ∀ S : Finset (Fin 6), S.card = 5 →
        BlindOnCircum (P (a S)) (P (b S)) (P (d S)) z := by sorry

end Clifford

/-! ## The chain predicate and CliffordChain(n) -/
section Chain

/-- A Clifford object: a point or a generalized circle. -/
inductive BlindObj
  | pt (z : ℂ)
  | gc (g : BlindGenCircle)

/-- `BlindChain n c X`: `X` is a Clifford object of level `n` for the centres `c`:
levels 0, 1, 2 are `M`, the circle itself, `P_01`; odd `n ≥ 3`: a generalized circle containing,
for each `i`, some level-`(n-1)` point of the circles other than `i`; even `n ≥ 4`: a point lying,
for each `i`, on some level-`(n-1)` object of the circles other than `i`. -/
def BlindChain : (n : ℕ) → (Fin n → ℂ) → BlindObj → Prop
  | 0, _, X => X = .pt 0
  | 1, c, X => X = .gc (.circle (c 0) ‖c 0‖ (norm_nonneg _))
  | 2, c, X => X = .pt (BlindP (c 0) (c 1))
  | n + 3, c, X =>
    if Odd (n + 3) then
      ∃ g : BlindGenCircle, X = .gc g ∧ ∀ i : Fin (n + 3), ∃ z ∈ g.carrier,
        BlindChain (n + 2) (fun j => c (i.succAbove j)) (.pt z)
    else
      ∃ z : ℂ, X = .pt z ∧ ∀ i : Fin (n + 3), ∃ g : BlindGenCircle, z ∈ g.carrier ∧
        BlindChain (n + 2) (fun j => c (i.succAbove j)) (.gc g)

/-- General position: circles pairwise transversal (`M`, `c_i`, `c_j` not collinear), and every
triple non-degenerate (centres not collinear, second intersection points not collinear). -/
def BlindGeneralPosition {n : ℕ} (c : Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, i < j → ¬ Collinear ℝ ({0, c i, c j} : Set ℂ)) ∧
  (∀ i j k : Fin n, i < j → j < k →
    ¬ Collinear ℝ ({c i, c j, c k} : Set ℂ) ∧
    ¬ Collinear ℝ ({BlindP (c i) (c j), BlindP (c i) (c k), BlindP (c j) (c k)} : Set ℂ))

/-- Clifford's theorem for `n` circles: in general position a level-`n` object exists. -/
def BlindCliffordChain (n : ℕ) : Prop :=
  ∀ c : Fin n → ℂ, BlindGeneralPosition c → ∃ X : BlindObj, BlindChain n c X

-- thm:chain (n = 4): "CliffordChain(4) and CliffordChain(5) hold."
theorem blind_5 : BlindCliffordChain 4 := by sorry

-- thm:chain (n = 5)
theorem blind_6 : BlindCliffordChain 5 := by sorry

end Chain

/-! ## Miquel's five circles -/
section Five

-- thm:five: "Let A,T,M:{0,…,4}→ℂ be injective, with no point of one family equal to a point of
-- another (so the fifteen labelled points are pairwise distinct)."
theorem blind_7 (A T M : Fin 5 → ℂ)
    (hA : Function.Injective A) (hT : Function.Injective T) (hM : Function.Injective M)
    (hAT : ∀ i j, A i ≠ T j) (hAM : ∀ i j, A i ≠ M j) (hTM : ∀ i j, T i ≠ M j)
    (hcol : ∀ i : Fin 5, Collinear ℝ ({A (i - 1), A i, T (i + 1), T (i - 1)} : Set ℂ))
    (hcyc : ∀ i : Fin 5, Concyclic ({A (i - 1), A i, T i, M (i - 1), M i} : Set ℂ)) :
    Concyclic (Set.range M) ∨ Collinear ℝ (Set.range M) := by sorry

end Five

/-! ## Lester's circle -/
section Lester

abbrev BlindPlane := EuclideanSpace ℝ (Fin 2)

/-- `D` is the apex of the equilateral triangle on `BC`, erected on the side of line `BC`
opposite to `A` (outwards) or on the same side as `A` (inwards). -/
def BlindApex (outward : Bool) (A B C D : BlindPlane) : Prop :=
  dist D B = dist B C ∧ dist D C = dist B C ∧
    (if outward then (line[ℝ, B, C]).SOppSide A D else (line[ℝ, B, C]).SSameSide A D)

/-- `F` is the first (outward) or second (inward) Fermat point: the common point of the three
lines joining each vertex to the apex of the equilateral triangle on the opposite side. -/
def BlindIsFermat (t : Affine.Triangle ℝ BlindPlane) (outward : Bool) (F : BlindPlane) : Prop :=
  ∃ Da Db Dc : BlindPlane,
    BlindApex outward (t.points 0) (t.points 1) (t.points 2) Da ∧
    BlindApex outward (t.points 1) (t.points 2) (t.points 0) Db ∧
    BlindApex outward (t.points 2) (t.points 0) (t.points 1) Dc ∧
    F ∈ line[ℝ, t.points 0, Da] ∧ F ∈ line[ℝ, t.points 1, Db] ∧ F ∈ line[ℝ, t.points 2, Dc]

-- thm:lester: "Let ABC be a scalene triangle in the plane."
theorem blind_8 (t : Affine.Triangle ℝ BlindPlane)
    (hscalene : dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2) ∧
      dist (t.points 1) (t.points 2) ≠ dist (t.points 2) (t.points 0) ∧
      dist (t.points 2) (t.points 0) ≠ dist (t.points 0) (t.points 1))
    (F₁ F₂ : BlindPlane) (hF₁ : BlindIsFermat t true F₁) (hF₂ : BlindIsFermat t false F₂) :
    Concyclic ({t.circumcenter, t.ninePointCircle.center, F₁, F₂} : Set BlindPlane) := by sorry

end Lester

/-! ## Sawayama–Thébault -/
section Thebault

/-- `P` is a Thébault centre on the side of the vertex `Y` (`B` or `C`) of the cevian `AD`:
there is `r > 0` with `P` at distance `r` from lines `AD` and `BC`, at distance `R - r` from the
circumcentre, on the same side of `AD` as `Y` and on the same side of `BC` as `A`. -/
def BlindThebaultCentre (t : Affine.Triangle ℝ BlindPlane) (D Y P : BlindPlane) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    Metric.infDist P (line[ℝ, t.points 0, D] : Set BlindPlane) = r ∧
    Metric.infDist P (line[ℝ, t.points 1, t.points 2] : Set BlindPlane) = r ∧
    dist P t.circumcenter = t.circumradius - r ∧
    (line[ℝ, t.points 0, D]).SSameSide P Y ∧
    (line[ℝ, t.points 1, t.points 2]).SSameSide P (t.points 0)

-- thm:thebault: "Let ABC be a triangle and D a point strictly between B and C."
theorem blind_9 (t : Affine.Triangle ℝ BlindPlane) (D : BlindPlane)
    (hD : Sbtw ℝ (t.points 1) D (t.points 2)) (P Q : BlindPlane)
    (hP : BlindThebaultCentre t D (t.points 1) P)
    (hQ : BlindThebaultCentre t D (t.points 2) Q) :
    Collinear ℝ ({P, Q, t.incenter} : Set BlindPlane) := by sorry

end Thebault

/-! ## Kosnita -/
section Kosnita

-- thm:kosnita: "Let ABC be a triangle with circumcentre O, and let O_a,O_b,O_c be the circumcentres
-- of the triangles OBC, OCA, OAB."
-- AMBIGUOUS: "no two diametrically opposite" could be stated as ¬Collinear {O,B,C} etc.
-- (equivalent on a circle of positive radius).
theorem blind_10 (t : Affine.Triangle ℝ BlindPlane) (Oa Ob Oc : BlindPlane)
    (hnA : t.circumcenter ≠ midpoint ℝ (t.points 1) (t.points 2))
    (hnB : t.circumcenter ≠ midpoint ℝ (t.points 2) (t.points 0))
    (hnC : t.circumcenter ≠ midpoint ℝ (t.points 0) (t.points 1))
    (hS : dist (t.points 0) (t.points 1) ^ 2 + dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 ≠ 5 * t.circumradius ^ 2)
    (hOa : dist Oa t.circumcenter = dist Oa (t.points 1) ∧ dist Oa (t.points 1) = dist Oa (t.points 2))
    (hOb : dist Ob t.circumcenter = dist Ob (t.points 2) ∧ dist Ob (t.points 2) = dist Ob (t.points 0))
    (hOc : dist Oc t.circumcenter = dist Oc (t.points 0) ∧ dist Oc (t.points 0) = dist Oc (t.points 1)) :
    ∃ X : BlindPlane, X ∈ line[ℝ, t.points 0, Oa] ∧ X ∈ line[ℝ, t.points 1, Ob] ∧
      X ∈ line[ℝ, t.points 2, Oc] := by sorry

end Kosnita

/-! ## Blundon and Steiner–Lehmus -/
section Companions

-- thm:blundon: "For a triangle in a real inner product space with circumradius R, inradius r and
-- semiperimeter s, [the two-sided inequality] holds."
theorem blind_11 {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) :
    let R := t.circumradius
    let r := t.inradius
    let s := (dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2) +
      dist (t.points 2) (t.points 0)) / 2
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2 ∧
    s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) := by
  sorry

-- thm:steiner: "In a non-degenerate triangle ABC, let E on segment AC and F on segment AB be the
-- feet of the internal bisectors from B and C. If BE = CF then AB = AC."
theorem blind_12 {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (A B C E F : P) (hABC : AffineIndependent ℝ ![A, B, C])
    (hE : E ∈ affineSegment ℝ A C) (hEb : ∠ A B E = ∠ E B C)
    (hF : F ∈ affineSegment ℝ A B) (hFb : ∠ A C F = ∠ F C B)
    (h : dist B E = dist C F) : dist A B = dist A C := by sorry

end Companions
