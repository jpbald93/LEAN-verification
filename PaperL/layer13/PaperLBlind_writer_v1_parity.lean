/-
  L13 stage 2 blind re-formalisation of Paper L, from BLIND.txt only.
  Conventions:
  * S (the Riemann sphere) is `OnePoint ℂ`; `∞` is `OnePoint.infty`; a point z of the plane is
    `(z : OnePoint ℂ)`.
  * The index set {1,…,n} is `Fin n`, with the prose index i read as `Fin` index i-1
    (so "c(1)" is `c 0`, "the first two circles" are `c 0`, `c 1`).
  * "the configuration obtained by deleting c(i)" is `c ∘ Fin.succAbove i`.

  PARITY WARNING (see report). Taken literally, clauses 4 and 5 of the chain make even levels
  ≥ 4 generalized circles and odd levels ≥ 3 single points. Then level 3 would need level-2
  objects that are generalized circles, but a level-2 object is a single point, so no level-3
  object exists; and Statements 2, 3 refer to "the point which is the Clifford object" at
  even levels 2k+4, 2k+6. The statements (and Clifford's classical chain: point, circle, point,
  …) fit the opposite parity. Following the instruction to define notions *exactly as the prose
  says*, the definition below is the literal one.
-/
import Mathlib

namespace PaperLBlind

open OnePoint

noncomputable section

/-- A generalized circle in S: a Euclidean circle of the plane (positive radius), or a
Euclidean line of the plane together with `∞`. -/
def BlindIsGCircle (X : Set (OnePoint ℂ)) : Prop :=
  (∃ (z : ℂ) (r : ℝ), 0 < r ∧ X = (fun w : ℂ => (w : OnePoint ℂ)) '' Metric.sphere z r) ∨
  (∃ a b : ℂ, a ≠ b ∧
    X = insert ∞ ((fun w : ℂ => (w : OnePoint ℂ)) '' {z : ℂ | Collinear ℝ ({a, b, z} : Set ℂ)}))
-- AMBIGUOUS: "Euclidean circle" could also admit radius 0 (a point circle); we require r > 0.

/-- The circle with diameter from 0 to 2·c, i.e. centre c through 0 (a subset of the plane). -/
def BlindCircle (c : ℂ) : Set ℂ := Metric.sphere c ‖c‖

/-- Two circles (centres c, d) are transversal: they meet in exactly one point besides 0. -/
def BlindTransversal (c d : ℂ) : Prop :=
  ∃! z : ℂ, z ≠ 0 ∧ z ∈ BlindCircle c ∧ z ∈ BlindCircle d

/-- The second intersection: the point other than 0 where the two circles meet; defined when the
pair is transversal (junk value 0 otherwise). -/
def BlindSecond (c d : ℂ) : ℂ :=
  haveI := Classical.propDecidable (BlindTransversal c d)
  if h : BlindTransversal c d then Classical.choose h.exists else 0

/-- General position of a configuration of n circles. -/
def BlindGenPos {n : ℕ} (c : Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, i ≠ j → BlindTransversal (c i) (c j)) ∧
  (∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
    (∀ z : ℂ, z ≠ 0 →
      ¬ (z ∈ BlindCircle (c i) ∧ z ∈ BlindCircle (c j) ∧ z ∈ BlindCircle (c k))) ∧
    BlindSecond (c i) (c j) ≠ BlindSecond (c i) (c k) ∧
    BlindSecond (c i) (c j) ≠ BlindSecond (c j) (c k) ∧
    BlindSecond (c i) (c k) ≠ BlindSecond (c j) (c k))

/-- `BlindCliff n c X`: X is a Clifford object of level n for the configuration c (literal
prose). -/
def BlindCliff : (n : ℕ) → (Fin n → ℂ) → Set (OnePoint ℂ) → Prop
  | 0, _, X => X = {((0 : ℂ) : OnePoint ℂ)}
  | 1, c, X => X = (fun w : ℂ => (w : OnePoint ℂ)) '' BlindCircle (c 0)
  | 2, c, X => X = {((BlindSecond (c 0) (c 1) : ℂ) : OnePoint ℂ)}
  | n + 3, c, X =>
    if Even (n + 3) then
      BlindIsGCircle X ∧
        ∀ i : Fin (n + 3), ∃ p : OnePoint ℂ, BlindCliff (n + 2) (c ∘ i.succAbove) {p} ∧ p ∈ X
    else
      ∃ p : OnePoint ℂ, X = {p} ∧
        ∀ i : Fin (n + 3), ∃ Y : Set (OnePoint ℂ),
          BlindIsGCircle Y ∧ BlindCliff (n + 2) (c ∘ i.succAbove) Y ∧ p ∈ Y
-- AMBIGUOUS: "has a Clifford object of level n−1 which is …, and that point lies in X" read as
-- "some such object exists and lies in / contains"; alternative: every such object does.
-- AMBIGUOUS: parity of clauses 4/5 taken literally (even = generalized circle, odd = point);
-- alternative: the swapped parity (even = point, odd = generalized circle) the statements use.

/-- Finite-plane variant: same recursion, but every Clifford object at every level is required
to be a subset of the plane (i.e. not to contain `∞`). -/
def BlindCliffFin : (n : ℕ) → (Fin n → ℂ) → Set (OnePoint ℂ) → Prop
  | 0, _, X => X = {((0 : ℂ) : OnePoint ℂ)}
  | 1, c, X => X = (fun w : ℂ => (w : OnePoint ℂ)) '' BlindCircle (c 0)
  | 2, c, X => X = {((BlindSecond (c 0) (c 1) : ℂ) : OnePoint ℂ)}
  | n + 3, c, X =>
    ∞ ∉ X ∧
    if Even (n + 3) then
      BlindIsGCircle X ∧
        ∀ i : Fin (n + 3), ∃ p : OnePoint ℂ,
          BlindCliffFin (n + 2) (c ∘ i.succAbove) {p} ∧ p ∈ X
    else
      ∃ p : OnePoint ℂ, X = {p} ∧
        ∀ i : Fin (n + 3), ∃ Y : Set (OnePoint ℂ),
          BlindIsGCircle Y ∧ BlindCliffFin (n + 2) (c ∘ i.succAbove) Y ∧ p ∈ Y
-- AMBIGUOUS: "subsets of the plane rather than of S" read as "∞ ∉ X" at every level (levels 0–2
-- are automatically in the plane); alternative: only the top-level object must avoid ∞.

/-- The six-centre configuration (3,−6), (6,−3), (1,2), (−2,−1), (0,−4), (4,0). -/
def BlindSix : Fin 6 → ℂ :=
  ![⟨3, -6⟩, ⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩]

/-- Statement 1. "For every n ≥ 1 and every configuration of n circles in general
position, there exists a Clifford object of level n." -/
theorem blind_1 : ∀ n : ℕ, 1 ≤ n → ∀ c : Fin n → ℂ, BlindGenPos c →
    ∃ X : Set (OnePoint ℂ), BlindCliff n c X := by sorry

/-- Statement 2. "For every k ≥ 0 and every configuration d of 2k+5 circles in general
position, there exists a generalized circle Y such that, for every index i, the point which is
the Clifford object of level 2k+4 for the configuration obtained by deleting d(i) lies in Y." -/
theorem blind_2 : ∀ k : ℕ, ∀ d : Fin (2 * k + 5) → ℂ, BlindGenPos d →
    ∃ Y : Set (OnePoint ℂ), BlindIsGCircle Y ∧
      ∀ i : Fin (2 * k + 5), ∃ p : OnePoint ℂ,
        BlindCliff (2 * k + 4) (d ∘ i.succAbove) {p} ∧ p ∈ Y := by sorry
-- AMBIGUOUS: "the point which is the Clifford object" read existentially (such a point exists
-- and lies in Y); alternative: every p with {p} a Clifford object of that level lies in Y.

/-- Statement 3. "For every k ≥ 0, every configuration c of 2k+6 circles in general position
and every index i, there exists a generalized circle Y such that the point which is the Clifford
object of level 2k+6 for c lies in Y, and, for every index j, the point which is the Clifford
object of level 2k+4 for the configuration obtained by deleting c(i) and then the j-th remaining
entry also lies in Y." -/
theorem blind_3 : ∀ k : ℕ, ∀ c : Fin (2 * k + 6) → ℂ, BlindGenPos c → ∀ i : Fin (2 * k + 6),
    ∃ Y : Set (OnePoint ℂ), BlindIsGCircle Y ∧
      (∃ p : OnePoint ℂ, BlindCliff (2 * k + 6) c {p} ∧ p ∈ Y) ∧
      ∀ j : Fin (2 * k + 5), ∃ q : OnePoint ℂ,
        BlindCliff (2 * k + 4) ((c ∘ i.succAbove) ∘ j.succAbove) {q} ∧ q ∈ Y := by sorry
-- AMBIGUOUS: "the point which is the Clifford object" read existentially, as in Statement 2;
-- alternative: universally over all single-point Clifford objects of that level.

/-- Statement 4. "Call a configuration *finite-plane admissible* when all the Clifford objects
of every level are required to be subsets of the plane rather than of S." -/
theorem blind_4 : ∀ n : ℕ, 1 ≤ n →
    ((∀ c : Fin n → ℂ, BlindGenPos c → ∃ X : Set (OnePoint ℂ), BlindCliffFin n c X) ↔
      n ≤ 5) := by
  sorry

/-- Statement 5. "The configuration of six circles with centres (3,−6), (6,−3), (1,2), (−2,−1),
(0,−4), (4,0) is in general position and has no Clifford object of level 6 in the plane; hence
the finite-plane statement fails at n = 6 and above." -/
theorem blind_5 :
    BlindGenPos BlindSix ∧ (¬ ∃ X : Set (OnePoint ℂ), BlindCliffFin 6 BlindSix X) ∧
      ∀ n : ℕ, 6 ≤ n →
        ¬ (∀ c : Fin n → ℂ, BlindGenPos c → ∃ X : Set (OnePoint ℂ), BlindCliffFin n c X) := by
  sorry
-- AMBIGUOUS: "no Clifford object of level 6 in the plane" read as no finite-plane
-- (BlindCliffFin) object; alternative: no S-Clifford object X (BlindCliff) with ∞ ∉ X.

/-- Statement 6. "For that same six-centre configuration the set {∞} is a Clifford object of
level 6, and it is the only one." -/
theorem blind_6 :
    BlindCliff 6 BlindSix {∞} ∧ ∀ X : Set (OnePoint ℂ), BlindCliff 6 BlindSix X → X = {∞} := by
  sorry

/-- Statement 7. "For every configuration of three circles in general position, the three
pairwise second intersections lie on a generalized circle." -/
theorem blind_7 : ∀ c : Fin 3 → ℂ, BlindGenPos c →
    ∃ Y : Set (OnePoint ℂ), BlindIsGCircle Y ∧
      ((BlindSecond (c 0) (c 1) : ℂ) : OnePoint ℂ) ∈ Y ∧
      ((BlindSecond (c 0) (c 2) : ℂ) : OnePoint ℂ) ∈ Y ∧
      ((BlindSecond (c 1) (c 2) : ℂ) : OnePoint ℂ) ∈ Y := by sorry

end

end PaperLBlind
