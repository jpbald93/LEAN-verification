/-
  Layer 13, stage 2 — blind re-formalisation of Paper L.
  Source: BLIND.txt only (setting + seven numbered statements in prose).
  Indexing: the prose indices 1,…,n are Lean's `Fin n` indices 0,…,n-1, so "c(1)" is `c 0`.
-/
import Mathlib

namespace PaperLBlind

open OnePoint

noncomputable section

/-- The Riemann sphere S = one-point compactification of ℂ. -/
abbrev BlindS := OnePoint ℂ

/-- The image in S of a subset of the plane. -/
def BlindEmb (A : Set ℂ) : Set BlindS := ((↑) : ℂ → BlindS) '' A

/-- The finite plane, as a subset of S. -/
def BlindPlane : Set BlindS := Set.range ((↑) : ℂ → BlindS)

/-- A generalized circle in S: a Euclidean circle of the plane, or a Euclidean line together
with ∞. -/
def BlindIsGCircle (X : Set BlindS) : Prop :=
  (∃ (z : ℂ) (r : ℝ), 0 < r ∧ X = BlindEmb (Metric.sphere z r)) ∨
  (∃ a b : ℂ, a ≠ b ∧ X = insert ∞ (BlindEmb {w : ℂ | ∃ t : ℝ, w = a + (t : ℂ) * (b - a)}))

/-- The circle with diameter from 0 to 2·c: centre c, radius |c|. -/
def BlindCircle (c : ℂ) : Set ℂ := Metric.sphere c ‖c‖

/-- Transversal: the two circles meet in exactly one point besides 0. -/
def BlindTransversal (c d : ℂ) : Prop :=
  ∃! z : ℂ, z ≠ 0 ∧ z ∈ BlindCircle c ∧ z ∈ BlindCircle d

/-- The second intersection: the point other than 0 where the circles meet (when transversal;
an arbitrary junk value `0` otherwise). -/
def BlindSecond (c d : ℂ) : ℂ :=
  open Classical in
  if h : BlindTransversal c d then h.exists.choose else 0

/-- General position of a configuration `c : Fin n → ℂ`. -/
def BlindGenPos {n : ℕ} (c : Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, i ≠ j → BlindTransversal (c i) (c j)) ∧
  (∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
    (¬ ∃ z : ℂ, z ≠ 0 ∧ z ∈ BlindCircle (c i) ∧ z ∈ BlindCircle (c j) ∧ z ∈ BlindCircle (c k)) ∧
    BlindSecond (c i) (c j) ≠ BlindSecond (c i) (c k) ∧
    BlindSecond (c i) (c j) ≠ BlindSecond (c j) (c k) ∧
    BlindSecond (c i) (c k) ≠ BlindSecond (c j) (c k))

/-- The configuration obtained by deleting the entry `c i`. -/
def BlindDelete {m : ℕ} (c : Fin (m + 1) → ℂ) (i : Fin (m + 1)) : Fin m → ℂ :=
  fun j => c (i.succAbove j)

/-- Clifford object of level n for a configuration of n circles. With `plane = false` this is
the chain on the sphere S; with `plane = true` every object at every level is additionally
required to be a subset of the plane (the "finite-plane" variant of Statement 4). -/
def BlindCliffordP (plane : Bool) : (n : ℕ) → (Fin n → ℂ) → Set BlindS → Prop
  | 0, _, X => (plane = true → X ⊆ BlindPlane) ∧ X = {((0 : ℂ) : BlindS)}
  | 1, c, X => (plane = true → X ⊆ BlindPlane) ∧ X = BlindEmb (BlindCircle (c 0))
  | 2, c, X => (plane = true → X ⊆ BlindPlane) ∧ X = {((BlindSecond (c 0) (c 1) : ℂ) : BlindS)}
  | m + 3, c, X =>
      (plane = true → X ⊆ BlindPlane) ∧
      if Odd (m + 3) then
        BlindIsGCircle X ∧
          ∀ i : Fin (m + 3), ∃ p : BlindS, BlindCliffordP plane (m + 2) (BlindDelete c i) {p} ∧ p ∈ X
      else
        ∃ p : BlindS, X = {p} ∧
          ∀ i : Fin (m + 3), ∃ Y : Set BlindS,
            BlindCliffordP plane (m + 2) (BlindDelete c i) Y ∧ BlindIsGCircle Y ∧ p ∈ Y
-- AMBIGUOUS: "has a Clifford object of level n−1 which is a single point, and that point lies in X"
-- is read existentially (some such object exists and lies in X); the alternative is "every
-- level-(n−1) object of the deleted configuration (assumed unique) lies in X".

/-- Clifford object of level n on the sphere S. -/
def BlindClifford (n : ℕ) (c : Fin n → ℂ) (X : Set BlindS) : Prop := BlindCliffordP false n c X

/-- Finite-plane Clifford object of level n (all objects at every level are subsets of the plane). -/
def BlindCliffordFin (n : ℕ) (c : Fin n → ℂ) (X : Set BlindS) : Prop := BlindCliffordP true n c X
-- AMBIGUOUS: in the finite-plane variant "generalized circle" is kept as defined (so it must be a
-- Euclidean circle, since a line carries ∞); the alternative would allow bare lines without ∞.

/-- The six-centre configuration of Statement 5. -/
def BlindSix : Fin 6 → ℂ :=
  ![⟨3, -6⟩, ⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩]

/-- Statement 1. "For every n ≥ 1 and every configuration of n circles in general position, there
exists a Clifford object of level n." -/
theorem blind_1 (n : ℕ) (hn : 1 ≤ n) (c : Fin n → ℂ) (hc : BlindGenPos c) :
    ∃ X : Set BlindS, BlindClifford n c X := by sorry

/-- Statement 2. "For every k ≥ 0 and every configuration d of 2k+5 circles in general position,
there exists a generalized circle Y such that, for every index i, the point which is the Clifford
object of level 2k+4 for the configuration obtained by deleting d(i) lies in Y." -/
-- AMBIGUOUS: "the point which is the Clifford object" is read as: such a point object exists, and
-- every point that is a level-(2k+4) object of the deleted configuration lies in Y. The
-- alternative is the purely existential reading (some such point lies in Y).
theorem blind_2 (k : ℕ) (d : Fin (2 * k + 5) → ℂ) (hd : BlindGenPos d) :
    ∃ Y : Set BlindS, BlindIsGCircle Y ∧
      ∀ i : Fin (2 * k + 5),
        (∃ p : BlindS, BlindClifford (2 * k + 4) (BlindDelete d i) {p}) ∧
        ∀ p : BlindS, BlindClifford (2 * k + 4) (BlindDelete d i) {p} → p ∈ Y := by sorry

/-- Statement 3. "For every k ≥ 0, every configuration c of 2k+6 circles in general position and
every index i, there exists a generalized circle Y such that the point which is the Clifford object
of level 2k+6 for c lies in Y, and, for every index j, the point which is the Clifford object of
level 2k+4 for the configuration obtained by deleting c(i) and then the j-th remaining entry also
lies in Y." -/
-- AMBIGUOUS: same treatment of "the point which is the Clifford object" as in Statement 2
-- (existence + every such point lies in Y); alternative: purely existential.
theorem blind_3 (k : ℕ) (c : Fin (2 * k + 6) → ℂ) (hc : BlindGenPos c) (i : Fin (2 * k + 6)) :
    ∃ Y : Set BlindS, BlindIsGCircle Y ∧
      ((∃ p : BlindS, BlindClifford (2 * k + 6) c {p}) ∧
        ∀ p : BlindS, BlindClifford (2 * k + 6) c {p} → p ∈ Y) ∧
      ∀ j : Fin (2 * k + 5),
        (∃ q : BlindS, BlindClifford (2 * k + 4) (BlindDelete (BlindDelete c i) j) {q}) ∧
        ∀ q : BlindS, BlindClifford (2 * k + 4) (BlindDelete (BlindDelete c i) j) {q} → q ∈ Y := by
  sorry

/-- Statement 4. "Call a configuration finite-plane admissible when all the Clifford objects of
every level are required to be subsets of the plane rather than of S." -/
theorem blind_4 (n : ℕ) (hn : 1 ≤ n) :
    (∀ c : Fin n → ℂ, BlindGenPos c → ∃ X : Set BlindS, BlindCliffordFin n c X) ↔ n ≤ 5 := by
  sorry

/-- Statement 5. "The configuration of six circles with centres (3,−6), (6,−3), (1,2), (−2,−1),
(0,−4), (4,0) is in general position and has no Clifford object of level 6 in the plane; hence the
finite-plane statement fails at n = 6 and above." -/
-- AMBIGUOUS: "no Clifford object of level 6 in the plane" is read as: no level-6 object on S is a
-- subset of the plane. Alternative: no finite-plane object (`BlindCliffordFin`) of level 6, where
-- the lower levels are also restricted to the plane.
theorem blind_5 :
    BlindGenPos BlindSix ∧
    (¬ ∃ X : Set BlindS, BlindClifford 6 BlindSix X ∧ X ⊆ BlindPlane) ∧
    ∀ n : ℕ, 6 ≤ n →
      ¬ (∀ c : Fin n → ℂ, BlindGenPos c → ∃ X : Set BlindS, BlindCliffordFin n c X) := by
  sorry

/-- Statement 6. "For that same six-centre configuration the set {∞} is a Clifford object of
level 6, and it is the only one." -/
theorem blind_6 :
    BlindClifford 6 BlindSix {∞} ∧
    ∀ X : Set BlindS, BlindClifford 6 BlindSix X → X = {∞} := by sorry

/-- Statement 7. "For every configuration of three circles in general position, the three pairwise
second intersections lie on a generalized circle." -/
theorem blind_7 (c : Fin 3 → ℂ) (hc : BlindGenPos c) :
    ∃ Y : Set BlindS, BlindIsGCircle Y ∧
      ((BlindSecond (c 0) (c 1) : ℂ) : BlindS) ∈ Y ∧
      ((BlindSecond (c 0) (c 2) : ℂ) : BlindS) ∈ Y ∧
      ((BlindSecond (c 1) (c 2) : ℂ) : BlindS) ∈ Y := by sorry

end

end PaperLBlind
