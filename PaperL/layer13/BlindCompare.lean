import Clifford.MorleyKernel
import Clifford.Counter6
import Clifford.Mobius
import Clifford.Classify

open OnePoint

namespace PaperLBlind

noncomputable section

abbrev BlindS := OnePoint ℂ

def BlindEmb (A : Set ℂ) : Set BlindS := ((↑) : ℂ → BlindS) '' A

def BlindPlane : Set BlindS := Set.range ((↑) : ℂ → BlindS)

def BlindIsGCircle (X : Set BlindS) : Prop :=
  (∃ (z : ℂ) (r : ℝ), 0 < r ∧ X = BlindEmb (Metric.sphere z r)) ∨
  (∃ a b : ℂ, a ≠ b ∧ X = insert ∞
    (BlindEmb {w : ℂ | ∃ t : ℝ, w = a + (t : ℂ) * (b - a)}))

def BlindCircle (c : ℂ) : Set ℂ := Metric.sphere c ‖c‖

def BlindTransversal (c d : ℂ) : Prop :=
  ∃! z : ℂ, z ≠ 0 ∧ z ∈ BlindCircle c ∧ z ∈ BlindCircle d

def BlindSecond (c d : ℂ) : ℂ :=
  open Classical in
  if h : BlindTransversal c d then h.exists.choose else 0

def BlindGenPos {n : ℕ} (c : Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, i ≠ j → BlindTransversal (c i) (c j)) ∧
  (∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
    (¬ ∃ z : ℂ, z ≠ 0 ∧ z ∈ BlindCircle (c i) ∧ z ∈ BlindCircle (c j) ∧
      z ∈ BlindCircle (c k)) ∧
    BlindSecond (c i) (c j) ≠ BlindSecond (c i) (c k) ∧
    BlindSecond (c i) (c j) ≠ BlindSecond (c j) (c k) ∧
    BlindSecond (c i) (c k) ≠ BlindSecond (c j) (c k))

def BlindDelete {m : ℕ} (c : Fin (m + 1) → ℂ) (i : Fin (m + 1)) : Fin m → ℂ :=
  fun j => c (i.succAbove j)

def BlindCliffordP (plane : Bool) : (n : ℕ) → (Fin n → ℂ) → Set BlindS → Prop
  | 0, _, X => (plane = true → X ⊆ BlindPlane) ∧ X = {((0 : ℂ) : BlindS)}
  | 1, c, X => (plane = true → X ⊆ BlindPlane) ∧ X = BlindEmb (BlindCircle (c 0))
  | 2, c, X => (plane = true → X ⊆ BlindPlane) ∧
      X = {((BlindSecond (c 0) (c 1) : ℂ) : BlindS)}
  | m + 3, c, X =>
      (plane = true → X ⊆ BlindPlane) ∧
      if Odd (m + 3) then
        BlindIsGCircle X ∧
          ∀ i : Fin (m + 3), ∃ p : BlindS,
            BlindCliffordP plane (m + 2) (BlindDelete c i) {p} ∧ p ∈ X
      else
        ∃ p : BlindS, X = {p} ∧
          ∀ i : Fin (m + 3), ∃ Y : Set BlindS,
            BlindCliffordP plane (m + 2) (BlindDelete c i) Y ∧ BlindIsGCircle Y ∧ p ∈ Y

def BlindClifford (n : ℕ) (c : Fin n → ℂ) (X : Set BlindS) : Prop :=
  BlindCliffordP false n c X

def BlindCliffordFin (n : ℕ) (c : Fin n → ℂ) (X : Set BlindS) : Prop :=
  BlindCliffordP true n c X

def BlindSix : Fin 6 → ℂ :=
  ![⟨3, -6⟩, ⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩]

end

end PaperLBlind

namespace BlindCompare

open PaperLBlind

noncomputable section

/-- S1, reconstructed from the blind prose. -/
def blind_1 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ c : Fin n → ℂ, BlindGenPos c →
    ∃ X : Set BlindS, BlindClifford n c X

/-- S1, the sphere-valued Clifford-chain assertion supplied by the named real results. -/
def real_1 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → Clifford.CliffordChainS n

/-- S2, reconstructed literally: each deleted configuration has some point object. -/
def blind_2 : Prop :=
  ∀ (k : ℕ) (d : Fin (2 * k + 5) → ℂ), BlindGenPos d →
    ∃ Y : Set BlindS, BlindIsGCircle Y ∧
      ∀ i : Fin (2 * k + 5), ∃ p : BlindS,
        BlindClifford (2 * k + 4) (BlindDelete d i) {p} ∧ p ∈ Y

/-- S2, exactly the universally closed type of `hodd_inf_all'`. -/
def real_2 : Prop :=
  ∀ (k : ℕ) (d : Fin (2 * k + 5) → ℂ), Clifford.GenPosN d →
    ∃ Y, Clifford.IsGCircleS Y ∧ ∀ i : Fin (2 * k + 5),
      Clifford.MorleyKernel.EptInf (2 * k + 4) (d ∘ i.succAbove) ∈ Y

/-- S3, reconstructed literally with existentially chosen point objects. -/
def blind_3 : Prop :=
  ∀ (k : ℕ) (c : Fin (2 * k + 6) → ℂ), BlindGenPos c →
    ∀ i : Fin (2 * k + 6), ∃ Y : Set BlindS, BlindIsGCircle Y ∧
      ∃ p : BlindS, BlindClifford (2 * k + 6) c {p} ∧ p ∈ Y ∧
        ∀ j : Fin (2 * k + 5), ∃ q : BlindS,
          BlindClifford (2 * k + 4) (BlindDelete (BlindDelete c i) j) {q} ∧ q ∈ Y

/-- S3, exactly the universally closed type of `heven_inf_all`. -/
def real_3 : Prop :=
  ∀ (k : ℕ) (c : Fin (2 * k + 6) → ℂ), Clifford.GenPosN c →
    ∀ i : Fin (2 * k + 6), ∃ Y, Clifford.IsGCircleS Y ∧
      Clifford.MorleyKernel.EptInf (2 * k + 6) c ∈ Y ∧
        ∀ j : Fin (2 * k + 5),
          Clifford.MorleyKernel.EptInf (2 * k + 4)
            ((c ∘ i.succAbove) ∘ j.succAbove) ∈ Y

/-- S4, reconstructed with the prose's explicit `n ≥ 1` range. -/
def blind_4 : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ((∀ c : Fin n → ℂ, BlindGenPos c →
      ∃ X : Set BlindS, BlindCliffordFin n c X) ↔ n ≤ 5)

/-- S4, the universally closed type of `cliffordChain_iff`. -/
def real_4 : Prop :=
  ∀ n : ℕ, Clifford.CliffordChain n ↔ n ≤ 5

/-- S5, using the redaction choice recorded at the blind definition. -/
def blind_5 : Prop :=
  BlindGenPos BlindSix ∧
    ¬ ∃ X : Set BlindS, BlindClifford 6 BlindSix X ∧ X ⊆ BlindPlane

/-- S5, the conjunction of the exact two named real theorem types. -/
def real_5 : Prop :=
  Clifford.GenPosN Clifford.Counter6.cx ∧ ¬ Clifford.CliffordChain 6

/-- S6, reconstructed as existence of `{∞}` and uniqueness among all sphere objects. -/
def blind_6 : Prop :=
  BlindClifford 6 BlindSix {∞} ∧
    ∀ X : Set BlindS, BlindClifford 6 BlindSix X → X = {∞}

/-- S6, the conjunction of the exact two named real theorem types. -/
def real_6 : Prop :=
  Clifford.ChainS 6 Clifford.Counter6.cx {∞} ∧
    ∀ X : Set (OnePoint ℂ), Clifford.ChainS 6 Clifford.Counter6.cx X → X = {∞}

/-- S7, reconstructed directly as concyclicity of the three pairwise blind intersections. -/
def blind_7 : Prop :=
  ∀ c : Fin 3 → ℂ, BlindGenPos c → ∃ Y : Set BlindS, BlindIsGCircle Y ∧
    (BlindSecond (c 0) (c 1) : BlindS) ∈ Y ∧
    (BlindSecond (c 0) (c 2) : BlindS) ∈ Y ∧
    (BlindSecond (c 1) (c 2) : BlindS) ∈ Y

/-- S7, exactly `CliffordChainS 3`. -/
def real_7 : Prop := Clifford.CliffordChainS 3

/-
No implication theorem is asserted here. In every row, even the first required conversion
already crosses at least one independently defined geometric predicate (`BlindGenPos` versus
`GenPosN`, `BlindSecond` versus `second`, `BlindIsGCircle` versus `IsGCircleS`, or
`BlindCliffordP` versus `Chain`/`ChainS`). Establishing any such bridge is genuine mathematics,
not definitional unfolding or proposition repackaging, so the mandated stop rule applies.
-/

end

end BlindCompare
