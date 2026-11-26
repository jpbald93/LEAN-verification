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

namespace BlindCompareFull

open PaperLBlind

noncomputable section

def BlindN1 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ c : Fin n → ℂ, BlindGenPos c →
    ∃ X : Set BlindS, BlindClifford n c X

def RealN1 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → Clifford.CliffordChainS n

example : (∀ n : ℕ, 3 ≤ n → Clifford.CliffordChainS n) =
    type_of% @Clifford.MorleyKernel.cliffordChainS_inf := rfl

example : (∀ n : ℕ, n ≤ 5 → Clifford.CliffordChainS n) =
    type_of% @Clifford.cliffordChainS_of_le_five := rfl

theorem N1_BR (_h : BlindN1) : RealN1 := by
  intro n hn
  by_cases h3 : 3 ≤ n
  · exact Clifford.MorleyKernel.cliffordChainS_inf n h3
  · exact Clifford.cliffordChainS_of_le_five (by omega)

-- UNCLOSED N1_RB: converting the hypothesis and result requires BlindGenPos/GenPosN and
-- BlindCliffordP/ChainS bridge lemmas; none are present in the library.

def BlindN7 : Prop :=
  ∀ c : Fin 3 → ℂ, BlindGenPos c → ∃ Y : Set BlindS, BlindIsGCircle Y ∧
    (BlindSecond (c 0) (c 1) : BlindS) ∈ Y ∧
    (BlindSecond (c 0) (c 2) : BlindS) ∈ Y ∧
    (BlindSecond (c 1) (c 2) : BlindS) ∈ Y

def RealN7 : Prop := Clifford.CliffordChainS 3

example : RealN7 = type_of% @Clifford.cliffordChain_threeS := rfl

theorem N7_BR (_h : BlindN7) : RealN7 := Clifford.cliffordChain_threeS

-- UNCLOSED N7_RB: unfolding ChainS 3 yields incidence for algebraic second points on an
-- IsGCircleS; conversion to BlindSecond, BlindIsGCircle, and BlindGenPos needs absent bridges.

def BlindN6 : Prop :=
  BlindClifford 6 BlindSix {∞} ∧
    ∀ X : Set BlindS, BlindClifford 6 BlindSix X → X = {∞}

def RealN6 : Prop :=
  Clifford.ChainS 6 Clifford.Counter6.cx {∞} ∧
    ∀ X : Set (OnePoint ℂ), Clifford.ChainS 6 Clifford.Counter6.cx X → X = {∞}

example : Clifford.ChainS 6 Clifford.Counter6.cx {∞} =
    type_of% @Clifford.Counter6S.chainS_six := rfl

example : (∀ X : Set (OnePoint ℂ), Clifford.ChainS 6 Clifford.Counter6.cx X → X = {∞}) =
    type_of% @Clifford.Counter6S.chainS_six_unique := rfl

theorem N6_BR (_h : BlindN6) : RealN6 :=
  ⟨Clifford.Counter6S.chainS_six, fun _ hX => Clifford.Counter6S.chainS_six_unique hX⟩

-- UNCLOSED N6_RB: BlindSix and Counter6.cx are definitionally equal, but converting the
-- existence and uniqueness claims needs a BlindCliffordP false/ChainS equivalence.

def BlindN2 : Prop :=
  ∀ (k : ℕ) (d : Fin (2 * k + 5) → ℂ), BlindGenPos d →
    ∃ Y : Set BlindS, BlindIsGCircle Y ∧
      ∀ i : Fin (2 * k + 5),
        (∃ p : BlindS, BlindClifford (2 * k + 4) (BlindDelete d i) {p}) ∧
        ∀ p : BlindS, BlindClifford (2 * k + 4) (BlindDelete d i) {p} → p ∈ Y

def RealN2 : Prop :=
  type_of% @Clifford.MorleyKernel.hodd_inf_all'

theorem N2_BR (_h : BlindN2) : RealN2 := Clifford.MorleyKernel.hodd_inf_all'

-- UNCLOSED N2_RB: hodd_inf_all' gives incidence only for EptInf. Even after bridging the blind
-- predicates, the writer requires every certified singleton point to lie on Y. This would need
-- a universal-incidence lemma; identifying all such points with EptInf is unavailable and the
-- corresponding general even-level uniqueness statement is refuted by not_UniqEven.lean.

def BlindN3 : Prop :=
  ∀ (k : ℕ) (c : Fin (2 * k + 6) → ℂ), BlindGenPos c → ∀ i : Fin (2 * k + 6),
    ∃ Y : Set BlindS, BlindIsGCircle Y ∧
      ((∃ p : BlindS, BlindClifford (2 * k + 6) c {p}) ∧
        ∀ p : BlindS, BlindClifford (2 * k + 6) c {p} → p ∈ Y) ∧
      ∀ j : Fin (2 * k + 5),
        (∃ q : BlindS, BlindClifford (2 * k + 4) (BlindDelete (BlindDelete c i) j) {q}) ∧
        ∀ q : BlindS, BlindClifford (2 * k + 4) (BlindDelete (BlindDelete c i) j) {q} → q ∈ Y

def RealN3 : Prop :=
  type_of% @Clifford.MorleyKernel.heven_inf_all

theorem N3_BR (_h : BlindN3) : RealN3 := Clifford.MorleyKernel.heven_inf_all

-- UNCLOSED N3_RB: the real payload gives incidence only for the parent and child EptInf values.
-- The writer quantifies universally over every certified parent and twice-deleted singleton;
-- predicate bridges plus canonical certificates do not prove those universal clauses, and the
-- needed general uniqueness principle is false.

def BlindN5 : Prop :=
  BlindGenPos BlindSix ∧
    (¬ ∃ X : Set BlindS, BlindClifford 6 BlindSix X ∧ X ⊆ BlindPlane) ∧
    ∀ n : ℕ, 6 ≤ n →
      ¬ (∀ c : Fin n → ℂ, BlindGenPos c → ∃ X : Set BlindS, BlindCliffordFin n c X)

def RealN5 : Prop :=
  Clifford.GenPosN Clifford.Counter6.cx ∧
    ¬ Clifford.CliffordChain 6 ∧
    ∀ n : ℕ, 6 ≤ n → ¬ Clifford.CliffordChain n

example : Clifford.GenPosN Clifford.Counter6.cx =
    type_of% @Clifford.Counter6.cx_genPosN := rfl

example : (¬ Clifford.CliffordChain 6) =
    type_of% @Clifford.Counter6.not_cliffordChain_six := rfl

example : (∀ n : ℕ, 6 ≤ n → ¬ Clifford.CliffordChain n) =
    type_of% @Clifford.not_cliffordChain_of_six_le := rfl

theorem N5_BR (_h : BlindN5) : RealN5 :=
  ⟨Clifford.Counter6.cx_genPosN, Clifford.Counter6.not_cliffordChain_six,
    fun _ hn => Clifford.not_cliffordChain_of_six_le hn⟩

-- UNCLOSED N5_RB: RealN5 concerns plane-valued Chain/CliffordChain. The writer additionally
-- requires BlindGenPos BlindSix, absence of a sphere BlindClifford top object contained in the
-- plane, and failure of the recursively plane-restricted BlindCliffordFin for every n >= 6.
-- These require general-position, sphere/plane, and recursive predicate translation lemmas.

def BlindN4 : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ((∀ c : Fin n → ℂ, BlindGenPos c →
      ∃ X : Set BlindS, BlindCliffordFin n c X) ↔ n ≤ 5)

def RealN4 : Prop :=
  ∀ n : ℕ, Clifford.CliffordChain n ↔ n ≤ 5

example : RealN4 = type_of% @Clifford.cliffordChain_iff := rfl

theorem N4_BR (_h : BlindN4) : RealN4 := Clifford.cliffordChain_iff

-- UNCLOSED N4_RB: each n >= 1 requires equivalence between universal existence for the
-- sphere-valued, recursively plane-contained BlindCliffordFin and plane-valued CliffordChain,
-- together with BlindGenPos/GenPosN. liftS supplies only a real Chain-to-ChainS transport.

end

end BlindCompareFull
