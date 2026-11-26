import Clifford.MorleyKernel

/-! Layer 13 stage 4b: blind statements with library predicates substituted. -/

open Clifford

namespace BlindNorm

/-- Blind statement 1, library predicates substituted. -/
def blind_1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ c : Fin n → ℂ, GenPosN c → ∃ X, ChainS n c X

/-- Blind statement 2, library predicates substituted. -/
def blind_2 : Prop :=
  ∀ (k : ℕ) (d : Fin (2 * k + 5) → ℂ), GenPosN d →
    ∃ Y, IsGCircleS Y ∧ ∀ i : Fin (2 * k + 5),
      ∃ p : OnePoint ℂ, ChainS (2 * k + 4) (d ∘ i.succAbove) {p} ∧ p ∈ Y

/-- Blind statement 3, library predicates substituted. -/
def blind_3 : Prop :=
  ∀ (k : ℕ) (c : Fin (2 * k + 6) → ℂ), GenPosN c → ∀ i : Fin (2 * k + 6),
    ∃ Y, IsGCircleS Y ∧ (∃ p : OnePoint ℂ, ChainS (2 * k + 6) c {p} ∧ p ∈ Y) ∧
      ∀ j : Fin (2 * k + 5),
        ∃ q : OnePoint ℂ, ChainS (2 * k + 4) ((c ∘ i.succAbove) ∘ j.succAbove) {q} ∧ q ∈ Y

/-! ## N1 -/

/-- The real side as stated by the library (type read off by `type_of%`). -/
abbrev realN1 : Prop := ∀ n : ℕ, 3 ≤ n → CliffordChainS n

example : realN1 = type_of% @Clifford.MorleyKernel.cliffordChainS_inf := rfl

theorem N1_BR (h : blind_1) : realN1 := fun n hn c hc => h n (by omega) c hc

theorem N1_RB (h : realN1) : blind_1 := by
  intro n hn c hc
  match n, c, hc, hn with
  | 1, c, _, _ => exact ⟨_, rfl⟩
  | 2, c, _, _ => exact ⟨_, rfl⟩
  | n + 3, c, hc, _ => exact h (n + 3) (by omega) c hc

/-! ## Shared plumbing (unfolding-only; local copies, no library proof bodies invoked) -/

theorem genPos_comp {n : ℕ} {c : Fin (n + 1) → ℂ} (h : GenPosN c) (i : Fin (n + 1)) :
    GenPosN (c ∘ i.succAbove) :=
  ⟨fun _ _ hab => h.1 _ _ (Fin.succAbove_right_injective.ne hab),
    fun _ _ _ h1 h2 => h.2 _ _ _ (Fin.strictMono_succAbove i h1) (Fin.strictMono_succAbove i h2)⟩

theorem unfold_odd {m : ℕ} {c : Fin (2 * m + 3) → ℂ} {X : Set (OnePoint ℂ)} :
    ChainS (2 * m + 3) c X ↔
      IsGCircleS X ∧ ∀ i : Fin (2 * m + 3), ∃ p, ChainS (2 * m + 2) (c ∘ i.succAbove) {p} ∧ p ∈ X := by
  show ChainS ((2 * m) + 3) c X ↔ _
  rw [ChainS, if_pos (by omega)]

theorem unfold_even {m : ℕ} {c : Fin (2 * m + 4) → ℂ} {X : Set (OnePoint ℂ)} :
    ChainS (2 * m + 4) c X ↔
      ∃ p, X = {p} ∧ ∀ i : Fin (2 * m + 4), ∃ Y, ChainS (2 * m + 3) (c ∘ i.succAbove) Y ∧ p ∈ Y := by
  show ChainS ((2 * m + 1) + 3) c X ↔ _
  rw [ChainS, if_neg (by omega)]

/-! ## Library facts, stated as hypotheses (types read by `type_of%`; never invoked) -/

open Clifford.MorleyKernel in
abbrev H4 : Prop := type_of% @Clifford.MorleyKernel.h4_pt_inf
open Clifford.MorleyKernel in
abbrev Hodd : Prop := type_of% @Clifford.MorleyKernel.hodd_inf_all'
open Clifford.MorleyKernel in
abbrev Heven : Prop := type_of% @Clifford.MorleyKernel.heven_inf_all

open Clifford.MorleyKernel in
/- Canonical point is a level object: `P` from the (hypothesised) library incidences,
re-proved here by the same induction (unfolding only). -/
theorem canon_chain (h4 : H4) (heven : Heven) :
    ∀ (k : ℕ) (c : Fin (2 * k + 4) → ℂ), GenPosN c →
      ChainS (2 * k + 4) c {EptInf (2 * k + 4) c} := by
  intro k
  induction k with
  | zero => exact h4
  | succ k ih =>
    intro c hc
    have hc' : GenPosN (c : Fin (2 * k + 6) → ℂ) := hc
    show ChainS (2 * (k + 1) + 4) c {EptInf (2 * k + 6) c}
    rw [unfold_even]
    refine ⟨_, rfl, fun i => ?_⟩
    obtain ⟨Y, hY, hE, hj⟩ := heven k c hc' i
    refine ⟨Y, ?_, hE⟩
    show ChainS (2 * (k + 1) + 3) _ Y
    rw [unfold_odd]
    exact ⟨hY, fun j => ⟨_, ih _ (genPos_comp (genPos_comp hc' i) j), hj j⟩⟩

/-! ## N2 -/

open Clifford.MorleyKernel in
abbrev realN2 : Prop := type_of% @Clifford.MorleyKernel.hodd_inf_all'

/- R→B: canonical point is a certified level object (`canon_chain`), so it witnesses the blind
existential. Uses `h4`, `heven` only to build `canon_chain`; `hodd` supplies `Y`. -/
open Clifford.MorleyKernel in
theorem N2_RB (h4 : H4) (heven : Heven) (hodd : realN2) : blind_2 := by
  intro k d hd
  obtain ⟨Y, hY, hi⟩ := hodd k d hd
  exact ⟨Y, hY, fun i =>
    ⟨_, canon_chain h4 heven k (d ∘ i.succAbove) (genPos_comp hd i), hi i⟩⟩

/- The one missing ingredient for B→R: an even-level object is the canonical point. -/
open Clifford.MorleyKernel in
def UniqEven : Prop :=
  ∀ (k : ℕ) (d : Fin (2 * k + 4) → ℂ), GenPosN d → ∀ p : OnePoint ℂ,
    ChainS (2 * k + 4) d {p} → p = EptInf (2 * k + 4) d

/- B→R holds *given* `UniqEven`; without it the blind existential does not name the point. -/
open Clifford.MorleyKernel in
theorem N2_BR_of_uniq (U : UniqEven) (h : blind_2) : realN2 := by
  intro k d hd
  obtain ⟨Y, hY, hi⟩ := h k d hd
  refine ⟨Y, hY, fun i => ?_⟩
  obtain ⟨p, hp, hpY⟩ := hi i
  rwa [U k _ (genPos_comp hd i) p hp] at hpY

/-! ## N3 -/

open Clifford.MorleyKernel in
abbrev realN3 : Prop := type_of% @Clifford.MorleyKernel.heven_inf_all

open Clifford.MorleyKernel in
theorem N3_RB (h4 : H4) (heven : Heven) : blind_3 := by
  intro k c hc i
  obtain ⟨Y, hY, hE, hj⟩ := heven k c hc i
  refine ⟨Y, hY, ⟨_, canon_chain h4 heven (k + 1) c hc, hE⟩, fun j => ?_⟩
  exact ⟨_, canon_chain h4 heven k _ (genPos_comp (genPos_comp hc i) j), hj j⟩

open Clifford.MorleyKernel in
theorem N3_BR_of_uniq (U : UniqEven) (h : blind_3) : realN3 := by
  intro k c hc i
  obtain ⟨Y, hY, ⟨p, hp, hpY⟩, hj⟩ := h k c hc i
  have e : p = EptInf (2 * k + 6) c := U (k + 1) c hc p hp
  refine ⟨Y, hY, e ▸ hpY, fun j => ?_⟩
  obtain ⟨q, hq, hqY⟩ := hj j
  have e' := U k _ (genPos_comp (genPos_comp hc i) j) q hq
  exact e' ▸ hqY

end BlindNorm
