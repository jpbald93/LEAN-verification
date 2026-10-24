import Fivecircles

open Affine EuclideanGeometry

/-- blind_7 verbatim. -/
def blind7_stmt : Prop :=
  ∀ (A T M : Fin 5 → ℂ)
    (hA : Function.Injective A) (hT : Function.Injective T) (hM : Function.Injective M)
    (hAT : ∀ i j, A i ≠ T j) (hAM : ∀ i j, A i ≠ M j) (hTM : ∀ i j, T i ≠ M j)
    (hcol : ∀ i : Fin 5, Collinear ℝ ({A (i - 1), A i, T (i + 1), T (i - 1)} : Set ℂ))
    (hcyc : ∀ i : Fin 5, Concyclic ({A (i - 1), A i, T i, M (i - 1), M i} : Set ℂ)),
    Concyclic (Set.range M) ∨ Collinear ℝ (Set.range M)

theorem rb_7 : (type_of% @Fivecircles.fivecircles) → blind7_stmt := by
  intro h A T M hA hT hM hAT hAM hTM hcol hcyc
  exact h A T M hA hT hM hAT hAM hTM hcol hcyc

theorem br_7 : blind7_stmt → (type_of% @Fivecircles.fivecircles) := by
  intro h A T M hA hT hM hAT hAM hTM hcol hcyc
  exact h A T M hA hT hM hAT hAM hTM hcol hcyc
