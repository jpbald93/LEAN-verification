import Clifford
open Clifford Complex ComplexConjugate OnePoint
namespace ReviewCheck

/-- The centres `2t − 2i t²`, `t = 1..6` (Astra's counterexample to the uniqueness of the
even-level Clifford point under `ChainS`). -/
def c : Fin 6 → ℂ :=
  ![⟨2,-2⟩,⟨4,-8⟩,⟨6,-18⟩,⟨8,-32⟩,⟨10,-50⟩,⟨12,-72⟩]

theorem gp : GenPosN c := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | (intro h; have := congrArg Complex.im h; norm_num [c] at this)
  · intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk <;>
      refine ⟨?_, ?_⟩ <;> intro h <;> have := congrArg Complex.im h <;>
      norm_num [c, triP, cycP, det3] at this

theorem four (i : Fin 6) (j : Fin 5) :
    ChainS 4 ((c ∘ i.succAbove) ∘ j.succAbove)
      {((4 * I : ℂ) : OnePoint ℂ)} := by
  have hd := ((gp.comp_succAbove i).comp_succAbove j).pos4
  have hf := chain4_ofS ((c ∘ i.succAbove) ∘ j.succAbove) hd
  have he : miquel (((c ∘ i.succAbove) ∘ j.succAbove) 0)
      (((c ∘ i.succAbove) ∘ j.succAbove) 1)
      (((c ∘ i.succAbove) ∘ j.succAbove) 2)
      (((c ∘ i.succAbove) ∘ j.succAbove) 3) = 4 * I := by
    rw [miquel, div_eq_iff hd.mD_ne_zero]
    fin_cases i <;> fin_cases j <;>
      norm_num [Function.comp_def, Fin.succAbove, Fin.lt_def,
        Fin.castSucc, Fin.succ, Fin.castAdd, Fin.castLE, c] <;>
      apply Complex.ext <;> norm_num [mN, mD, det4, det3, pow_two]
  rwa [he] at hf

theorem five (i : Fin 6) :
    ChainS 5 (c ∘ i.succAbove) (lineS (4 * I) 1) := by
  refine ⟨Or.inr ⟨_, _, one_ne_zero, rfl⟩,
    fun j => ⟨_, four i j, ?_⟩⟩
  exact mem_lineS (t := 0) (by simp)

theorem six_finite : ChainS 6 c {((4 * I : ℂ) : OnePoint ℂ)} := by
  refine ⟨_, rfl, fun i => ⟨_, five i, ?_⟩⟩
  exact mem_lineS (t := 0) (by simp)

theorem six_infty : ChainS 6 c {∞} :=
  ⟨_, rfl, fun i => ⟨_, five i, Or.inl rfl⟩⟩

open Clifford.MorleyKernel

/-- Uniqueness of the even-level Clifford point fails for `ChainS`: the same configuration has both
`{4i}` and `{∞}` as level-6 objects. -/
theorem not_UniqEven : ¬ (∀ (k : ℕ) (d : Fin (2*k+4) → ℂ),
    GenPosN d → ∀ p : OnePoint ℂ,
    ChainS (2*k+4) d {p} → p = EptInf (2*k+4) d) := by
  intro U
  have e1 := U 1 c gp _ six_finite
  have e2 := U 1 c gp _ six_infty
  exact OnePoint.coe_ne_infty (4 * I : ℂ) (e1.trans e2.symm)

#print axioms not_UniqEven
end ReviewCheck
