import Mathlib

namespace PaperK3

/-! ## A. Bilinear form on ℝ⁶ -/

def B (X Y : Fin 6 → ℝ) : ℝ :=
  X 0*Y 0 - X 1*Y 1 - X 2*Y 2 - X 3*Y 3 - X 4*Y 5 - X 5*Y 4

theorem B_self_zero_iff (X : Fin 6 → ℝ) :
    B X X = 0 ↔ (X 0)^2 - ((X 1)^2 + (X 2)^2 + (X 3)^2) = 2 * (X 4) * (X 5) := by
  unfold B
  constructor <;> intro h <;> linear_combination h

/-- Tangency identity. NOTE: needs both cycle conditions `B X X = 0`, `B Y Y = 0`
(it is not a polynomial identity without them). -/
theorem tangency_identity (X Y : Fin 6 → ℝ) (hX : B X X = 0) (hY : B Y Y = 0) :
    -2 * X 4 * Y 4 * B X Y = (X 0*Y 4 - Y 0*X 4)^2 - ((X 1*Y 4 - Y 1*X 4)^2
      + (X 2*Y 4 - Y 2*X 4)^2 + (X 3*Y 4 - Y 3*X 4)^2) := by
  unfold B at *
  linear_combination (-(Y 4)^2) * hX - (X 4)^2 * hY

/-- The affine sphere with signed radius `r` and centre `(a,b,c)`. -/
noncomputable def sph (r a b c : ℝ) : Fin 6 → ℝ :=
  ![r, a, b, c, 1, (r^2 - (a^2 + b^2 + c^2)) / 2]

theorem sph_cycle (r a b c : ℝ) : B (sph r a b c) (sph r a b c) = 0 := by
  simp [B, sph]; ring

/-! ## B. Equal power -/

theorem equal_power {ι : Type*} (X : ι → Fin 6 → ℝ)
    (hX4 : ∀ i, X i 4 = 1)
    (hX5 : ∀ i, X i 5 = ((X i 0)^2 - ((X i 1)^2 + (X i 2)^2 + (X i 3)^2)) / 2)
    (P : Fin 6 → ℝ) (hP : ∀ i, B P (X i) = 0) (hP4 : P 4 ≠ 0) :
    ∀ i, (P 1 / P 4 - X i 1)^2 + (P 2 / P 4 - X i 2)^2 + (P 3 / P 4 - X i 3)^2
          - (P 0 / P 4 - X i 0)^2
        = (P 1 / P 4)^2 + (P 2 / P 4)^2 + (P 3 / P 4)^2 - (P 0 / P 4)^2 + 2 * (P 5 / P 4) := by
  intro i
  have h := hP i
  unfold B at h
  rw [hX4, hX5] at h
  have key : P 0 / P 4 * X i 0 - (P 1 / P 4 * X i 1 + P 2 / P 4 * X i 2 + P 3 / P 4 * X i 3)
      = ((X i 0)^2 - ((X i 1)^2 + (X i 2)^2 + (X i 3)^2)) / 2 + P 5 / P 4 := by
    field_simp
    linear_combination 2 * h
  linear_combination 2 * key

theorem equal_power_pair {ι : Type*} (X : ι → Fin 6 → ℝ)
    (hX4 : ∀ i, X i 4 = 1)
    (hX5 : ∀ i, X i 5 = ((X i 0)^2 - ((X i 1)^2 + (X i 2)^2 + (X i 3)^2)) / 2)
    (P : Fin 6 → ℝ) (hP : ∀ i, B P (X i) = 0) (hP4 : P 4 ≠ 0) (i j : ι) :
    (P 1 / P 4 - X i 1)^2 + (P 2 / P 4 - X i 2)^2 + (P 3 / P 4 - X i 3)^2
          - (P 0 / P 4 - X i 0)^2
      = (P 1 / P 4 - X j 1)^2 + (P 2 / P 4 - X j 2)^2 + (P 3 / P 4 - X j 3)^2
          - (P 0 / P 4 - X j 0)^2 := by
  rw [equal_power X hX4 hX5 P hP hP4 i, equal_power X hX4 hX5 P hP hP4 j]


/-! ## C. Regular tetrahedron -/

/-- Four unit spheres at the tetrahedron vertices plus an arbitrary fifth affine sphere. -/
noncomputable def tetraFam (r a b c : ℝ) : Fin 5 → Fin 6 → ℝ :=
  ![sph 1 1 1 1, sph 1 1 (-1) (-1), sph 1 (-1) 1 (-1), sph 1 (-1) (-1) 1, sph r a b c]

theorem tetraFam_4 (r a b c : ℝ) (i : Fin 5) : tetraFam r a b c i 4 = 1 := by
  fin_cases i <;> simp [tetraFam, sph]

theorem tetraFam_5 (r a b c : ℝ) (i : Fin 5) : tetraFam r a b c i 5 =
    ((tetraFam r a b c i 0)^2 - ((tetraFam r a b c i 1)^2 + (tetraFam r a b c i 2)^2
      + (tetraFam r a b c i 3)^2)) / 2 := by
  fin_cases i <;> simp [tetraFam, sph]

/-- Uniqueness of the equidistant point: the only point equidistant from the four
vertices is the origin, and the common squared distance is `3`. -/
theorem tetra_equidistant_unique (x y z d : ℝ)
    (h0 : (x-1)^2 + (y-1)^2 + (z-1)^2 = d)
    (h1 : (x-1)^2 + (y+1)^2 + (z+1)^2 = d)
    (h2 : (x+1)^2 + (y-1)^2 + (z+1)^2 = d)
    (h3 : (x+1)^2 + (y+1)^2 + (z-1)^2 = d) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ d = 3 := by
  have hx : x = 0 := by linear_combination (-1/8) * (h0 + h1 - h2 - h3)
  have hy : y = 0 := by linear_combination (-1/8) * (h0 - h1 + h2 - h3)
  have hz : z = 0 := by linear_combination (-1/8) * (h0 - h1 - h2 + h3)
  subst hx hy hz
  refine ⟨rfl, rfl, rfl, ?_⟩
  linear_combination -h0

/-- **E1 in ℝ³, regular tetrahedron**: for an arbitrary fifth sphere, any `P` B-orthogonal
to all five spheres with `P 4 ≠ 0` has affine point `P_X = (0,0,0)`. -/
theorem tetra_PX_origin (r a b c : ℝ) (P : Fin 6 → ℝ)
    (hP : ∀ i, B P (tetraFam r a b c i) = 0) (hP4 : P 4 ≠ 0) :
    P 1 / P 4 = 0 ∧ P 2 / P 4 = 0 ∧ P 3 / P 4 = 0 := by
  have E := equal_power (tetraFam r a b c) (tetraFam_4 r a b c) (tetraFam_5 r a b c) P hP hP4
  have e0 := E 0; have e1 := E 1; have e2 := E 2; have e3 := E 3
  simp [tetraFam, sph] at e0 e1 e2 e3
  set K := (P 1 / P 4)^2 + (P 2 / P 4)^2 + (P 3 / P 4)^2 - (P 0 / P 4)^2 + 2 * (P 5 / P 4)
  set d := K + (P 0 / P 4 - 1)^2
  obtain ⟨hx, hy, hz, -⟩ := tetra_equidistant_unique (P 1 / P 4) (P 2 / P 4) (P 3 / P 4) d
    (by linear_combination e0) (by linear_combination e1)
    (by linear_combination e2) (by linear_combination e3)
  exact ⟨hx, hy, hz⟩

/-! ## D. Inscribed / enclosing radii at `P_X = 0` -/

/-- The centres are at distance `√3` from the origin. -/
theorem tetra_centre_norm :
    Real.sqrt (1^2 + 1^2 + 1^2) = Real.sqrt 3 ∧
    Real.sqrt (1^2 + (-1)^2 + (-1)^2) = Real.sqrt 3 ∧
    Real.sqrt ((-1)^2 + 1^2 + (-1)^2) = Real.sqrt 3 ∧
    Real.sqrt ((-1)^2 + (-1)^2 + 1^2) = Real.sqrt 3 := by
  norm_num

/-- Metric contact: inscribed radius `√3 - 1` (external, `ρ + 1 = √3`), enclosing radius
`√3 + 1` (internal, `ρ - 1 = √3`); both radii are positive. -/
theorem tetra_radii_metric :
    0 < Real.sqrt 3 - 1 ∧ (Real.sqrt 3 - 1) + 1 = Real.sqrt 3 ∧
    0 < Real.sqrt 3 + 1 ∧ (Real.sqrt 3 + 1) - 1 = Real.sqrt 3 := by
  have h : 1 < Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨by linarith, by ring, by linarith, by ring⟩

/-- Oriented (Laguerre) tangency in the B-form: the enclosing sphere `sph (√3+1) 0 0 0`
and the inscribed sphere with opposite orientation `sph (1-√3) 0 0 0` (radius `√3 - 1`,
external contact) are B-orthogonal to all four unit spheres. -/
theorem tetra_tangent_B (i : Fin 4) :
    B (sph (Real.sqrt 3 + 1) 0 0 0) (tetraFam 0 0 0 0 (Fin.castSucc i)) = 0 ∧
    B (sph (1 - Real.sqrt 3) 0 0 0) (tetraFam 0 0 0 0 (Fin.castSucc i)) = 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> simp [B, tetraFam, sph] <;> constructor <;> linear_combination (-1/2) * h3

/-- Squared-distance form of the contact conditions: `|c_i|² = (ρ ± 1)²`. -/
theorem tetra_tangent_sq :
    (Real.sqrt 3 - 1 + 1)^2 = 3 ∧ (Real.sqrt 3 + 1 - 1)^2 = 3 ∧
    (Real.sqrt 3 - 1)^2 = 4 - 2 * Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩ <;> linear_combination h3

/-- Thm 3.6 conclusion in the regular-tetrahedron case: centre `P_X = 0`, inscribed radius
`√3 - 1`, enclosing radius `√3 + 1`, both tangent to all four unit spheres. -/
theorem tetra_E1_apollonius (r a b c : ℝ) (P : Fin 6 → ℝ)
    (hP : ∀ i, B P (tetraFam r a b c i) = 0) (hP4 : P 4 ≠ 0) :
    (P 1 / P 4 = 0 ∧ P 2 / P 4 = 0 ∧ P 3 / P 4 = 0) ∧
    (∀ i : Fin 4,
      B (sph (Real.sqrt 3 + 1) (P 1 / P 4) (P 2 / P 4) (P 3 / P 4))
        (tetraFam 0 0 0 0 (Fin.castSucc i)) = 0 ∧
      B (sph (1 - Real.sqrt 3) (P 1 / P 4) (P 2 / P 4) (P 3 / P 4))
        (tetraFam 0 0 0 0 (Fin.castSucc i)) = 0) := by
  obtain ⟨hx, hy, hz⟩ := tetra_PX_origin r a b c P hP hP4
  refine ⟨⟨hx, hy, hz⟩, ?_⟩
  rw [hx, hy, hz]
  exact tetra_tangent_B

/-! ## E(i). Scaled tetrahedron, common radius `r > 0` (centres `r·(±1,±1,±1)`). -/

noncomputable def tetraFamR (s r a b c : ℝ) : Fin 5 → Fin 6 → ℝ :=
  ![sph s s s s, sph s s (-s) (-s), sph s (-s) s (-s), sph s (-s) (-s) s, sph r a b c]

theorem tetraFamR_4 (s r a b c : ℝ) (i : Fin 5) : tetraFamR s r a b c i 4 = 1 := by
  fin_cases i <;> simp [tetraFamR, sph]

theorem tetraFamR_5 (s r a b c : ℝ) (i : Fin 5) : tetraFamR s r a b c i 5 =
    ((tetraFamR s r a b c i 0)^2 - ((tetraFamR s r a b c i 1)^2 + (tetraFamR s r a b c i 2)^2
      + (tetraFamR s r a b c i 3)^2)) / 2 := by
  fin_cases i <;> simp [tetraFamR, sph]

theorem tetraR_PX_origin (s r a b c : ℝ) (hs : 0 < s) (P : Fin 6 → ℝ)
    (hP : ∀ i, B P (tetraFamR s r a b c i) = 0) (hP4 : P 4 ≠ 0) :
    P 1 / P 4 = 0 ∧ P 2 / P 4 = 0 ∧ P 3 / P 4 = 0 := by
  have E := equal_power (tetraFamR s r a b c) (tetraFamR_4 s r a b c) (tetraFamR_5 s r a b c)
    P hP hP4
  have e0 := E 0; have e1 := E 1; have e2 := E 2; have e3 := E 3
  simp [tetraFamR, sph] at e0 e1 e2 e3
  have hs' : s ≠ 0 := hs.ne'
  have hx : s * (P 1 / P 4) = 0 := by linear_combination (-1/8) * (e0 + e1 - e2 - e3)
  have hy : s * (P 2 / P 4) = 0 := by linear_combination (-1/8) * (e0 - e1 + e2 - e3)
  have hz : s * (P 3 / P 4) = 0 := by linear_combination (-1/8) * (e0 - e1 - e2 + e3)
  exact ⟨(mul_eq_zero.mp hx).resolve_left hs', (mul_eq_zero.mp hy).resolve_left hs',
    (mul_eq_zero.mp hz).resolve_left hs'⟩

theorem tetraR_tangent_B (s : ℝ) (i : Fin 4) :
    B (sph (s * (Real.sqrt 3 + 1)) 0 0 0) (tetraFamR s 0 0 0 0 (Fin.castSucc i)) = 0 ∧
    B (sph (s * (1 - Real.sqrt 3)) 0 0 0) (tetraFamR s 0 0 0 0 (Fin.castSucc i)) = 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> simp [B, tetraFamR, sph] <;> constructor <;>
    linear_combination (-s^2/2) * h3

/-! ## E(iii). The four vertices are affinely independent. -/

theorem tetra_affineIndependent :
    AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw 0,
    Finset.weightedVSubOfPoint_apply] at hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  simp [Fin.sum_univ_succ] at h0 h1 h2 hw
  intro i
  fin_cases i <;> simp <;> linarith

end PaperK3

#print axioms PaperK3.B_self_zero_iff
#print axioms PaperK3.tangency_identity
#print axioms PaperK3.equal_power
#print axioms PaperK3.tetra_equidistant_unique
#print axioms PaperK3.tetra_PX_origin
#print axioms PaperK3.tetra_radii_metric
#print axioms PaperK3.tetra_tangent_B
#print axioms PaperK3.tetra_tangent_sq
#print axioms PaperK3.tetra_E1_apollonius
#print axioms PaperK3.tetraR_PX_origin
#print axioms PaperK3.tetraR_tangent_B
#print axioms PaperK3.tetra_affineIndependent
