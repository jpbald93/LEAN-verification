import Arbelos

/-!
# Layer 15 comparison: classical arbelos statements (A1a–A5) vs the `Arbelos` library

The classical definitions and statements are copied verbatim from `PaperIClassical.lean`
(sha256 prefix `1c595a90ccb3925a`), namespace renamed to `L15CmpArbelos`. Each `cov_*` theorem
proves a classical statement from library theorems.
-/

open EuclideanGeometry RealInnerProductSpace MeasureTheory

local notation "E2" => EuclideanSpace ℝ (Fin 2)

noncomputable section

namespace L15CmpArbelos

/-! ## Verbatim classical definitions -/

/-- A circle `(c, t)` lying in the annulus between an outer circle `(O, R)` and an inner
circle `(o, ρ)`, tangent to both (externally to the inner, internally to the outer). -/
def ClassicalTangentToBoth (O : E2) (R : ℝ) (o : E2) (ρ : ℝ) (c : E2) (t : ℝ) : Prop :=
  0 < t ∧ dist c o = ρ + t ∧ dist c O = R - t

/-- A closed Steiner chain of `n` circles: each tangent to both given circles, each tangent
to the next one (cyclically), and with pairwise disjoint interiors. -/
def ClassicalSteinerChain (O : E2) (R : ℝ) (o : E2) (ρ : ℝ) (n : ℕ)
    (c : Fin n → E2) (t : Fin n → ℝ) : Prop :=
  (∀ i, ClassicalTangentToBoth O R o ρ (c i) (t i)) ∧
    (∀ i, dist (c i) (c (finRotate n i)) = t i + t (finRotate n i)) ∧
    (∀ i j, i ≠ j → t i + t j ≤ dist (c i) (c j))

/-- The (closed) arbelos region in the coordinates above. -/
def ClassicalArbelos (a b : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ dist z ((a + b : ℝ) : ℂ) ≤ a + b ∧ a ≤ dist z (a : ℂ) ∧
    b ≤ dist z ((2 * a + b : ℝ) : ℂ)}

/-! ## A1 twin circles -/

/-- A1a, verbatim classical statement. Covered by `Arbelos.twin_left`. -/
theorem cov_classical_A1a (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : 0 < z.im)
    (hperp : z.re + ρ = 2 * a)
    (hbig : dist z ((a + b : ℝ) : ℂ) = a + b - ρ)
    (hsmall : dist z (a : ℂ) = a + ρ) :
    ρ = a * b / (a + b) := by
  have hR : (0 : ℝ) ≤ a + b := by linarith
  exact Arbelos.twin_left ha hb ⟨z, ρ⟩ (by show z.re < 2 * a; linarith)
    (by
      rw [Arbelos.perpC, Arbelos.isTangent_vline_iff]
      show |z.re - 2 * a| = ρ
      rw [abs_of_neg (by linarith)]; linarith)
    ((Sphere.isIntTangent_iff_dist_center (s₁ := ⟨z, ρ⟩) (s₂ := Arbelos.bigS a b)).2
      ⟨hbig, hρ.le, hR⟩)
    ((Sphere.isExtTangent_iff_dist_center (s₁ := Arbelos.leftS a b) (s₂ := ⟨z, ρ⟩)).2
      ⟨by rw [dist_comm]; exact hsmall, ha.le, hρ.le⟩)

/-- A1b, verbatim classical statement. Covered by `Arbelos.twin_right`. -/
theorem cov_classical_A1b (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : 0 < z.im)
    (hperp : z.re - ρ = 2 * a)
    (hbig : dist z ((a + b : ℝ) : ℂ) = a + b - ρ)
    (hsmall : dist z ((2 * a + b : ℝ) : ℂ) = b + ρ) :
    ρ = a * b / (a + b) := by
  have hR : (0 : ℝ) ≤ a + b := by linarith
  exact Arbelos.twin_right ha hb ⟨z, ρ⟩ (by show 2 * a < z.re; linarith)
    (by
      rw [Arbelos.perpC, Arbelos.isTangent_vline_iff]
      show |z.re - 2 * a| = ρ
      rw [abs_of_pos (by linarith)]; linarith)
    ((Sphere.isIntTangent_iff_dist_center (s₁ := ⟨z, ρ⟩) (s₂ := Arbelos.bigS a b)).2
      ⟨hbig, hρ.le, hR⟩)
    ((Sphere.isExtTangent_iff_dist_center (s₁ := Arbelos.rightS a b) (s₂ := ⟨z, ρ⟩)).2
      ⟨by rw [dist_comm]; exact hsmall, hb.le, hρ.le⟩)

/-! ## A2 area -/

/-- The closed classical region and the library's region (`0 < im`) differ by a null set. -/
theorem volume_classicalArbelos (a b : ℝ) :
    volume (ClassicalArbelos a b) = volume (Arbelos.arbelosRegion a b) := by
  apply le_antisymm
  · calc volume (ClassicalArbelos a b)
        ≤ volume (Arbelos.arbelosRegion a b ∪ {z : ℂ | z.im = 0}) := by
          apply measure_mono
          intro z hz
          rcases hz.1.lt_or_eq with h | h
          · exact Or.inl ⟨h, hz.2⟩
          · exact Or.inr h.symm
      _ ≤ volume (Arbelos.arbelosRegion a b) + volume {z : ℂ | z.im = 0} := measure_union_le _ _
      _ = volume (Arbelos.arbelosRegion a b) := by rw [Arbelos.volume_realAxis, add_zero]
  · exact measure_mono fun z hz => ⟨hz.1.le, hz.2⟩

/-- A2b, verbatim classical statement. Covered by `Arbelos.arbelos_area` (plus null sets). -/
theorem cov_classical_A2b (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (D : ℂ) (hDre : D.re = 2 * a)
    (hDim : 0 < D.im) (hD : dist D ((a + b : ℝ) : ℂ) = a + b) :
    let C : ℂ := ((2 * a : ℝ) : ℂ)
    volume (ClassicalArbelos a b) =
      volume (Metric.closedBall (midpoint ℝ C D) (dist C D / 2)) := by
  intro C
  rw [volume_classicalArbelos, Arbelos.arbelos_area ha hb D (EuclideanGeometry.mem_sphere.2 hD)
    (by rw [Arbelos.perpC]; exact Arbelos.mem_vline_iff.2 hDre),
    Measure.addHaar_closedBall_eq_addHaar_ball]
  rfl

/-- A2a, verbatim classical statement. From A2b with `D = 2a + 2√(ab) i`. -/
theorem cov_classical_A2a (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (volume (ClassicalArbelos a b)).toReal = Real.pi * a * b := by
  have hab : 0 ≤ a * b := by positivity
  have hs : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt hab
  set D : ℂ := ⟨2 * a, 2 * Real.sqrt (a * b)⟩ with hDdef
  have hD : dist D ((a + b : ℝ) : ℂ) = a + b := by
    rw [← sq_eq_sq₀ dist_nonneg (by linarith), Arbelos.dist_sq_re_im]
    simp only [hDdef, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [hs]
  have hDim : 0 < D.im := by
    show 0 < 2 * Real.sqrt (a * b)
    have := Real.sqrt_pos.2 (mul_pos ha hb); linarith
  have h := cov_classical_A2b a b ha hb D rfl hDim hD
  simp only at h
  rw [h, Measure.addHaar_closedBall_eq_addHaar_ball, Complex.volume_ball]
  have hCD : dist ((2 * a : ℝ) : ℂ) D ^ 2 = 4 * (a * b) := by
    rw [Arbelos.dist_sq_re_im]
    simp only [hDdef, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [hs]
  have hr : 0 ≤ dist ((2 * a : ℝ) : ℂ) D / 2 := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.coe_toReal,
    NNReal.coe_real_pi, div_pow, hCD]
  ring

/-! ## A3 Pappus chain -/

/-- A3, verbatim classical statement (writer's Pappus indexing). Covered by
`Arbelos.pappus_unique` + `Arbelos.pappus_chain`. -/
theorem cov_classical_A3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℕ → ℂ) (ρ : ℕ → ℝ)
    (h0 : z 0 = ((2 * a + b : ℝ) : ℂ) ∧ ρ 0 = b)
    (hpos : ∀ n, 1 ≤ n → 0 < ρ n ∧ 0 < (z n).im)
    (hbig : ∀ n, 1 ≤ n → dist (z n) ((a + b : ℝ) : ℂ) = a + b - ρ n)
    (hsmall : ∀ n, 1 ≤ n → dist (z n) (a : ℂ) = a + ρ n)
    (hprev : ∀ n, 1 ≤ n → dist (z n) (z (n - 1)) = ρ n + ρ (n - 1))
    (hnew : ∀ n, 1 ≤ n → (z (n + 1), ρ (n + 1)) ≠ (z (n - 1), ρ (n - 1))) :
    ∀ n : ℕ, (z n).im = n * (2 * ρ n) := by
  have hR : (0 : ℝ) ≤ a + b := by linarith
  have hr : ∀ m, 0 < ρ m := by
    intro m; rcases m with _ | m
    · rw [h0.2]; exact hb
    · exact (hpos (m + 1) (by omega)).1
  have hc0 : (⟨z 0, ρ 0⟩ : Sphere ℂ) = Arbelos.rightS a b := by
    rw [h0.1, h0.2]; rfl
  have key := Arbelos.pappus_unique ha hb (fun n => ⟨z n, ρ n⟩) hc0 (fun n => hr n)
    (by
      intro n; rcases n with _ | n
      · show (⟨z 0, ρ 0⟩ : Sphere ℂ).IsIntTangent (Arbelos.bigS a b)
        rw [hc0, ← Arbelos.pappusCircle_zero ha hb]; exact Arbelos.pappus_tangent_big ha hb 0
      · exact (Sphere.isIntTangent_iff_dist_center (s₁ := ⟨z (n + 1), ρ (n + 1)⟩)
          (s₂ := Arbelos.bigS a b)).2 ⟨hbig (n + 1) (by omega), (hr _).le, hR⟩)
    (by
      intro n; rcases n with _ | n
      · show (Arbelos.leftS a b).IsExtTangent (⟨z 0, ρ 0⟩ : Sphere ℂ)
        rw [hc0, ← Arbelos.pappusCircle_zero ha hb]; exact Arbelos.pappus_tangent_left ha hb 0
      · exact (Sphere.isExtTangent_iff_dist_center (s₁ := Arbelos.leftS a b)
          (s₂ := ⟨z (n + 1), ρ (n + 1)⟩)).2
          ⟨by rw [dist_comm]; exact hsmall (n + 1) (by omega), ha.le, (hr _).le⟩)
    (by
      intro n
      have h := hprev (n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h
      exact (Sphere.isExtTangent_iff_dist_center (s₁ := ⟨z n, ρ n⟩)
          (s₂ := ⟨z (n + 1), ρ (n + 1)⟩)).2
          ⟨by show dist (z n) (z (n + 1)) = ρ n + ρ (n + 1); rw [dist_comm, h, add_comm],
            (hr _).le, (hr _).le⟩)
    (by
      intro n h
      apply hnew (n + 1) (by omega)
      simp only [Nat.add_sub_cancel]
      exact Prod.ext (congrArg Sphere.center h) (congrArg Sphere.radius h))
    (hpos 1 le_rfl).2
  intro n
  have h := Arbelos.pappus_chain (a := a) (b := b) n
  rw [← key n] at h
  exact h

/-! ## A4 Bankoff -/

/-- A4, verbatim classical statement. Covered by `Arbelos.bankoff`; the contact points given as
common points of the two tangent circles are the `IsExtTangentAt` points. -/
theorem cov_classical_A4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : 0 < z.im)
    (hbig : dist z ((a + b : ℝ) : ℂ) = a + b - ρ)
    (hsmall₁ : dist z (a : ℂ) = a + ρ)
    (hsmall₂ : dist z ((2 * a + b : ℝ) : ℂ) = b + ρ)
    (T₁ T₂ : ℂ) (hT₁ : dist T₁ (a : ℂ) = a ∧ dist T₁ z = ρ)
    (hT₂ : dist T₂ ((2 * a + b : ℝ) : ℂ) = b ∧ dist T₂ z = ρ)
    (w : ℂ) (R : ℝ) (hwC : dist w ((2 * a : ℝ) : ℂ) = R) (hw₁ : dist w T₁ = R)
    (hw₂ : dist w T₂ = R) :
    R = a * b / (a + b) := by
  have hR : (0 : ℝ) ≤ a + b := by linarith
  have hbig' : (⟨z, ρ⟩ : Sphere ℂ).IsIntTangent (Arbelos.bigS a b) :=
    (Sphere.isIntTangent_iff_dist_center (s₁ := ⟨z, ρ⟩) (s₂ := Arbelos.bigS a b)).2
      ⟨hbig, hρ.le, hR⟩
  have hleft' : (Arbelos.leftS a b).IsExtTangent ⟨z, ρ⟩ :=
    (Sphere.isExtTangent_iff_dist_center (s₁ := Arbelos.leftS a b) (s₂ := ⟨z, ρ⟩)).2
      ⟨by rw [dist_comm]; exact hsmall₁, ha.le, hρ.le⟩
  have hright' : (Arbelos.rightS a b).IsExtTangent ⟨z, ρ⟩ :=
    (Sphere.isExtTangent_iff_dist_center (s₁ := Arbelos.rightS a b) (s₂ := ⟨z, ρ⟩)).2
      ⟨by rw [dist_comm]; exact hsmall₂, hb.le, hρ.le⟩
  have hT₁' : (Arbelos.leftS a b).IsExtTangentAt ⟨z, ρ⟩ T₁ :=
    ⟨EuclideanGeometry.mem_sphere.2 hT₁.1, EuclideanGeometry.mem_sphere.2 hT₁.2,
      dist_add_dist_eq_iff.1 (by
        show dist (a : ℂ) T₁ + dist T₁ z = dist (a : ℂ) z
        rw [dist_comm (a : ℂ) T₁, hT₁.1, hT₁.2, dist_comm, hsmall₁])⟩
  have hT₂' : (Arbelos.rightS a b).IsExtTangentAt ⟨z, ρ⟩ T₂ :=
    ⟨EuclideanGeometry.mem_sphere.2 hT₂.1, EuclideanGeometry.mem_sphere.2 hT₂.2,
      dist_add_dist_eq_iff.1 (by
        show dist ((2 * a + b : ℝ) : ℂ) T₂ + dist T₂ z = dist ((2 * a + b : ℝ) : ℂ) z
        rw [dist_comm ((2 * a + b : ℝ) : ℂ) T₂, hT₂.1, hT₂.2, dist_comm, hsmall₂])⟩
  exact Arbelos.bankoff ha hb ⟨z, ρ⟩ hbig' hleft' hright' hz T₁ T₂ hT₁' hT₂' ⟨w, R⟩
    (EuclideanGeometry.mem_sphere.2 (by rw [dist_comm]; exact hwC))
    (EuclideanGeometry.mem_sphere.2 (by rw [dist_comm]; exact hw₁))
    (EuclideanGeometry.mem_sphere.2 (by rw [dist_comm]; exact hw₂))

/-! ## A5 Steiner porism -/

/-- A5 restricted to `1 ≤ n` (the only added hypothesis). Covered by
`Arbelos.steiner_porism_strong` (published commit 53d0573) transported along the isometry
`EuclideanSpace ℝ (Fin 2) ≃ ℂ`. -/
theorem cov_classical_A5_part (O o : E2) (R ρ : ℝ) (hρ : 0 < ρ) (hin : dist O o + ρ < R)
    (n : ℕ) (hn : 1 ≤ n)
    (hchain : ∃ c t, ClassicalSteinerChain O R o ρ n c t)
    (c₀ : E2) (t₀ : ℝ) (h₀ : ClassicalTangentToBoth O R o ρ c₀ t₀) :
    ∃ c t, ClassicalSteinerChain O R o ρ n c t ∧ ∃ i, c i = c₀ ∧ t i = t₀ := by
  obtain _ | k := n
  · omega
  obtain ⟨c, t, hct, hnext, hdisj⟩ := hchain
  let e : E2 ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have hR : 0 < R := by linarith [dist_nonneg (x := O) (y := o)]
  let S₁ : Sphere ℂ := ⟨e o, ρ⟩
  let S₂ : Sphere ℂ := ⟨e O, R⟩
  have tang : ∀ (x : E2) (r : ℝ), ClassicalTangentToBoth O R o ρ x r →
      0 < r ∧ S₁.IsExtTangent ⟨e x, r⟩ ∧ (⟨e x, r⟩ : Sphere ℂ).IsIntTangent S₂ := by
    rintro x r ⟨hr, h1, h2⟩
    refine ⟨hr, (Sphere.isExtTangent_iff_dist_center (s₁ := S₁) (s₂ := ⟨e x, r⟩)).2
      ⟨?_, hρ.le, hr.le⟩, (Sphere.isIntTangent_iff_dist_center (s₁ := ⟨e x, r⟩) (s₂ := S₂)).2
      ⟨?_, hr.le, hR.le⟩⟩
    · show dist (e o) (e x) = ρ + r; rw [e.dist_map, dist_comm, h1]
    · show dist (e x) (e O) = R - r; rw [e.dist_map, h2]
  let f : ZMod (k + 1) → Fin (k + 1) := fun i => i
  have hadd : ∀ i : ZMod (k + 1), f (i + 1) = f i + 1 := fun i => rfl
  let cc : ZMod (k + 1) → Sphere ℂ := fun i => ⟨e (c (f i)), t (f i)⟩
  have hr1 : ∀ j : Fin (k + 1), finRotate (k + 1) j = j + 1 := fun j => finRotate_apply j
  have hchain' : Arbelos.IsSteinerChain S₁ S₂ (k + 1) cc := by
    intro i
    obtain ⟨h0, h1, h2⟩ := tang _ _ (hct (f i))
    have h := hnext (f i)
    rw [hr1, ← hadd] at h
    refine ⟨h0, h1, h2, (Sphere.isExtTangent_iff_dist_center (s₁ := cc i) (s₂ := cc (i + 1))).2
      ⟨?_, (hct (f i)).1.le, (hct (f (i + 1))).1.le⟩⟩
    show dist (e (c (f i))) (e (c (f (i + 1)))) = t (f i) + t (f (i + 1))
    rw [e.dist_map]; exact h
  have hdisc : Arbelos.HasDisjointDiscs cc := by
    rw [Arbelos.hasDisjointDiscs_iff hchain']
    intro i j hij
    show t (f i) + t (f j) ≤ dist (e (c (f i))) (e (c (f j)))
    rw [e.dist_map]; exact hdisj (f i) (f j) hij
  obtain ⟨d, hd, hd0, -, hdd⟩ := Arbelos.steiner_porism_strong S₁ S₂ hρ
    (by show dist (e o) (e O) < R - ρ; rw [e.dist_map, dist_comm]; linarith)
    (k + 1) cc hchain' ⟨e c₀, t₀⟩ (tang _ _ h₀).2.1 (tang _ _ h₀).2.2
  have hdd' := (Arbelos.hasDisjointDiscs_iff hd).1 (hdd hdisc)
  have back : ∀ (x : ℂ) (y : E2), dist (e.symm x) y = dist x (e y) := by
    intro x y; rw [← e.dist_map, e.apply_symm_apply]
  let g : Fin (k + 1) → ZMod (k + 1) := fun i => i
  have hgadd : ∀ i : Fin (k + 1), g (i + 1) = g i + 1 := fun i => rfl
  refine ⟨fun i => e.symm (d (g i)).center, fun i => (d (g i)).radius, ⟨?_, ?_, ?_⟩, 0, ?_, ?_⟩
  · intro i
    obtain ⟨h0, h1, h2, -⟩ := hd (g i)
    obtain ⟨h1, -, -⟩ := Sphere.isExtTangent_iff_dist_center.1 h1
    obtain ⟨h2, -, -⟩ := Sphere.isIntTangent_iff_dist_center.1 h2
    refine ⟨h0, ?_, ?_⟩
    · show dist (e.symm (d (g i)).center) o = ρ + (d (g i)).radius
      rw [back, dist_comm]; exact h1
    · show dist (e.symm (d (g i)).center) O = R - (d (g i)).radius
      rw [back]; exact h2
  · intro i
    obtain ⟨-, -, -, h3⟩ := hd (g i)
    obtain ⟨h3, -, -⟩ := Sphere.isExtTangent_iff_dist_center.1 h3
    rw [hr1]
    show dist (e.symm (d (g i)).center) (e.symm (d (g (i + 1))).center) =
      (d (g i)).radius + (d (g (i + 1))).radius
    rw [hgadd, e.symm.dist_map]; exact h3
  · intro i j hij
    show (d (g i)).radius + (d (g j)).radius ≤ dist (e.symm (d (g i)).center) (e.symm (d (g j)).center)
    rw [e.symm.dist_map]; exact hdd' hij
  · show e.symm (d (g 0)).center = c₀
    rw [show g 0 = 0 from rfl, hd0]; exact e.symm_apply_apply c₀
  · show (d (g 0)).radius = t₀
    rw [show g 0 = 0 from rfl, hd0]

/-- A5 as written is false for `n = 0` (writer slip): `Fin 0` is empty, so the empty chain is a
`ClassicalSteinerChain`, but no index `i : Fin 0` can carry the given circle. Configuration:
`O = o = 0`, `R = 3`, `ρ = 1`, `c₀` at distance 2 from the centre, `t₀ = 1`. -/
theorem classical_A5_false_n0 :
    ¬ (∀ (O o : E2) (R ρ : ℝ) (_hρ : 0 < ρ) (_hin : dist O o + ρ < R) (n : ℕ)
      (_hchain : ∃ c t, ClassicalSteinerChain O R o ρ n c t)
      (c₀ : E2) (t₀ : ℝ) (_h₀ : ClassicalTangentToBoth O R o ρ c₀ t₀),
      ∃ c t, ClassicalSteinerChain O R o ρ n c t ∧ ∃ i, c i = c₀ ∧ t i = t₀) := by
  intro h
  let e : E2 ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have h2 : dist (e.symm 2) (0 : E2) = 2 := by
    rw [dist_zero_right, LinearIsometryEquiv.norm_map]
    norm_num
  obtain ⟨c, t, -, i, -⟩ := h 0 0 3 1 one_pos (by rw [dist_self]; norm_num) 0
    ⟨Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩ (e.symm 2) 1
    ⟨one_pos, by rw [h2]; norm_num, by rw [h2]; norm_num⟩
  exact i.elim0


/-! ## I1c (inversion of a circle not through the centre), via `Arbelos.image_inversion_sphere` -/

/-- Mathlib's inversion commutes with a linear isometry equivalence. -/
theorem map_inversion (f : E2 ≃ₗᵢ[ℝ] ℂ) (O : E2) (k : ℝ) (x : E2) :
    f (inversion O k x) = inversion (f O) k (f x) := by
  simp only [inversion, vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, f.dist_map]

/-- I1c, verbatim classical statement. Covered by `Arbelos.image_inversion_sphere` (in `ℂ`),
transported along `E2 ≃ ℂ`. -/
theorem cov_classical_I1c (O : E2) (k : ℝ) (hk : 0 < k) (c : E2) (ρ : ℝ) (hρ : 0 < ρ)
    (hO : dist O c ≠ ρ) :
    ∃ c' : E2, ∃ ρ' : ℝ, 0 < ρ' ∧ inversion O k '' Metric.sphere c ρ = Metric.sphere c' ρ' := by
  let f : E2 ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have hp : ‖(⟨f c, ρ⟩ : Sphere ℂ).center - f O‖ ^ 2 ≠ (⟨f c, ρ⟩ : Sphere ℂ).radius ^ 2 := by
    show ‖f c - f O‖ ^ 2 ≠ ρ ^ 2
    rw [← dist_eq_norm, f.dist_map, dist_comm]
    intro h
    exact hO ((sq_eq_sq₀ dist_nonneg hρ.le).1 h)
  have himg := Arbelos.image_inversion_sphere (c := f O) hk.ne' (s := ⟨f c, ρ⟩) hρ.le hp
  set T := Arbelos.invSphere (f O) k ⟨f c, ρ⟩ with hT
  have hden : 0 < |‖f c - f O‖ ^ 2 - ρ ^ 2| := abs_pos.2 (sub_ne_zero.2 hp)
  refine ⟨f.symm T.center, T.radius, ?_, ?_⟩
  · show 0 < k ^ 2 * ρ / |‖f c - f O‖ ^ 2 - ρ ^ 2|
    positivity
  · have hS : ((⟨f c, ρ⟩ : Sphere ℂ) : Set ℂ) = f '' Metric.sphere c ρ := by
      rw [LinearIsometryEquiv.image_sphere]
    have hT' : (T : Set ℂ) = Metric.sphere T.center T.radius := rfl
    rw [hS, hT', Set.image_image] at himg
    have h2 := congrArg (fun X => f.symm '' X) himg
    simp only [Set.image_image, LinearIsometryEquiv.image_sphere] at h2
    rw [← h2]
    apply Set.image_congr
    intro x _
    rw [← map_inversion, LinearIsometryEquiv.symm_apply_apply]

end L15CmpArbelos

#print axioms L15CmpArbelos.cov_classical_A1a
#print axioms L15CmpArbelos.cov_classical_A1b
#print axioms L15CmpArbelos.cov_classical_A2a
#print axioms L15CmpArbelos.cov_classical_A2b
#print axioms L15CmpArbelos.cov_classical_A3
#print axioms L15CmpArbelos.cov_classical_A4
#print axioms L15CmpArbelos.cov_classical_A5_part
#print axioms L15CmpArbelos.classical_A5_false_n0
#print axioms L15CmpArbelos.cov_classical_I1c
