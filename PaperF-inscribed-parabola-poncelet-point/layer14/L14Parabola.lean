import QuadMiquel.ParabolaPoints

/-!
# Layer 14 (Part A): Mathlib-only restatements of the parabola theorems

Every `l14_*` theorem below has a statement mentioning only Mathlib notions. The four lines are
`line[ℝ, pᵢ, qᵢ]` with `pᵢ ≠ qᵢ`; general position is stated with `AffineSubspace.Parallel` and
common points; the six vertices are points `aᵢⱼ` lying on both lines; the four triangles are
Mathlib triangles with the given vertices; orthocentres, circumspheres, reflections and orthogonal
projections are Mathlib's. The Miquel point is any point `M` on the four circumspheres
(`l14_miquel_existsUnique` shows there is exactly one). The directrix is the affine span of the
four orthocentres, the parabola is `{z | dist z M = Metric.infDist z S}`, and the vertex is the
midpoint of `M` and its orthogonal projection on `S`.
The `l14b_*` lemmas are the bridges to the library's own definitions; the `l14w_*` theorems are
explicit witnesses (non-vacuity).
-/

open Complex ComplexConjugate

namespace QuadMiquel

/-! ### Bridges -/

theorem l14b_carrier {p q : ℂ} (h : p ≠ q) :
    (⟨p, q - p⟩ : Line).carrier = (line[ℝ, p, q] : Set ℂ) := by
  rw [carrier_eq_line _ (sub_ne_zero.2 h.symm)]; simp

theorem l14b_mem {p q z : ℂ} (h : p ≠ q) : z ∈ (⟨p, q - p⟩ : Line).carrier ↔ z ∈ line[ℝ, p, q] := by
  rw [l14b_carrier h]; rfl

theorem l14b_mem_iff {p q z : ℂ} (h : p ≠ q) : z ∈ line[ℝ, p, q] ↔ cr (q - p) (z - p) = 0 := by
  rw [← l14b_mem h]; rfl

theorem l14b_genPos {p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℂ}
    (h₁ : p₁ ≠ q₁) (h₂ : p₂ ≠ q₂) (h₃ : p₃ ≠ q₃) (h₄ : p₄ ≠ q₄)
    (n₁₂ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₂, q₂])
    (n₁₃ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₃, q₃])
    (n₁₄ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₄, q₄])
    (n₂₃ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₃, q₃])
    (n₂₄ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₄, q₄])
    (n₃₄ : ¬ line[ℝ, p₃, q₃].Parallel line[ℝ, p₄, q₄])
    (c₁₂₃ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃])
    (c₁₂₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₄, q₄])
    (c₁₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
    (c₂₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄]) :
    GenPos ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ := by
  rw [genPos_iff]
  simp only [l14b_mem h₁, l14b_mem h₂, l14b_mem h₃, l14b_mem h₄, add_sub_cancel]
  exact ⟨⟨sub_ne_zero.2 h₁.symm, sub_ne_zero.2 h₂.symm, sub_ne_zero.2 h₃.symm,
    sub_ne_zero.2 h₄.symm⟩, ⟨n₁₂, n₁₃, n₁₄, n₂₃, n₂₄, n₃₄⟩, c₁₂₃, c₁₂₄, c₁₃₄, c₂₃₄⟩

theorem l14b_meet {p q p' q' a : ℂ} (h : p ≠ q) (h' : p' ≠ q')
    (hc : cr (⟨p, q - p⟩ : Line).d (⟨p', q' - p'⟩ : Line).d ≠ 0)
    (ha : a ∈ line[ℝ, p, q] ∧ a ∈ line[ℝ, p', q']) : a = meet ⟨p, q - p⟩ ⟨p', q' - p'⟩ :=
  (meet_eq_iff (by rw [cr_anti]; exact neg_ne_zero.2 hc) a).1 ⟨(l14b_mem h).2 ha.1, (l14b_mem h').2 ha.2⟩

theorem l14b_setup {p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ : ℂ}
    (h₁ : p₁ ≠ q₁) (h₂ : p₂ ≠ q₂) (h₃ : p₃ ≠ q₃) (h₄ : p₄ ≠ q₄)
    (n₁₂ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₂, q₂])
    (n₁₃ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₃, q₃])
    (n₁₄ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₄, q₄])
    (n₂₃ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₃, q₃])
    (n₂₄ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₄, q₄])
    (n₃₄ : ¬ line[ℝ, p₃, q₃].Parallel line[ℝ, p₄, q₄])
    (c₁₂₃ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃])
    (c₁₂₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₄, q₄])
    (c₁₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
    (c₂₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
    (m₁₂ : a₁₂ ∈ line[ℝ, p₁, q₁] ∧ a₁₂ ∈ line[ℝ, p₂, q₂])
    (m₁₃ : a₁₃ ∈ line[ℝ, p₁, q₁] ∧ a₁₃ ∈ line[ℝ, p₃, q₃])
    (m₁₄ : a₁₄ ∈ line[ℝ, p₁, q₁] ∧ a₁₄ ∈ line[ℝ, p₄, q₄])
    (m₂₃ : a₂₃ ∈ line[ℝ, p₂, q₂] ∧ a₂₃ ∈ line[ℝ, p₃, q₃])
    (m₂₄ : a₂₄ ∈ line[ℝ, p₂, q₂] ∧ a₂₄ ∈ line[ℝ, p₄, q₄])
    (m₃₄ : a₃₄ ∈ line[ℝ, p₃, q₃] ∧ a₃₄ ∈ line[ℝ, p₄, q₄]) :
    GenPos ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ ∧
    a₁₂ = meet ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ∧ a₁₃ = meet ⟨p₁, q₁ - p₁⟩ ⟨p₃, q₃ - p₃⟩ ∧
    a₁₄ = meet ⟨p₁, q₁ - p₁⟩ ⟨p₄, q₄ - p₄⟩ ∧ a₂₃ = meet ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ∧
    a₂₄ = meet ⟨p₂, q₂ - p₂⟩ ⟨p₄, q₄ - p₄⟩ ∧ a₃₄ = meet ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ := by
  have hG := l14b_genPos h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄
  exact ⟨hG, l14b_meet h₁ h₂ hG.p12 m₁₂, l14b_meet h₁ h₃ hG.p13 m₁₃, l14b_meet h₁ h₄ hG.p14 m₁₄,
    l14b_meet h₂ h₃ hG.p23 m₂₃, l14b_meet h₂ h₄ hG.p24 m₂₄, l14b_meet h₃ h₄ hG.p34 m₃₄⟩

theorem l14b_tri {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    T = ⟨![a, b, c], affineIndependent_iff_not_collinear_set.2 hn⟩ :=
  Affine.Simplex.ext fun i => by rw [e]

theorem l14b_orthocenter {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : T.orthocenter = ortho a b c := by
  rw [ortho_eq_orthocenter hn, ← l14b_tri e hn]

theorem l14b_circumcenter {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : T.circumcenter = circ a b c := by
  rw [circ_eq_circumcenter hn, ← l14b_tri e hn]

theorem l14b_mem_circumsphere {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) (z : ℂ) :
    z ∈ T.circumsphere ↔ z ∈ Metric.sphere (circ a b c) (dist a (circ a b c)) := by
  have h0 : T.points 0 = a := by rw [e]; rfl
  rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center,
    Affine.Simplex.circumsphere_radius, ← T.dist_circumcenter_eq_circumradius 0, h0,
    l14b_circumcenter e hn, Metric.mem_sphere]

theorem l14b_setupT {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄)
    {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![meet L₂ L₃, meet L₂ L₄, meet L₃ L₄])
    (e₂ : T₂.points = ![meet L₁ L₃, meet L₁ L₄, meet L₃ L₄])
    (e₃ : T₃.points = ![meet L₁ L₂, meet L₁ L₄, meet L₂ L₄])
    (e₄ : T₄.points = ![meet L₁ L₂, meet L₁ L₃, meet L₂ L₃]) :
    T₁.orthocenter = ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) ∧
    T₂.orthocenter = ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) ∧
    T₃.orthocenter = ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄) ∧
    T₄.orthocenter = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∧
    (∀ z, z ∈ T₁.circumsphere ↔ z ∈ Metric.sphere (circ (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄))
      (dist (meet L₂ L₃) (circ (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄)))) ∧
    (∀ z, z ∈ T₂.circumsphere ↔ z ∈ Metric.sphere (circ (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄))
      (dist (meet L₁ L₃) (circ (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄)))) ∧
    (∀ z, z ∈ T₃.circumsphere ↔ z ∈ Metric.sphere (circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄))
      (dist (meet L₁ L₂) (circ (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄)))) ∧
    (∀ z, z ∈ T₄.circumsphere ↔ z ∈ Metric.sphere (circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃))
      (dist (meet L₁ L₂) (circ (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)))) := by
  obtain ⟨t4, t3, t2, t1⟩ := genPos_triangles h
  exact ⟨l14b_orthocenter e₁ t1, l14b_orthocenter e₂ t2, l14b_orthocenter e₃ t3,
    l14b_orthocenter e₄ t4, l14b_mem_circumsphere e₁ t1, l14b_mem_circumsphere e₂ t2,
    l14b_mem_circumsphere e₃ t3, l14b_mem_circumsphere e₄ t4⟩

theorem l14b_miquel {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄)
    {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![meet L₂ L₃, meet L₂ L₄, meet L₃ L₄])
    (e₂ : T₂.points = ![meet L₁ L₃, meet L₁ L₄, meet L₃ L₄])
    (e₃ : T₃.points = ![meet L₁ L₂, meet L₁ L₄, meet L₂ L₄])
    (e₄ : T₄.points = ![meet L₁ L₂, meet L₁ L₃, meet L₂ L₃]) {M : ℂ}
    (hM : M ∈ T₁.circumsphere ∧ M ∈ T₂.circumsphere ∧ M ∈ T₃.circumsphere ∧ M ∈ T₄.circumsphere) :
    M = miquelPt L₁ L₂ L₃ L₄ := by
  obtain ⟨-, -, -, -, s1, -, s3, s4⟩ := l14b_setupT h e₁ e₂ e₃ e₄
  exact miquelPt_unique h ((s4 M).1 hM.2.2.2) ((s3 M).1 hM.2.2.1) ((s1 M).1 hM.1)

theorem l14b_miquel_mem {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄)
    {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![meet L₂ L₃, meet L₂ L₄, meet L₃ L₄])
    (e₂ : T₂.points = ![meet L₁ L₃, meet L₁ L₄, meet L₃ L₄])
    (e₃ : T₃.points = ![meet L₁ L₂, meet L₁ L₄, meet L₂ L₄])
    (e₄ : T₄.points = ![meet L₁ L₂, meet L₁ L₃, meet L₂ L₃]) :
    miquelPt L₁ L₂ L₃ L₄ ∈ T₁.circumsphere ∧ miquelPt L₁ L₂ L₃ L₄ ∈ T₂.circumsphere ∧
      miquelPt L₁ L₂ L₃ L₄ ∈ T₃.circumsphere ∧ miquelPt L₁ L₂ L₃ L₄ ∈ T₄.circumsphere := by
  obtain ⟨-, -, -, -, s1, s2, s3, s4⟩ := l14b_setupT h e₁ e₂ e₃ e₄
  obtain ⟨k1, k2, k3, k4⟩ := miquel h
  exact ⟨(s1 _).2 k1, (s2 _).2 k2, (s3 _).2 k3, (s4 _).2 k4⟩

/-- Orthogonal projection onto a line `line[h₀, h₀ + W]`, characterised by membership and
orthogonality. -/
theorem l14b_proj {s : AffineSubspace ℝ ℂ} [Nonempty s] [s.direction.HasOrthogonalProjection]
    {h₀ W z q : ℂ} (hs : s = line[ℝ, h₀, h₀ + W]) (hW : W ≠ 0) (hq : cr W (q - h₀) = 0)
    (hperp : (conj W * (z - q)).re = 0) :
    (EuclideanGeometry.orthogonalProjection s z : ℂ) = q := by
  rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
  subst hs
  refine ⟨by rw [← SetLike.mem_coe, mem_line_iff hW]; exact hq, ?_⟩
  rw [direction_affineSpan, Submodule.mem_orthogonal]
  intro u hu
  rw [mem_vectorSpan_pair] at hu
  obtain ⟨r, rfl⟩ := hu
  rw [vsub_eq_sub, vsub_eq_sub, Complex.inner, Complex.real_smul,
    show (z - q) * conj ((r : ℂ) * (h₀ - (h₀ + W))) = -(r : ℂ) * (conj W * (z - q)) by
      simp only [map_mul, map_sub, map_add, Complex.conj_ofReal]; ring,
    ← Complex.ofReal_neg, Complex.re_ofReal_mul, hperp, mul_zero]

theorem l14b_reflection {p q : ℂ} (h : p ≠ q) (z : ℂ) :
    EuclideanGeometry.reflection line[ℝ, p, q] z = reflPt z ⟨p, q - p⟩ := by
  have hf := foot_eq_orthogonalProjection z (⟨p, q - p⟩ : Line) (sub_ne_zero.2 h.symm)
  simp only [add_sub_cancel] at hf
  rw [EuclideanGeometry.reflection_apply', ← hf, reflPt, vsub_eq_sub, vadd_eq_add]; ring

theorem l14b_midpoint (x y : ℂ) : midpoint ℝ x y = (x + y) / 2 := by
  rw [midpoint_eq_smul_add ℝ x y, invOf_eq_inv, Complex.real_smul]; push_cast; ring

/-! ### Generic forms (directrix given as any subspace equal to `orthoLine`) -/

theorem l14b_finrank {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    Module.finrank ℝ (orthoLine L₁ L₂ L₃ L₄).direction = 1 := by
  rw [orthoLine_eq h, direction_affineSpan, vectorSpan_pair, finrank_span_singleton]
  rw [vsub_eq_sub, sub_add_cancel_left, neg_ne_zero]
  exact simson_dir_ne h

theorem l14b_tanPt_proj {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) {S : AffineSubspace ℝ ℂ}
    [Nonempty S] [S.direction.HasOrthogonalProjection] (hS : S = orthoLine L₁ L₂ L₃ L₄) (L : Line)
    (hL : L = L₁ ∨ L = L₂ ∨ L = L₃ ∨ L = L₄) :
    (EuclideanGeometry.orthogonalProjection S (tanPt L L₁ L₂ L₃ L₄) : ℂ) =
      reflPt (miquelPt L₁ L₂ L₃ L₄) L := by
  have hR : cr (dirW L₁ L₂ L₃ L₄)
      (reflPt (miquelPt L₁ L₂ L₃ L₄) L - ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)) = 0 := by
    obtain ⟨r1, r2, r3, r4⟩ := reflPt_cr h
    rcases hL with rfl | rfl | rfl | rfl
    · exact r1
    · exact r2
    · exact r3
    · exact r4
  exact l14b_proj (hS.trans (orthoLine_eq h)) (dirW_ne h) hR
    (perpMeet_perp _ (line_not_perp h L hL))

theorem l14b_vertex_eq {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) {S : AffineSubspace ℝ ℂ}
    [Nonempty S] [S.direction.HasOrthogonalProjection] (hS : S = orthoLine L₁ L₂ L₃ L₄) :
    midpoint ℝ (miquelPt L₁ L₂ L₃ L₄)
      (EuclideanGeometry.orthogonalProjection S (miquelPt L₁ L₂ L₃ L₄) : ℂ) = vertex L₁ L₂ L₃ L₄ := by
  rw [l14b_proj (hS.trans (orthoLine_eq h)) (dirW_ne h)
    (foot_mem (miquelPt L₁ L₂ L₃ L₄) (directrix L₁ L₂ L₃ L₄))
    (foot_perp (miquelPt L₁ L₂ L₃ L₄) (directrix L₁ L₂ L₃ L₄) (dirW_ne h)), l14b_midpoint]
  rfl

theorem l14b_vertex {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) {S : AffineSubspace ℝ ℂ}
    [Nonempty S] [S.direction.HasOrthogonalProjection] (hS : S = orthoLine L₁ L₂ L₃ L₄) :
    dist (midpoint ℝ (miquelPt L₁ L₂ L₃ L₄)
      (EuclideanGeometry.orthogonalProjection S (miquelPt L₁ L₂ L₃ L₄) : ℂ)) (miquelPt L₁ L₂ L₃ L₄) =
      Metric.infDist (midpoint ℝ (miquelPt L₁ L₂ L₃ L₄)
        (EuclideanGeometry.orthogonalProjection S (miquelPt L₁ L₂ L₃ L₄) : ℂ)) (S : Set ℂ) ∧
    dist (midpoint ℝ (miquelPt L₁ L₂ L₃ L₄)
      (EuclideanGeometry.orthogonalProjection S (miquelPt L₁ L₂ L₃ L₄) : ℂ)) (miquelPt L₁ L₂ L₃ L₄) =
      Metric.infDist (miquelPt L₁ L₂ L₃ L₄) (S : Set ℂ) / 2 ∧
    ∀ z, dist z (miquelPt L₁ L₂ L₃ L₄) = Metric.infDist z (S : Set ℂ) →
      Metric.infDist (midpoint ℝ (miquelPt L₁ L₂ L₃ L₄)
        (EuclideanGeometry.orthogonalProjection S (miquelPt L₁ L₂ L₃ L₄) : ℂ)) (S : Set ℂ) ≤
        Metric.infDist z (S : Set ℂ) := by
  rw [l14b_vertex_eq h hS]
  subst hS
  exact ⟨vertex_onParabola h, dist_vertex h, fun z hz => vertex_closest h hz⟩

theorem l14b_tangent_iff {p q f : ℂ} (h : p ≠ q) (S : AffineSubspace ℝ ℂ) :
    Tangent ⟨p, q - p⟩ f S ↔
      ∃! z, z ∈ line[ℝ, p, q] ∧ dist z f = Metric.infDist z (S : Set ℂ) := by
  unfold Tangent OnParabola; simp only [l14b_mem h]

/-- A point of the parabola at distance `≤ infDist M S / 2` from `S` is the midpoint of `M` and
its projection: the nearest point of the parabola to the directrix is unique. -/
theorem l14b_nearest_unique (S : AffineSubspace ℝ ℂ) [Nonempty S] [S.direction.HasOrthogonalProjection]
    {M z : ℂ} (hz : dist z M = Metric.infDist z (S : Set ℂ))
    (hle : Metric.infDist z (S : Set ℂ) ≤ Metric.infDist M (S : Set ℂ) / 2) :
    z = midpoint ℝ M (EuclideanGeometry.orthogonalProjection S M : ℂ) := by
  set P : ℂ := ((EuclideanGeometry.orthogonalProjection S M : S) : ℂ)
  set Q : ℂ := ((EuclideanGeometry.orthogonalProjection S z : S) : ℂ)
  have hP : dist M P = Metric.infDist M (S : Set ℂ) :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist S M
  have hQ : dist z Q = Metric.infDist z (S : Set ℂ) :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist S z
  have hmem : Q ∈ S := EuclideanGeometry.orthogonalProjection_mem _
  have h1 : Metric.infDist M (S : Set ℂ) ≤ dist M Q := Metric.infDist_le_dist_of_mem hmem
  have h2 := dist_triangle M z Q
  have hpy := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq M hmem
  rw [dist_comm z M] at hz
  have e1 : dist M Q = dist M P := by linarith
  have hPP : dist Q P = 0 := by
    rw [dist_comm Q M, e1] at hpy
    have : dist Q P * dist Q P = 0 := by linarith
    exact mul_self_eq_zero.1 this
  have ePP : Q = P := dist_eq_zero.1 hPP
  have hw : Wbtw ℝ M z P := by
    rw [← dist_add_dist_eq_iff, ← ePP]; linarith
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
  have hd := dist_lineMap_left (𝕜 := ℝ) M P t
  rw [Real.norm_eq_abs, abs_of_nonneg ht0, dist_comm] at hd
  by_cases h0 : dist M P = 0
  · have eMP : M = P := dist_eq_zero.1 h0
    rw [← eMP, AffineMap.lineMap_same_apply, midpoint_self]
  · have ht : t = 1 / 2 := by
      have : t * dist M P = (1 / 2) * dist M P := by linarith
      exact mul_right_cancel₀ h0 this
    rw [ht, midpoint, one_div, invOf_eq_inv]

theorem l14b_parallel_iff {p q p' q' : ℂ} (h : p ≠ q) (h' : p' ≠ q') :
    line[ℝ, p, q].Parallel line[ℝ, p', q'] ↔ cr (q - p) (q' - p') = 0 := by
  have := parallel_iff_cr (L := ⟨p, q - p⟩) (M := ⟨p', q' - p'⟩) (sub_ne_zero.2 h.symm)
    (sub_ne_zero.2 h'.symm)
  simpa using this

theorem l14b_noconc {p q p' q' p'' q'' a : ℂ} (h : p ≠ q) (h' : p' ≠ q') (h'' : p'' ≠ q'')
    (hc : cr (q - p) (q' - p') ≠ 0) (ha : a ∈ line[ℝ, p, q] ∧ a ∈ line[ℝ, p', q'])
    (hn : cr (q'' - p'') (a - p'') ≠ 0) :
    ¬ ∃ z, z ∈ line[ℝ, p, q] ∧ z ∈ line[ℝ, p', q'] ∧ z ∈ line[ℝ, p'', q''] := by
  rintro ⟨z, hz, hz', hz''⟩
  have e1 := l14b_meet h h' hc ha
  have e2 := l14b_meet h h' hc ⟨hz, hz'⟩
  rw [l14b_mem_iff h'', e2, ← e1] at hz''
  exact hn hz''

/-! ### The Mathlib-only statements -/

section Config

variable {p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℂ}
  (h₁ : p₁ ≠ q₁) (h₂ : p₂ ≠ q₂) (h₃ : p₃ ≠ q₃) (h₄ : p₄ ≠ q₄)
  (n₁₂ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₂, q₂])
  (n₁₃ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₃, q₃])
  (n₁₄ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₄, q₄])
  (n₂₃ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₃, q₃])
  (n₂₄ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₄, q₄])
  (n₃₄ : ¬ line[ℝ, p₃, q₃].Parallel line[ℝ, p₄, q₄])
  (c₁₂₃ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃])
  (c₁₂₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₄, q₄])
  (c₁₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
  (c₂₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
  {a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ : ℂ}
  (m₁₂ : a₁₂ ∈ line[ℝ, p₁, q₁] ∧ a₁₂ ∈ line[ℝ, p₂, q₂])
  (m₁₃ : a₁₃ ∈ line[ℝ, p₁, q₁] ∧ a₁₃ ∈ line[ℝ, p₃, q₃])
  (m₁₄ : a₁₄ ∈ line[ℝ, p₁, q₁] ∧ a₁₄ ∈ line[ℝ, p₄, q₄])
  (m₂₃ : a₂₃ ∈ line[ℝ, p₂, q₂] ∧ a₂₃ ∈ line[ℝ, p₃, q₃])
  (m₂₄ : a₂₄ ∈ line[ℝ, p₂, q₂] ∧ a₂₄ ∈ line[ℝ, p₄, q₄])
  (m₃₄ : a₃₄ ∈ line[ℝ, p₃, q₃] ∧ a₃₄ ∈ line[ℝ, p₄, q₄])
include h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄

/-- The four triangles exist as Mathlib triangles (their vertices are affinely independent). -/
theorem l14_triangles_exist :
    ∃ T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ, T₁.points = ![a₂₃, a₂₄, a₃₄] ∧
      T₂.points = ![a₁₃, a₁₄, a₃₄] ∧ T₃.points = ![a₁₂, a₁₄, a₂₄] ∧
      T₄.points = ![a₁₂, a₁₃, a₂₃] := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨t4, t3, t2, t1⟩ := genPos_triangles hG
  exact ⟨⟨_, affineIndependent_iff_not_collinear_set.2 t1⟩,
    ⟨_, affineIndependent_iff_not_collinear_set.2 t2⟩,
    ⟨_, affineIndependent_iff_not_collinear_set.2 t3⟩,
    ⟨_, affineIndependent_iff_not_collinear_set.2 t4⟩, rfl, rfl, rfl, rfl⟩

/-- **F3 (Newton–Gauss ⟂ directrix)**, Mathlib form: every vector of the affine span of the four
orthocentres is orthogonal to `N₂ − N₁` and `N₃ − N₁` (`Nᵢ` the diagonal midpoints). -/
theorem l14_newton_perp_orthoLine {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![a₂₃, a₂₄, a₃₄]) (e₂ : T₂.points = ![a₁₃, a₁₄, a₃₄])
    (e₃ : T₃.points = ![a₁₂, a₁₄, a₂₄]) (e₄ : T₄.points = ![a₁₂, a₁₃, a₂₃]) :
    ∀ x ∈ affineSpan ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ),
    ∀ y ∈ affineSpan ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ),
      inner ℝ (x - y) (midpoint ℝ a₁₃ a₂₄ - midpoint ℝ a₁₂ a₃₄) = 0 ∧
      inner ℝ (x - y) (midpoint ℝ a₁₄ a₂₃ - midpoint ℝ a₁₂ a₃₄) = 0 := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄, -⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  rw [o₁, o₂, o₃, o₄]
  simp only [l14b_midpoint]
  intro x hx y hy
  exact newton_perp_orthoLine hG hx hy

/-- The directrix (the affine span of the four orthocentres) is a line. -/
theorem l14_directrix_finrank {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![a₂₃, a₂₄, a₃₄]) (e₂ : T₂.points = ![a₁₃, a₁₄, a₃₄])
    (e₃ : T₃.points = ![a₁₂, a₁₄, a₂₄]) (e₄ : T₄.points = ![a₁₂, a₁₃, a₂₃]) :
    Module.finrank ℝ (affineSpan ℝ
      ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)).direction = 1 := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄, -⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  rw [o₁, o₂, o₃, o₄]
  exact l14b_finrank hG

/-- **Miquel point** (Mathlib form): exactly one point lies on the four circumspheres. -/
theorem l14_miquel_existsUnique {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![a₂₃, a₂₄, a₃₄]) (e₂ : T₂.points = ![a₁₃, a₁₄, a₃₄])
    (e₃ : T₃.points = ![a₁₂, a₁₄, a₂₄]) (e₄ : T₄.points = ![a₁₂, a₁₃, a₂₃]) :
    ∃! M : ℂ, M ∈ T₁.circumsphere ∧ M ∈ T₂.circumsphere ∧ M ∈ T₃.circumsphere ∧
      M ∈ T₄.circumsphere := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  exact ⟨_, l14b_miquel_mem hG e₁ e₂ e₃ e₄, fun M hM => l14b_miquel hG e₁ e₂ e₃ e₄ hM⟩

/-- **P3 (Lambert)**, Mathlib form: some point `M` on the four circumspheres is the focus of a
parabola with directrix the span of the orthocentres, tangent to the four lines. -/
theorem l14_lambert {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![a₂₃, a₂₄, a₃₄]) (e₂ : T₂.points = ![a₁₃, a₁₄, a₃₄])
    (e₃ : T₃.points = ![a₁₂, a₁₄, a₂₄]) (e₄ : T₄.points = ![a₁₂, a₁₃, a₂₃]) :
    ∃ M : ℂ, (M ∈ T₁.circumsphere ∧ M ∈ T₂.circumsphere ∧ M ∈ T₃.circumsphere ∧
      M ∈ T₄.circumsphere) ∧
      ∀ L : AffineSubspace ℝ ℂ, L = line[ℝ, p₁, q₁] ∨ L = line[ℝ, p₂, q₂] ∨ L = line[ℝ, p₃, q₃] ∨
        L = line[ℝ, p₄, q₄] →
        ∃! z, z ∈ L ∧ dist z M = Metric.infDist z (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄, -⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  refine ⟨_, l14b_miquel_mem hG e₁ e₂ e₃ e₄, ?_⟩
  rw [o₁, o₂, o₃, o₄]
  rintro L (rfl | rfl | rfl | rfl)
  · exact (l14b_tangent_iff h₁ _).1 (parabola_tangent₁ hG)
  · exact (l14b_tangent_iff h₂ _).1 (parabola_tangent₂ hG)
  · exact (l14b_tangent_iff h₃ _).1 (parabola_tangent₃ hG)
  · exact (l14b_tangent_iff h₄ _).1 (parabola_tangent₄ hG)

variable {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
  (e₁ : T₁.points = ![a₂₃, a₂₄, a₃₄]) (e₂ : T₂.points = ![a₁₃, a₁₄, a₃₄])
  (e₃ : T₃.points = ![a₁₂, a₁₄, a₂₄]) (e₄ : T₄.points = ![a₁₂, a₁₃, a₂₃]) {M : ℂ}
  (hM : M ∈ T₁.circumsphere ∧ M ∈ T₂.circumsphere ∧ M ∈ T₃.circumsphere ∧ M ∈ T₄.circumsphere)
include e₁ e₂ e₃ e₄ hM

/-- **F1 (Steiner line)**, Mathlib form: the reflections of the Miquel point in the four lines are
collinear. -/
theorem l14_reflections_collinear :
    Collinear ℝ ({EuclideanGeometry.reflection line[ℝ, p₁, q₁] M,
      EuclideanGeometry.reflection line[ℝ, p₂, q₂] M, EuclideanGeometry.reflection line[ℝ, p₃, q₃] M,
      EuclideanGeometry.reflection line[ℝ, p₄, q₄] M} : Set ℂ) := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain rfl := l14b_miquel hG e₁ e₂ e₃ e₄ hM
  rw [l14b_reflection h₁, l14b_reflection h₂, l14b_reflection h₃, l14b_reflection h₄]
  exact reflections_collinear hG

/-- **F1**, Mathlib form: the four reflections lie on the affine span of the four orthocentres. -/
theorem l14_reflPt_mem_orthoLine :
    EuclideanGeometry.reflection line[ℝ, p₁, q₁] M ∈ affineSpan ℝ
      ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, p₂, q₂] M ∈ affineSpan ℝ
      ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, p₃, q₃] M ∈ affineSpan ℝ
      ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, p₄, q₄] M ∈ affineSpan ℝ
      ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄, -⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  obtain rfl := l14b_miquel hG e₁ e₂ e₃ e₄ hM
  rw [o₁, o₂, o₃, o₄, l14b_reflection h₁, l14b_reflection h₂, l14b_reflection h₃,
    l14b_reflection h₄]
  exact reflPt_mem_orthoLine hG

/-- **F2**, Mathlib form: the Miquel point is not on the affine span of the orthocentres. -/
theorem l14_miquel_not_mem_orthoLine :
    M ∉ affineSpan ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄, -⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  obtain rfl := l14b_miquel hG e₁ e₂ e₃ e₄ hM
  rw [o₁, o₂, o₃, o₄]
  exact miquel_not_mem_orthoLine hG

/-- **F3**, Mathlib form: each of the four lines meets the parabola with focus `M` and directrix
the span of the orthocentres in exactly one point. -/
theorem l14_parabola_tangent :
    ∀ L : AffineSubspace ℝ ℂ, L = line[ℝ, p₁, q₁] ∨ L = line[ℝ, p₂, q₂] ∨ L = line[ℝ, p₃, q₃] ∨
      L = line[ℝ, p₄, q₄] →
      ∃! z, z ∈ L ∧ dist z M = Metric.infDist z (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄, -⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  obtain rfl := l14b_miquel hG e₁ e₂ e₃ e₄ hM
  rw [o₁, o₂, o₃, o₄]
  rintro L (rfl | rfl | rfl | rfl)
  · exact (l14b_tangent_iff h₁ _).1 (parabola_tangent₁ hG)
  · exact (l14b_tangent_iff h₂ _).1 (parabola_tangent₂ hG)
  · exact (l14b_tangent_iff h₃ _).1 (parabola_tangent₃ hG)
  · exact (l14b_tangent_iff h₄ _).1 (parabola_tangent₄ hG)

theorem l14_parabola_tangent₁ :
    ∃! z, z ∈ line[ℝ, p₁, q₁] ∧ dist z M = Metric.infDist z (affineSpan ℝ
      ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) :=
  l14_parabola_tangent h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄
    m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄ e₁ e₂ e₃ e₄ hM _ (Or.inl rfl)

theorem l14_parabola_tangent₂ :
    ∃! z, z ∈ line[ℝ, p₂, q₂] ∧ dist z M = Metric.infDist z (affineSpan ℝ
      ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) :=
  l14_parabola_tangent h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄
    m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄ e₁ e₂ e₃ e₄ hM _ (Or.inr (Or.inl rfl))

theorem l14_parabola_tangent₃ :
    ∃! z, z ∈ line[ℝ, p₃, q₃] ∧ dist z M = Metric.infDist z (affineSpan ℝ
      ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) :=
  l14_parabola_tangent h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄
    m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄ e₁ e₂ e₃ e₄ hM _ (Or.inr (Or.inr (Or.inl rfl)))

theorem l14_parabola_tangent₄ :
    ∃! z, z ∈ line[ℝ, p₄, q₄] ∧ dist z M = Metric.infDist z (affineSpan ℝ
      ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) :=
  l14_parabola_tangent h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄
    m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄ e₁ e₂ e₃ e₄ hM _ (Or.inr (Or.inr (Or.inr rfl)))

/-- **P1 (all four lines)**, Mathlib form: on each line `L` there is a point `z` of the parabola,
the only one, and its orthogonal projection on the directrix is the reflection of `M` in `L`. -/
theorem l14_tanPt_all :
    ∀ pq ∈ ({(p₁, q₁), (p₂, q₂), (p₃, q₃), (p₄, q₄)} : Set (ℂ × ℂ)),
      ∃ z, z ∈ line[ℝ, pq.1, pq.2] ∧
        dist z M = Metric.infDist z (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) ∧
        (∀ w, w ∈ line[ℝ, pq.1, pq.2] → dist w M = Metric.infDist w (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) →
            w = z) ∧
        (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) z : ℂ) =
          EuclideanGeometry.reflection line[ℝ, pq.1, pq.2] M := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄, -⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  obtain rfl := l14b_miquel hG e₁ e₂ e₃ e₄ hM
  have hS : affineSpan ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} :
      Set ℂ) = orthoLine ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ := by
    rw [o₁, o₂, o₃, o₄]; rfl
  have key : ∀ {p q : ℂ} (hpq : p ≠ q), (⟨p, q - p⟩ : Line) ∈
      ({⟨p₁, q₁ - p₁⟩, ⟨p₂, q₂ - p₂⟩, ⟨p₃, q₃ - p₃⟩, ⟨p₄, q₄ - p₄⟩} : Set Line) →
      ∃ z, z ∈ line[ℝ, p, q] ∧ dist z (miquelPt ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩
          ⟨p₄, q₄ - p₄⟩) = Metric.infDist z (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) ∧
        (∀ w, w ∈ line[ℝ, p, q] → dist w (miquelPt ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩
          ⟨p₄, q₄ - p₄⟩) = Metric.infDist w (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) →
            w = z) ∧
        (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) z : ℂ) =
          EuclideanGeometry.reflection line[ℝ, p, q] (miquelPt ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩
            ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩) := by
    intro p q hpq hL
    obtain ⟨t1, t2, t3⟩ := tanPt_all hG _ hL
    have hL' : (⟨p, q - p⟩ : Line) = ⟨p₁, q₁ - p₁⟩ ∨ (⟨p, q - p⟩ : Line) = ⟨p₂, q₂ - p₂⟩ ∨
        (⟨p, q - p⟩ : Line) = ⟨p₃, q₃ - p₃⟩ ∨ (⟨p, q - p⟩ : Line) = ⟨p₄, q₄ - p₄⟩ := by
      simpa using hL
    unfold OnParabola at t2 t3
    rw [← hS] at t2 t3
    refine ⟨_, (l14b_mem hpq).1 t1, t2, fun w hw hw' => t3 w ((l14b_mem hpq).2 hw) hw', ?_⟩
    rw [l14b_tanPt_proj hG hS _ hL', l14b_reflection hpq]
  rintro ⟨p, q⟩ hpq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hpq
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key h₁ (by simp)
  · exact key h₂ (by simp)
  · exact key h₃ (by simp)
  · exact key h₄ (by simp)

/-- **P2 (vertex)**, Mathlib form: the midpoint `V` of `M` and its orthogonal projection on the
directrix `S` is on the parabola, `dist V M = infDist M S / 2`, and `V` is a point of the parabola
nearest to `S`. -/
theorem l14_vertex :
    dist (midpoint ℝ M (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) M : ℂ)) M =
      Metric.infDist (midpoint ℝ M (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) M : ℂ))
        (affineSpan ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) :
          Set ℂ) ∧
    dist (midpoint ℝ M (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) M : ℂ)) M =
      Metric.infDist M (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) / 2 ∧
    ∀ z, dist z M = Metric.infDist z (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) →
      Metric.infDist (midpoint ℝ M (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) M : ℂ))
        (affineSpan ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) :
          Set ℂ) ≤
      Metric.infDist z (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄, -⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  obtain rfl := l14b_miquel hG e₁ e₂ e₃ e₄ hM
  exact l14b_vertex hG (by rw [o₁, o₂, o₃, o₄]; rfl)

theorem l14_vertex_onParabola :
    dist (midpoint ℝ M (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) M : ℂ)) M =
      Metric.infDist (midpoint ℝ M (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) M : ℂ))
        (affineSpan ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) :
          Set ℂ) :=
  (l14_vertex h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄
    m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄ e₁ e₂ e₃ e₄ hM).1

theorem l14_dist_vertex :
    dist (midpoint ℝ M (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) M : ℂ)) M =
      Metric.infDist M (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) / 2 :=
  (l14_vertex h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄
    m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄ e₁ e₂ e₃ e₄ hM).2.1

/-- **P2 (vertex as a property)**: there is exactly one point of the parabola nearest to the
directrix — a point `V` of the parabola with `infDist V S ≤ infDist z S` for all `z` on it. -/
theorem l14_vertex_closest :
    ∃! V : ℂ, dist V M = Metric.infDist V (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) ∧
      ∀ z, dist z M = Metric.infDist z (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) →
        Metric.infDist V (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) ≤
        Metric.infDist z (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) := by
  obtain ⟨v1, v2, v3⟩ := l14_vertex h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄
    m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄ e₁ e₂ e₃ e₄ hM
  refine ⟨_, ⟨v1, v3⟩, fun z ⟨hz, hle⟩ => l14b_nearest_unique _ hz ?_⟩
  have := hle _ v1
  rw [← v1, v2] at this
  exact this

/-- **Bridge (transfer).** In the Mathlib configuration, every Mathlib object equals the library's
local one. Used for the witnesses. -/
theorem l14b_transfer :
    GenPos ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ ∧
    a₁₂ = meet ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ∧ a₁₃ = meet ⟨p₁, q₁ - p₁⟩ ⟨p₃, q₃ - p₃⟩ ∧
    a₁₄ = meet ⟨p₁, q₁ - p₁⟩ ⟨p₄, q₄ - p₄⟩ ∧ a₂₃ = meet ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ∧
    a₂₄ = meet ⟨p₂, q₂ - p₂⟩ ⟨p₄, q₄ - p₄⟩ ∧ a₃₄ = meet ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ ∧
    M = miquelPt ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ ∧
    T₁.orthocenter = ortho a₂₃ a₂₄ a₃₄ ∧ T₂.orthocenter = ortho a₁₃ a₁₄ a₃₄ ∧
    T₃.orthocenter = ortho a₁₂ a₁₄ a₂₄ ∧ T₄.orthocenter = ortho a₁₂ a₁₃ a₂₃ ∧
    affineSpan ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) =
      orthoLine ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ ∧
    EuclideanGeometry.reflection line[ℝ, p₁, q₁] M = reflPt M ⟨p₁, q₁ - p₁⟩ ∧
    EuclideanGeometry.reflection line[ℝ, p₂, q₂] M = reflPt M ⟨p₂, q₂ - p₂⟩ ∧
    EuclideanGeometry.reflection line[ℝ, p₃, q₃] M = reflPt M ⟨p₃, q₃ - p₃⟩ ∧
    EuclideanGeometry.reflection line[ℝ, p₄, q₄] M = reflPt M ⟨p₄, q₄ - p₄⟩ ∧
    (∀ pq ∈ ({(p₁, q₁), (p₂, q₂), (p₃, q₃), (p₄, q₄)} : Set (ℂ × ℂ)),
      tanPt ⟨pq.1, pq.2 - pq.1⟩ ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ ∈
        line[ℝ, pq.1, pq.2] ∧
      dist (tanPt ⟨pq.1, pq.2 - pq.1⟩ ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩) M =
        Metric.infDist (tanPt ⟨pq.1, pq.2 - pq.1⟩ ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩
          ⟨p₄, q₄ - p₄⟩) (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ)) ∧
    midpoint ℝ M (EuclideanGeometry.orthogonalProjection (affineSpan ℝ
        ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ)) M : ℂ) =
      vertex ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ := by
  obtain ⟨hG, E₁₂, E₁₃, E₁₄, E₂₃, E₂₄, E₃₄⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  subst E₁₂ E₁₃ E₁₄ E₂₃ E₂₄ E₃₄
  obtain ⟨o₁, o₂, o₃, o₄, -⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  obtain rfl := l14b_miquel hG e₁ e₂ e₃ e₄ hM
  have hS : affineSpan ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} :
      Set ℂ) = orthoLine ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ := by
    rw [o₁, o₂, o₃, o₄]; rfl
  refine ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl, rfl, o₁, o₂, o₃, o₄, hS, l14b_reflection h₁ _,
    l14b_reflection h₂ _, l14b_reflection h₃ _, l14b_reflection h₄ _, ?_, l14b_vertex_eq hG hS⟩
  have key : ∀ {p q : ℂ} (hpq : p ≠ q), (⟨p, q - p⟩ : Line) ∈
      ({⟨p₁, q₁ - p₁⟩, ⟨p₂, q₂ - p₂⟩, ⟨p₃, q₃ - p₃⟩, ⟨p₄, q₄ - p₄⟩} : Set Line) →
      tanPt ⟨p, q - p⟩ ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ ∈ line[ℝ, p, q] ∧
      dist (tanPt ⟨p, q - p⟩ ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩)
        (miquelPt ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩) =
        Metric.infDist (tanPt ⟨p, q - p⟩ ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩
          ⟨p₄, q₄ - p₄⟩) (affineSpan ℝ
          ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) : Set ℂ) := by
    intro p q hpq hL
    obtain ⟨t1, t2, -⟩ := tanPt_all hG _ hL
    unfold OnParabola at t2
    rw [← hS] at t2
    exact ⟨(l14b_mem hpq).1 t1, t2⟩
  rintro ⟨p, q⟩ hpq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hpq
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key h₁ (by simp)
  · exact key h₂ (by simp)
  · exact key h₃ (by simp)
  · exact key h₄ (by simp)

end Config

/-! ### Witnesses (non-vacuity) -/

theorem l14wbA_base :
    (0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) := by
  have h1 : (0 : ℂ) ≠ 1 := by norm_num [Complex.ext_iff]
  have h2 : (1 - I : ℂ) ≠ -2 + 2 * I := by norm_num [Complex.ext_iff]
  have h3 : (-1 + 3 * I : ℂ) ≠ -2 := by norm_num [Complex.ext_iff]
  have h4 : (-1 - 2 * I : ℂ) ≠ 3 := by norm_num [Complex.ext_iff]
  have m12 : (0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h2]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m13 : (-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m14 : (3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m23 : (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] := by
    rw [l14b_mem_iff h2, l14b_mem_iff h3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m24 : (1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3] := by
    rw [l14b_mem_iff h2, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m34 : (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3] := by
    rw [l14b_mem_iff h3, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨h1, h2, h3, h4, (by rw [l14b_parallel_iff h1 h2]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h1 h3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h1 h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h2 h3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h2 h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h3 h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (l14b_noconc h1 h2 h3 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m12 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])), (l14b_noconc h1 h2 h4 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m12 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])), (l14b_noconc h1 h3 h4 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m13 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])), (l14b_noconc h2 h3 h4 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m23 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])), m12, m13, m14, m23, m24, m34⟩

theorem l14wbA_vals :
    GenPos (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) ∧
    meet (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) = 0 ∧
    meet (⟨0, 1 - (0)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) = -2 ∧
    meet (⟨0, 1 - (0)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = 3 ∧
    meet (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) = -3/2 + 3/2 * I ∧
    meet (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = 1 - I ∧
    meet (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = -3 - 3 * I ∧
    miquelPt (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = (I : ℂ) ∧
    ortho (-3/2 + 3/2 * I) (1 - I) (-3 - 3 * I) = -1/2 - 1/2 * I ∧
    ortho (-2) (3) (-3 - 3 * I) = -3 + 2 * I ∧
    ortho (0) (3) (1 - I) = 1 - 2 * I ∧
    ortho (0) (-2) (-3/2 + 3/2 * I) = -3/2 + 1/2 * I ∧
    foot ((I : ℂ)) (⟨0, 1 - (0)⟩ : Line) = 0 ∧
    foot ((I : ℂ)) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) = -1/2 + 1/2 * I ∧
    reflPt ((I : ℂ)) (⟨0, 1 - (0)⟩ : Line) = -I ∧
    reflPt ((I : ℂ)) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) = -1 ∧
    reflPt ((I : ℂ)) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) = -3 + 2 * I ∧
    reflPt ((I : ℂ)) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = 2 - 3 * I ∧
    tanPt (⟨0, 1 - (0)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = 1 ∧
    tanPt (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = -1/2 + 1/2 * I ∧
    tanPt (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = -1/2 + 9/2 * I ∧
    tanPt (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = 7 + 2 * I ∧
    vertex (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = -1/2 + 1/2 * I := by
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := l14wbA_base
  obtain ⟨hG, e12, e13, e14, e23, e24, e34⟩ := l14b_setup h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34
  have hM : miquelPt (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = (I : ℂ) := by
    rw [miquelPt, ← e12, ← e13, ← e14, ← e23, ← e24]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hf1 : foot ((I : ℂ)) (⟨0, 1 - (0)⟩ : Line) = 0 := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hf2 : foot ((I : ℂ)) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) = -1/2 + 1/2 * I := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hr1 : reflPt ((I : ℂ)) (⟨0, 1 - (0)⟩ : Line) = -I := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hr2 : reflPt ((I : ℂ)) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) = -1 := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hr3 : reflPt ((I : ℂ)) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) = -3 + 2 * I := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hr4 : reflPt ((I : ℂ)) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = 2 - 3 * I := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have ht1 : tanPt (⟨0, 1 - (0)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = 1 := by
    rw [tanPt, perpMeet, dirW, hM, hf1, hf2, hr1]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have ht2 : tanPt (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = -1/2 + 1/2 * I := by
    rw [tanPt, perpMeet, dirW, hM, hf1, hf2, hr2]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have ht3 : tanPt (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = -1/2 + 9/2 * I := by
    rw [tanPt, perpMeet, dirW, hM, hf1, hf2, hr3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have ht4 : tanPt (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) = 7 + 2 * I := by
    rw [tanPt, perpMeet, dirW, hM, hf1, hf2, hr4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨hG, e12.symm, e13.symm, e14.symm, e23.symm, e24.symm, e34.symm, hM, (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), hf1, hf2, hr1, hr2, hr3, hr4, ht1, ht2, ht3, ht4, by rw [vertex, directrix, dirW, hM, hf1, hf2, ← e12, ← e13, ← e23]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]⟩

theorem l14wbA_master :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧ ((I : ℂ) ∈ T1.circumsphere ∧ (I : ℂ) ∈ T2.circumsphere ∧ (I : ℂ) ∈ T3.circumsphere ∧ (I : ℂ) ∈ T4.circumsphere) ∧
    T1.orthocenter = -1/2 - 1/2 * I ∧
    T2.orthocenter = -3 + 2 * I ∧
    T3.orthocenter = 1 - 2 * I ∧
    T4.orthocenter = -3/2 + 1/2 * I ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) = -I ∧
    EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) = -1 ∧
    EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) = -3 + 2 * I ∧
    EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) = 2 - 3 * I ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ dist (1 : ℂ) (I : ℂ) = Metric.infDist (1 : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    ((-1/2 + 1/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ dist (-1/2 + 1/2 * I : ℂ) (I : ℂ) = Metric.infDist (-1/2 + 1/2 * I : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    ((-1/2 + 9/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ dist (-1/2 + 9/2 * I : ℂ) (I : ℂ) = Metric.infDist (-1/2 + 9/2 * I : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    ((7 + 2 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3] ∧ dist (7 + 2 * I : ℂ) (I : ℂ) = Metric.infDist (7 + 2 * I : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (1 : ℂ) : ℂ) = -I ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (-1/2 + 1/2 * I : ℂ) : ℂ) = -1 ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (-1/2 + 9/2 * I : ℂ) : ℂ) = -3 + 2 * I ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (7 + 2 * I : ℂ) : ℂ) = 2 - 3 * I ∧
    midpoint ℝ ((I : ℂ) : ℂ) (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) ((I : ℂ) : ℂ) : ℂ) = -1/2 + 1/2 * I ∧
    Module.finrank ℝ (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)).direction = 1 := by
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := l14wbA_base
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, ?_⟩
  obtain ⟨hG, -⟩ := l14b_setup h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34
  obtain ⟨T1, T2, T3, T4, e1, e2, e3, e4⟩ := l14_triangles_exist h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34
  obtain ⟨-, v12, v13, v14, v23, v24, v34, vM, o1, o2, o3, o4, -, -, r1, r2, r3, r4, t1, t2, t3, t4, vV⟩ := l14wbA_vals
  have e1' : T1.points = ![meet (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line), meet (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line), meet (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line)] := by
    rw [e1, v23, v24, v34]
  have e2' : T2.points = ![meet (⟨0, 1 - (0)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line), meet (⟨0, 1 - (0)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line), meet (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line)] := by
    rw [e2, v13, v14, v34]
  have e3' : T3.points = ![meet (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line), meet (⟨0, 1 - (0)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line), meet (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line)] := by
    rw [e3, v12, v14, v24]
  have e4' : T4.points = ![meet (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line), meet (⟨0, 1 - (0)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line), meet (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line)] := by
    rw [e4, v12, v13, v23]
  have hMc := l14b_miquel_mem hG e1' e2' e3' e4'
  rw [vM] at hMc
  obtain ⟨-, -, -, -, -, -, -, -, O1, O2, O3, O4, -, R1, R2, R3, R4, TP, VX⟩ := l14b_transfer h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34 e1 e2 e3 e4 hMc
  have TA := l14_tanPt_all h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34 e1 e2 e3 e4 hMc
  have tp : ∀ {p q : ℂ}, (p, q) ∈ ({(0, 1), (1 - I, -2 + 2 * I), (-1 + 3 * I, -2), (-1 - 2 * I, 3)} : Set (ℂ × ℂ)) →
      tanPt ⟨p, q - p⟩ (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line) ∈ line[ℝ, p, q] ∧ dist (tanPt ⟨p, q - p⟩ (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line)) (I : ℂ) = Metric.infDist (tanPt ⟨p, q - p⟩ (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line)) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ) ∧
      (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (tanPt ⟨p, q - p⟩ (⟨0, 1 - (0)⟩ : Line) (⟨1 - I, -2 + 2 * I - (1 - I)⟩ : Line) (⟨-1 + 3 * I, -2 - (-1 + 3 * I)⟩ : Line) (⟨-1 - 2 * I, 3 - (-1 - 2 * I)⟩ : Line)) : ℂ) = EuclideanGeometry.reflection line[ℝ, p, q] (I : ℂ) := by
    intro p q hpq
    obtain ⟨m, d⟩ := TP _ hpq
    obtain ⟨z, -, -, hu, hz⟩ := TA _ hpq
    have := hu _ m d
    exact ⟨m, d, by rw [this]; exact hz⟩
  obtain ⟨tm1, td1, tq1⟩ := tp (p := 0) (q := 1) (by simp)
  rw [t1] at tm1 td1 tq1
  obtain ⟨tm2, td2, tq2⟩ := tp (p := 1 - I) (q := -2 + 2 * I) (by simp)
  rw [t2] at tm2 td2 tq2
  obtain ⟨tm3, td3, tq3⟩ := tp (p := -1 + 3 * I) (q := -2) (by simp)
  rw [t3] at tm3 td3 tq3
  obtain ⟨tm4, td4, tq4⟩ := tp (p := -1 - 2 * I) (q := 3) (by simp)
  rw [t4] at tm4 td4 tq4
  rw [vV] at VX
  refine ⟨T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, hMc, by rw [O1, o1], by rw [O2, o2], by rw [O3, o3], by rw [O4, o4], by rw [R1, r1], by rw [R2, r2], by rw [R3, r3], by rw [R4, r4], ⟨tm1, td1⟩, ⟨tm2, td2⟩, ⟨tm3, td3⟩, ⟨tm4, td4⟩, by rw [tq1, R1, r1], by rw [tq2, R2, r2], by rw [tq3, R3, r3], by rw [tq4, R4, r4], VX, l14_directrix_finrank h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34 e1 e2 e3 e4⟩

/-- Witness for `l14_reflections_collinear`: hypotheses hold; the four reflections are pairwise distinct. -/
theorem l14w_reflections_collinear :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧ ((I : ℂ) ∈ T1.circumsphere ∧ (I : ℂ) ∈ T2.circumsphere ∧ (I : ℂ) ∈ T3.circumsphere ∧ (I : ℂ) ∈ T4.circumsphere) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) := by
  obtain ⟨B, T1, T2, T3, T4, E, C, o1, o2, o3, o4, r1, r2, r3, r4, t1, t2, t3, t4, q1, q2, q3, q4, vx, fr⟩ := l14wbA_master
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := B
  obtain ⟨e1, e2, e3, e4⟩ := E
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, C, ?_⟩
  rw [r1, r2, r3, r4]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_reflPt_mem_orthoLine`: the span of the orthocentres is a genuine line (two distinct orthocentres, `finrank = 1`) and the four reflections are pairwise distinct. -/
theorem l14w_reflPt_mem_orthoLine :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧ ((I : ℂ) ∈ T1.circumsphere ∧ (I : ℂ) ∈ T2.circumsphere ∧ (I : ℂ) ∈ T3.circumsphere ∧ (I : ℂ) ∈ T4.circumsphere) ∧
    Module.finrank ℝ (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)).direction = 1 ∧
    T1.orthocenter ≠ T2.orthocenter ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) := by
  obtain ⟨B, T1, T2, T3, T4, E, C, o1, o2, o3, o4, r1, r2, r3, r4, t1, t2, t3, t4, q1, q2, q3, q4, vx, fr⟩ := l14wbA_master
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := B
  obtain ⟨e1, e2, e3, e4⟩ := E
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, C, ?_⟩
  refine ⟨fr, ?_⟩
  rw [o1, o2, r1, r2, r3, r4]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_miquel_not_mem_orthoLine`: the directrix is a line and the focus is at positive distance from it. -/
theorem l14w_miquel_not_mem_orthoLine :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧ ((I : ℂ) ∈ T1.circumsphere ∧ (I : ℂ) ∈ T2.circumsphere ∧ (I : ℂ) ∈ T3.circumsphere ∧ (I : ℂ) ∈ T4.circumsphere) ∧
    Module.finrank ℝ (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)).direction = 1 ∧
    ((I : ℂ) : ℂ) ∉ (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) ∧
    0 < Metric.infDist ((I : ℂ) : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ) := by
  obtain ⟨B, T1, T2, T3, T4, E, C, o1, o2, o3, o4, r1, r2, r3, r4, t1, t2, t3, t4, q1, q2, q3, q4, vx, fr⟩ := l14wbA_master
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := B
  obtain ⟨e1, e2, e3, e4⟩ := E
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, C, ?_⟩
  have hn := l14_miquel_not_mem_orthoLine h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34 e1 e2 e3 e4 C
  refine ⟨fr, hn, ?_⟩
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist]
  refine dist_pos.2 fun h => hn ?_
  rw [h]; exact EuclideanGeometry.orthogonalProjection_mem _

/-- Witness for `l14_parabola_tangent` (and `₁`–`₄`): each line has an explicit point of the parabola (the tangency point), the four points are pairwise distinct, and the focus is not on the directrix (a genuine parabola). -/
theorem l14w_parabola_tangent :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧ ((I : ℂ) ∈ T1.circumsphere ∧ (I : ℂ) ∈ T2.circumsphere ∧ (I : ℂ) ∈ T3.circumsphere ∧ (I : ℂ) ∈ T4.circumsphere) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ dist (1 : ℂ) (I : ℂ) = Metric.infDist (1 : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    ((-1/2 + 1/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ dist (-1/2 + 1/2 * I : ℂ) (I : ℂ) = Metric.infDist (-1/2 + 1/2 * I : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    ((-1/2 + 9/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ dist (-1/2 + 9/2 * I : ℂ) (I : ℂ) = Metric.infDist (-1/2 + 9/2 * I : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    ((7 + 2 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3] ∧ dist (7 + 2 * I : ℂ) (I : ℂ) = Metric.infDist (7 + 2 * I : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    (1 : ℂ) ≠ (-1/2 + 1/2 * I : ℂ) ∧
    (1 : ℂ) ≠ (-1/2 + 9/2 * I : ℂ) ∧
    (1 : ℂ) ≠ (7 + 2 * I : ℂ) ∧
    (-1/2 + 1/2 * I : ℂ) ≠ (-1/2 + 9/2 * I : ℂ) ∧
    (-1/2 + 1/2 * I : ℂ) ≠ (7 + 2 * I : ℂ) ∧
    (-1/2 + 9/2 * I : ℂ) ≠ (7 + 2 * I : ℂ) ∧
    ((I : ℂ) : ℂ) ∉ (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) := by
  obtain ⟨B, T1, T2, T3, T4, E, C, o1, o2, o3, o4, r1, r2, r3, r4, t1, t2, t3, t4, q1, q2, q3, q4, vx, fr⟩ := l14wbA_master
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := B
  obtain ⟨e1, e2, e3, e4⟩ := E
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, C, ?_⟩
  refine ⟨t1, t2, t3, t4, ?_⟩
  refine ⟨by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], l14_miquel_not_mem_orthoLine h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34 e1 e2 e3 e4 C⟩

/-- Witness for `l14_tanPt_all`: the explicit tangency points project to the reflections, and both quadruples are pairwise distinct. -/
theorem l14w_tanPt_all :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧ ((I : ℂ) ∈ T1.circumsphere ∧ (I : ℂ) ∈ T2.circumsphere ∧ (I : ℂ) ∈ T3.circumsphere ∧ (I : ℂ) ∈ T4.circumsphere) ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (1 : ℂ) : ℂ) = EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (-1/2 + 1/2 * I : ℂ) : ℂ) = EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (-1/2 + 9/2 * I : ℂ) : ℂ) = EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (7 + 2 * I : ℂ) : ℂ) = EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) ∧
    (1 : ℂ) ≠ (-1/2 + 1/2 * I : ℂ) ∧
    (1 : ℂ) ≠ (-1/2 + 9/2 * I : ℂ) ∧
    (1 : ℂ) ≠ (7 + 2 * I : ℂ) ∧
    (-1/2 + 1/2 * I : ℂ) ≠ (-1/2 + 9/2 * I : ℂ) ∧
    (-1/2 + 1/2 * I : ℂ) ≠ (7 + 2 * I : ℂ) ∧
    (-1/2 + 9/2 * I : ℂ) ≠ (7 + 2 * I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (1 - I : ℂ), -2 + 2 * I] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (-1 + 3 * I : ℂ), -2] (I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-1 - 2 * I : ℂ), 3] (I : ℂ) := by
  obtain ⟨B, T1, T2, T3, T4, E, C, o1, o2, o3, o4, r1, r2, r3, r4, t1, t2, t3, t4, q1, q2, q3, q4, vx, fr⟩ := l14wbA_master
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := B
  obtain ⟨e1, e2, e3, e4⟩ := E
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, C, ?_⟩
  refine ⟨by rw [q1, r1], by rw [q2, r2], by rw [q3, r3], by rw [q4, r4], ?_⟩
  rw [r1, r2, r3, r4]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_vertex_onParabola`, `l14_dist_vertex`, `l14_vertex_closest`: the vertex is explicit, distinct from the focus and from the focus's projection, and `infDist M S > 0`. -/
theorem l14w_vertex :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧ ((I : ℂ) ∈ T1.circumsphere ∧ (I : ℂ) ∈ T2.circumsphere ∧ (I : ℂ) ∈ T3.circumsphere ∧ (I : ℂ) ∈ T4.circumsphere) ∧
    midpoint ℝ ((I : ℂ) : ℂ) (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) ((I : ℂ) : ℂ) : ℂ) = -1/2 + 1/2 * I ∧
    midpoint ℝ ((I : ℂ) : ℂ) (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) ((I : ℂ) : ℂ) : ℂ) ≠ (I : ℂ) ∧
    midpoint ℝ ((I : ℂ) : ℂ) (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) ((I : ℂ) : ℂ) : ℂ) ≠ (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) ((I : ℂ) : ℂ) : ℂ) ∧
    0 < Metric.infDist ((I : ℂ) : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ) := by
  obtain ⟨B, T1, T2, T3, T4, E, C, o1, o2, o3, o4, r1, r2, r3, r4, t1, t2, t3, t4, q1, q2, q3, q4, vx, fr⟩ := l14wbA_master
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := B
  obtain ⟨e1, e2, e3, e4⟩ := E
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, C, ?_⟩
  have hn := l14_miquel_not_mem_orthoLine h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34 e1 e2 e3 e4 C
  have hP : (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) ((I : ℂ) : ℂ) : ℂ) = -1 := by
    have := congrArg (fun z => 2 * z - (I : ℂ)) vx
    simp only [l14b_midpoint] at this
    linear_combination this
  refine ⟨vx, by rw [vx]; norm_num [Complex.ext_iff], by rw [vx, hP]; norm_num [Complex.ext_iff], ?_⟩
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist]
  refine dist_pos.2 fun h => hn ?_
  rw [h]; exact EuclideanGeometry.orthogonalProjection_mem _

/-- Witness for `l14_newton_perp_orthoLine`: the Newton–Gauss directions are nonzero and the directrix contains two distinct orthocentres. -/
theorem l14w_newton_perp_orthoLine :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧ ((I : ℂ) ∈ T1.circumsphere ∧ (I : ℂ) ∈ T2.circumsphere ∧ (I : ℂ) ∈ T3.circumsphere ∧ (I : ℂ) ∈ T4.circumsphere) ∧
    Module.finrank ℝ (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)).direction = 1 ∧
    midpoint ℝ (-2 : ℂ) (1 - I) ≠ midpoint ℝ (0 : ℂ) (-3 - 3 * I) ∧
    midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I) ≠ midpoint ℝ (0 : ℂ) (-3 - 3 * I) ∧
    T1.orthocenter ≠ T2.orthocenter := by
  obtain ⟨B, T1, T2, T3, T4, E, C, o1, o2, o3, o4, r1, r2, r3, r4, t1, t2, t3, t4, q1, q2, q3, q4, vx, fr⟩ := l14wbA_master
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := B
  obtain ⟨e1, e2, e3, e4⟩ := E
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, C, ?_⟩
  refine ⟨fr, ?_⟩
  simp only [l14b_midpoint]
  rw [o1, o2]
  exact ⟨by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff]⟩

/-- Witness for `l14_lambert` / `l14_miquel_existsUnique`: the Miquel point differs from the six vertices, and the four tangency points are pairwise distinct. -/
theorem l14w_lambert :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧ ((I : ℂ) ∈ T1.circumsphere ∧ (I : ℂ) ∈ T2.circumsphere ∧ (I : ℂ) ∈ T3.circumsphere ∧ (I : ℂ) ∈ T4.circumsphere) ∧
    ((I : ℂ) : ℂ) ≠ -2 ∧
    ((I : ℂ) : ℂ) ≠ -3 - 3 * I ∧
    ((I : ℂ) : ℂ) ≠ -3/2 + 3/2 * I ∧
    ((I : ℂ) : ℂ) ≠ 0 ∧
    ((I : ℂ) : ℂ) ≠ 1 - I ∧
    ((I : ℂ) : ℂ) ≠ 3 ∧
    (1 : ℂ) ≠ (-1/2 + 1/2 * I : ℂ) ∧
    (1 : ℂ) ≠ (-1/2 + 9/2 * I : ℂ) ∧
    (1 : ℂ) ≠ (7 + 2 * I : ℂ) ∧
    (-1/2 + 1/2 * I : ℂ) ≠ (-1/2 + 9/2 * I : ℂ) ∧
    (-1/2 + 1/2 * I : ℂ) ≠ (7 + 2 * I : ℂ) ∧
    (-1/2 + 9/2 * I : ℂ) ≠ (7 + 2 * I : ℂ) := by
  obtain ⟨B, T1, T2, T3, T4, E, C, o1, o2, o3, o4, r1, r2, r3, r4, t1, t2, t3, t4, q1, q2, q3, q4, vx, fr⟩ := l14wbA_master
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := B
  obtain ⟨e1, e2, e3, e4⟩ := E
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, C, ?_⟩
  norm_num [Complex.ext_iff]

theorem l14wbP_base :
    (0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) := by
  have h1 : (0 : ℂ) ≠ 1 := by norm_num [Complex.ext_iff]
  have h2 : (0 : ℂ) ≠ I := by norm_num [Complex.ext_iff]
  have h3 : (-I : ℂ) ≠ -1 - 2 * I := by norm_num [Complex.ext_iff]
  have h4 : (-2 + 3 * I : ℂ) ≠ 2 + I := by norm_num [Complex.ext_iff]
  have m12 : (0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h2]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m13 : (1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m14 : (4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m23 : (-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] := by
    rw [l14b_mem_iff h2, l14b_mem_iff h3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m24 : (2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I] := by
    rw [l14b_mem_iff h2, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m34 : (2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I] := by
    rw [l14b_mem_iff h3, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨h1, h2, h3, h4, (by rw [l14b_parallel_iff h1 h2]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h1 h3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h1 h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h2 h3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h2 h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by rw [l14b_parallel_iff h3 h4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (l14b_noconc h1 h2 h3 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m12 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])), (l14b_noconc h1 h2 h4 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m12 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])), (l14b_noconc h1 h3 h4 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m13 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])), (l14b_noconc h2 h3 h4 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m23 (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])), m12, m13, m14, m23, m24, m34⟩

theorem l14wbP_vals :
    GenPos (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) ∧
    meet (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) = 0 ∧
    meet (⟨0, 1 - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) = 1 ∧
    meet (⟨0, 1 - (0)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 4 ∧
    meet (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) = -I ∧
    meet (⟨0, I - (0)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 2 * I ∧
    meet (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 2 + I ∧
    miquelPt (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = (1 - I : ℂ) ∧
    ortho (-I) (2 * I) (2 + I) = 1 + I ∧
    ortho (1) (4) (2 + I) = 2 + 2 * I ∧
    ortho (0) (4) (2 * I) = 0 ∧
    ortho (0) (1) (-I) = 0 ∧
    foot ((1 - I : ℂ)) (⟨0, 1 - (0)⟩ : Line) = 1 ∧
    foot ((1 - I : ℂ)) (⟨0, I - (0)⟩ : Line) = -I ∧
    reflPt ((1 - I : ℂ)) (⟨0, 1 - (0)⟩ : Line) = 1 + I ∧
    reflPt ((1 - I : ℂ)) (⟨0, I - (0)⟩ : Line) = -1 - I ∧
    reflPt ((1 - I : ℂ)) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) = 0 ∧
    reflPt ((1 - I : ℂ)) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 3 + 3 * I ∧
    tanPt (⟨0, 1 - (0)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 2 ∧
    tanPt (⟨0, I - (0)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = -2 * I ∧
    tanPt (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 1/2 - 1/2 * I ∧
    tanPt (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 8 - 2 * I ∧
    vertex (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 1/2 - 1/2 * I := by
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := l14wbP_base
  obtain ⟨hG, e12, e13, e14, e23, e24, e34⟩ := l14b_setup h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34
  have hM : miquelPt (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = (1 - I : ℂ) := by
    rw [miquelPt, ← e12, ← e13, ← e14, ← e23, ← e24]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hf1 : foot ((1 - I : ℂ)) (⟨0, 1 - (0)⟩ : Line) = 1 := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hf2 : foot ((1 - I : ℂ)) (⟨0, I - (0)⟩ : Line) = -I := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hr1 : reflPt ((1 - I : ℂ)) (⟨0, 1 - (0)⟩ : Line) = 1 + I := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hr2 : reflPt ((1 - I : ℂ)) (⟨0, I - (0)⟩ : Line) = -1 - I := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hr3 : reflPt ((1 - I : ℂ)) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) = 0 := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hr4 : reflPt ((1 - I : ℂ)) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 3 + 3 * I := by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have ht1 : tanPt (⟨0, 1 - (0)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 2 := by
    rw [tanPt, perpMeet, dirW, hM, hf1, hf2, hr1]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have ht2 : tanPt (⟨0, I - (0)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = -2 * I := by
    rw [tanPt, perpMeet, dirW, hM, hf1, hf2, hr2]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have ht3 : tanPt (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 1/2 - 1/2 * I := by
    rw [tanPt, perpMeet, dirW, hM, hf1, hf2, hr3]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have ht4 : tanPt (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) = 8 - 2 * I := by
    rw [tanPt, perpMeet, dirW, hM, hf1, hf2, hr4]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨hG, e12.symm, e13.symm, e14.symm, e23.symm, e24.symm, e34.symm, hM, (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), (by norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]), hf1, hf2, hr1, hr2, hr3, hr4, ht1, ht2, ht3, ht4, by rw [vertex, directrix, dirW, hM, hf1, hf2, ← e12, ← e13, ← e23]; norm_num [Complex.ext_iff, cr, foot, reflPt, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]⟩

theorem l14wbP_master :
    ((0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-I : ℂ), 2 * I, 2 + I] ∧ T2.points = ![(1 : ℂ), 4, 2 + I] ∧ T3.points = ![(0 : ℂ), 4, 2 * I] ∧ T4.points = ![(0 : ℂ), 1, -I]) ∧ ((1 - I : ℂ) ∈ T1.circumsphere ∧ (1 - I : ℂ) ∈ T2.circumsphere ∧ (1 - I : ℂ) ∈ T3.circumsphere ∧ (1 - I : ℂ) ∈ T4.circumsphere) ∧
    T1.orthocenter = 1 + I ∧
    T2.orthocenter = 2 + 2 * I ∧
    T3.orthocenter = 0 ∧
    T4.orthocenter = 0 ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (1 - I : ℂ) = 1 + I ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), I] (1 - I : ℂ) = -1 - I ∧
    EuclideanGeometry.reflection line[ℝ, (-I : ℂ), -1 - 2 * I] (1 - I : ℂ) = 0 ∧
    EuclideanGeometry.reflection line[ℝ, (-2 + 3 * I : ℂ), 2 + I] (1 - I : ℂ) = 3 + 3 * I ∧
    ((2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ dist (2 : ℂ) (1 - I : ℂ) = Metric.infDist (2 : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    ((-2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ dist (-2 * I : ℂ) (1 - I : ℂ) = Metric.infDist (-2 * I : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    ((1/2 - 1/2 * I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ dist (1/2 - 1/2 * I : ℂ) (1 - I : ℂ) = Metric.infDist (1/2 - 1/2 * I : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    ((8 - 2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧ dist (8 - 2 * I : ℂ) (1 - I : ℂ) = Metric.infDist (8 - 2 * I : ℂ) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ)) ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (2 : ℂ) : ℂ) = 1 + I ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (-2 * I : ℂ) : ℂ) = -1 - I ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (1/2 - 1/2 * I : ℂ) : ℂ) = 0 ∧
    (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (8 - 2 * I : ℂ) : ℂ) = 3 + 3 * I ∧
    midpoint ℝ ((1 - I : ℂ) : ℂ) (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) ((1 - I : ℂ) : ℂ) : ℂ) = 1/2 - 1/2 * I ∧
    Module.finrank ℝ (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)).direction = 1 := by
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := l14wbP_base
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, ?_⟩
  obtain ⟨hG, -⟩ := l14b_setup h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34
  obtain ⟨T1, T2, T3, T4, e1, e2, e3, e4⟩ := l14_triangles_exist h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34
  obtain ⟨-, v12, v13, v14, v23, v24, v34, vM, o1, o2, o3, o4, -, -, r1, r2, r3, r4, t1, t2, t3, t4, vV⟩ := l14wbP_vals
  have e1' : T1.points = ![meet (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line), meet (⟨0, I - (0)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line), meet (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line)] := by
    rw [e1, v23, v24, v34]
  have e2' : T2.points = ![meet (⟨0, 1 - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line), meet (⟨0, 1 - (0)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line), meet (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line)] := by
    rw [e2, v13, v14, v34]
  have e3' : T3.points = ![meet (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line), meet (⟨0, 1 - (0)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line), meet (⟨0, I - (0)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line)] := by
    rw [e3, v12, v14, v24]
  have e4' : T4.points = ![meet (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line), meet (⟨0, 1 - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line), meet (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line)] := by
    rw [e4, v12, v13, v23]
  have hMc := l14b_miquel_mem hG e1' e2' e3' e4'
  rw [vM] at hMc
  obtain ⟨-, -, -, -, -, -, -, -, O1, O2, O3, O4, -, R1, R2, R3, R4, TP, VX⟩ := l14b_transfer h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34 e1 e2 e3 e4 hMc
  have TA := l14_tanPt_all h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34 e1 e2 e3 e4 hMc
  have tp : ∀ {p q : ℂ}, (p, q) ∈ ({(0, 1), (0, I), (-I, -1 - 2 * I), (-2 + 3 * I, 2 + I)} : Set (ℂ × ℂ)) →
      tanPt ⟨p, q - p⟩ (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line) ∈ line[ℝ, p, q] ∧ dist (tanPt ⟨p, q - p⟩ (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line)) (1 - I : ℂ) = Metric.infDist (tanPt ⟨p, q - p⟩ (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line)) ((affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) : Set ℂ) ∧
      (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)) (tanPt ⟨p, q - p⟩ (⟨0, 1 - (0)⟩ : Line) (⟨0, I - (0)⟩ : Line) (⟨-I, -1 - 2 * I - (-I)⟩ : Line) (⟨-2 + 3 * I, 2 + I - (-2 + 3 * I)⟩ : Line)) : ℂ) = EuclideanGeometry.reflection line[ℝ, p, q] (1 - I : ℂ) := by
    intro p q hpq
    obtain ⟨m, d⟩ := TP _ hpq
    obtain ⟨z, -, -, hu, hz⟩ := TA _ hpq
    have := hu _ m d
    exact ⟨m, d, by rw [this]; exact hz⟩
  obtain ⟨tm1, td1, tq1⟩ := tp (p := 0) (q := 1) (by simp)
  rw [t1] at tm1 td1 tq1
  obtain ⟨tm2, td2, tq2⟩ := tp (p := 0) (q := I) (by simp)
  rw [t2] at tm2 td2 tq2
  obtain ⟨tm3, td3, tq3⟩ := tp (p := -I) (q := -1 - 2 * I) (by simp)
  rw [t3] at tm3 td3 tq3
  obtain ⟨tm4, td4, tq4⟩ := tp (p := -2 + 3 * I) (q := 2 + I) (by simp)
  rw [t4] at tm4 td4 tq4
  rw [vV] at VX
  refine ⟨T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, hMc, by rw [O1, o1], by rw [O2, o2], by rw [O3, o3], by rw [O4, o4], by rw [R1, r1], by rw [R2, r2], by rw [R3, r3], by rw [R4, r4], ⟨tm1, td1⟩, ⟨tm2, td2⟩, ⟨tm3, td3⟩, ⟨tm4, td4⟩, by rw [tq1, R1, r1], by rw [tq2, R2, r2], by rw [tq3, R3, r3], by rw [tq4, R4, r4], VX, l14_directrix_finrank h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34 e1 e2 e3 e4⟩

/-- Witness for the perpendicular case (`L₁ ⟂ L₂`, so `H₃ = H₄`) of `l14_reflections_collinear` / `l14_reflPt_mem_orthoLine`: the hypotheses hold, `H₃ = H₄`, the span of the orthocentres is still a line, and the four reflections are pairwise distinct. -/
theorem l14w_reflections_perp :
    ((0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-I : ℂ), 2 * I, 2 + I] ∧ T2.points = ![(1 : ℂ), 4, 2 + I] ∧ T3.points = ![(0 : ℂ), 4, 2 * I] ∧ T4.points = ![(0 : ℂ), 1, -I]) ∧ ((1 - I : ℂ) ∈ T1.circumsphere ∧ (1 - I : ℂ) ∈ T2.circumsphere ∧ (1 - I : ℂ) ∈ T3.circumsphere ∧ (1 - I : ℂ) ∈ T4.circumsphere) ∧
    Module.finrank ℝ (affineSpan ℝ ({T1.orthocenter, T2.orthocenter, T3.orthocenter, T4.orthocenter} : Set ℂ)).direction = 1 ∧
    T3.orthocenter = T4.orthocenter ∧
    T1.orthocenter ≠ T3.orthocenter ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (1 - I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (0 : ℂ), I] (1 - I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (1 - I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-I : ℂ), -1 - 2 * I] (1 - I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), 1] (1 - I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-2 + 3 * I : ℂ), 2 + I] (1 - I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), I] (1 - I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-I : ℂ), -1 - 2 * I] (1 - I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (0 : ℂ), I] (1 - I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-2 + 3 * I : ℂ), 2 + I] (1 - I : ℂ) ∧
    EuclideanGeometry.reflection line[ℝ, (-I : ℂ), -1 - 2 * I] (1 - I : ℂ) ≠ EuclideanGeometry.reflection line[ℝ, (-2 + 3 * I : ℂ), 2 + I] (1 - I : ℂ) := by
  obtain ⟨B, T1, T2, T3, T4, E, C, o1, o2, o3, o4, r1, r2, r3, r4, t1, t2, t3, t4, q1, q2, q3, q4, vx, fr⟩ := l14wbP_master
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := B
  obtain ⟨e1, e2, e3, e4⟩ := E
  refine ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, C, ?_⟩
  refine ⟨fr, ?_⟩
  rw [o1, o3, o4, r1, r2, r3, r4]
  exact ⟨by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff], by norm_num [Complex.ext_iff]⟩

end QuadMiquel
