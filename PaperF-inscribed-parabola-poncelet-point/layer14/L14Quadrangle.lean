import QuadMiquel.QuadrangleSym

/-!
# Layer 14 (Part B): Mathlib-only restatements of the quadrangle theorems

Every `l14_*` theorem below has a statement mentioning only Mathlib notions: four points
`a b c d : ℂ` with no three collinear (`¬ Collinear ℝ {x, y, z}`), the four Mathlib triangles
`Tabc Tabd Tacd Tbcd` with the given vertices, their `ninePointCircle`s and `orthocenter`s,
feet as `EuclideanGeometry.orthogonalProjection` onto `line[ℝ, x, y]`, diagonal points as points
of `line[ℝ, a, b] ∩ line[ℝ, c, d]` etc., and `EuclideanGeometry.Cospherical`. The Poncelet point
is not given by a formula: it is any common point of the nine-point circles (`l14_poncelet_on_ninepoint`
shows there is exactly one when `d` is not the orthocentre of `abc`).
The `l14b_*` lemmas are the bridges to the library's own definitions; the `l14w_*` theorems are
explicit witnesses (non-vacuity).
-/

open Complex ComplexConjugate

namespace QuadMiquel

/-! ### Bridges -/

theorem l14b_cr_ne {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : cr (b - a) (c - a) ≠ 0 :=
  fun h0 => h (collinear_of_cr h0)

theorem l14b_QGen {a b c d : ℂ} (habc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (habd : ¬ Collinear ℝ ({a, b, d} : Set ℂ)) (hacd : ¬ Collinear ℝ ({a, c, d} : Set ℂ))
    (hbcd : ¬ Collinear ℝ ({b, c, d} : Set ℂ)) : QGen a b c d :=
  ⟨l14b_cr_ne habc, l14b_cr_ne habd, l14b_cr_ne hacd, l14b_cr_ne hbcd⟩

theorem l14b_tri {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : T = tri hn :=
  Affine.Simplex.ext fun i => by rw [e]; rfl

theorem l14b_orthocenter {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : T.orthocenter = ortho a b c := by
  rw [ortho_eq_orthocenter hn, l14b_tri e hn]; rfl

theorem l14b_mem_npc {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) (w : ℂ) :
    w ∈ T.ninePointCircle ↔ dist w (npc a b c) = dist ((a + b) / 2) (npc a b c) := by
  rw [l14b_tri e hn, mem_ninePointCircle_iff]

theorem l14b_npc {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    T.ninePointCircle = (tri hn).ninePointCircle := by rw [l14b_tri e hn]

/-- The Mathlib foot on `line[ℝ, p, q]` is the library's `foot` on `lineThrough p q`. -/
theorem l14b_foot {p q : ℂ} (h : p ≠ q) (z : ℂ) :
    (EuclideanGeometry.orthogonalProjection line[ℝ, p, q] z : ℂ) = foot z (lineThrough p q) := by
  have := foot_eq_orthogonalProjection z (lineThrough p q) (sub_ne_zero.2 h.symm)
  simp only [lineThrough, add_sub_cancel] at this
  exact this.symm

/-- A point of `line[ℝ, p, q] ∩ line[ℝ, r, s]` (non-parallel) is the library's `diagPt`. -/
theorem l14b_diag {p q r s x : ℂ} (hpq : p ≠ q) (hrs : r ≠ s)
    (hn : ¬ (line[ℝ, p, q]).Parallel (line[ℝ, r, s])) (hx : x ∈ line[ℝ, p, q] ∧ x ∈ line[ℝ, r, s]) :
    x = diagPt p q r s := by
  have hc := cr_ne_of_not_parallel hpq hrs hn
  refine (meet_eq_iff (L := lineThrough p q) (M := lineThrough r s) ?_ x).1 ?_
  · simpa [lineThrough] using hc
  · rw [lineThrough_carrier hpq, lineThrough_carrier hrs]; exact hx

theorem l14b_ne_of_ncol {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply h
  · simpa using collinear_pair ℝ a c
  · simpa [Set.insert_comm] using collinear_pair ℝ b a
  · simpa [Set.pair_comm] using collinear_pair ℝ a b

/-- Two simplices with the same vertex set have the same nine-point circle. -/
theorem l14b_ninePointCircle_eq_of_range_eq {s₁ s₂ : Affine.Triangle ℝ ℂ}
    (h : Set.range s₁.points = Set.range s₂.points) : s₁.ninePointCircle = s₂.ninePointCircle := by
  have hc := Affine.Simplex.circumcenter_eq_of_range_eq h
  have hr : s₁.circumradius = s₂.circumradius := by
    have hi : s₁.points 0 ∈ Set.range s₂.points := h ▸ Set.mem_range_self _
    obtain ⟨j, hj⟩ := hi
    rw [← s₁.dist_circumcenter_eq_circumradius 0, ← hj, hc, s₂.dist_circumcenter_eq_circumradius]
  ext
  · rw [Affine.Simplex.ninePointCircle_center, Affine.Simplex.ninePointCircle_center, hc,
      show s₁.centroid = s₂.centroid from Affine.Simplex.centroid_eq_of_range_eq h]
  · rw [Affine.Simplex.ninePointCircle_radius, Affine.Simplex.ninePointCircle_radius, hr]

theorem l14b_range3 (T : Affine.Triangle ℝ ℂ) :
    Set.range T.points = {T.points 0, T.points 1, T.points 2} := by
  ext x; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_succ,
    Fin.exists_fin_zero]
  constructor
  · rintro (h | h | h | ⟨⟨⟩⟩) <;> [exact Or.inl h.symm; exact Or.inr (Or.inl h.symm);
      exact Or.inr (Or.inr h.symm)]
  · rintro (h | h | h) <;> [exact Or.inl h.symm; exact Or.inr (Or.inl h.symm);
      exact Or.inr (Or.inr (Or.inl h.symm))]

/-- On a cospherical quadruple with `a b c` non-collinear, `d` is on the circumcircle of `abc`. -/
theorem l14b_cosph {a b c d : ℂ} (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hc : EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    dist d (circ a b c) = dist a (circ a b c) := by
  obtain ⟨o, r, ho⟩ := hc
  set T : Affine.Triangle ℝ ℂ := ⟨![a, b, c], affineIndependent_iff_not_collinear_set.2 hn⟩
  have htop : affineSpan ℝ (Set.range T.points) = ⊤ := by
    rw [T.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one, Complex.finrank_real_complex]
    simp
  have hoc : o = T.circumcenter := by
    refine T.eq_circumcenter_of_dist_eq (by rw [htop]; trivial) (r := r) ?_
    intro i; fin_cases i
    · exact ho a (by simp)
    · exact ho b (by simp)
    · exact ho c (by simp)
  rw [circ_eq_circumcenter hn, ← hoc, ho d (by simp), ho a (by simp)]

theorem l14b_parallel_iff {p q p' q' : ℂ} (h : p ≠ q) (h' : p' ≠ q') :
    line[ℝ, p, q].Parallel line[ℝ, p', q'] ↔ cr (q - p) (q' - p') = 0 := by
  have := parallel_iff_cr (L := lineThrough p q) (M := lineThrough p' q') (sub_ne_zero.2 h.symm)
    (sub_ne_zero.2 h'.symm)
  simpa [lineThrough] using this

theorem l14b_range_sub {T : Affine.Triangle ℝ ℂ} {p q r : ℂ}
    (h : Set.range T.points ⊆ {p, q, r}) : Set.range T.points = {p, q, r} := by
  classical
  have hinj := T.independent.injective
  set F : Finset ℂ := Finset.univ.image T.points with hFdef
  have hF : (F : Set ℂ) = Set.range T.points := by simp [F]
  have hc : F.card = 3 := by rw [Finset.card_image_of_injective _ hinj]; simp
  have hsub : F ⊆ {p, q, r} := by
    intro x hx
    have hx' : x ∈ Set.range T.points := by rw [← hF]; exact hx
    have := h hx'
    simpa using this
  have he := Finset.eq_of_subset_of_card_le hsub (by rw [hc]; exact Finset.card_le_three)
  rw [← hF, he]; simp

theorem l14b_tri_cases {a b c d : ℂ} (habc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (habd : ¬ Collinear ℝ ({a, b, d} : Set ℂ)) (hacd : ¬ Collinear ℝ ({a, c, d} : Set ℂ))
    {T : Affine.Triangle ℝ ℂ} (h : Set.range T.points ⊆ {a, b, c, d}) :
    Set.range T.points = {a, b, c} ∨ Set.range T.points = {a, b, d} ∨
      Set.range T.points = {a, c, d} ∨ Set.range T.points = {b, c, d} := by
  classical
  obtain ⟨hab, hac, hbc⟩ := l14b_ne_of_ncol habc
  obtain ⟨-, had, hbd⟩ := l14b_ne_of_ncol habd
  obtain ⟨-, -, hcd⟩ := l14b_ne_of_ncol hacd
  have sub : ∀ {x : ℂ} {s : Set ℂ}, x ∉ Set.range T.points → Set.range T.points ⊆ insert x s →
      Set.range T.points ⊆ s := fun hx hs y hy => by
    rcases hs hy with rfl | h' <;> [exact absurd hy hx; exact h']
  by_cases hd : d ∈ Set.range T.points
  · by_cases hc : c ∈ Set.range T.points
    · by_cases hb : b ∈ Set.range T.points
      · by_cases ha : a ∈ Set.range T.points
        · exfalso
          have hinj := T.independent.injective
          set F : Finset ℂ := Finset.univ.image T.points
          have hF : (F : Set ℂ) = Set.range T.points := by simp [F]
          have hc3 : F.card = 3 := by rw [Finset.card_image_of_injective _ hinj]; simp
          have hsub : ({a, b, c, d} : Finset ℂ) ⊆ F := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rw [← Finset.mem_coe, hF]
            rcases hx with rfl | rfl | rfl | rfl <;> assumption
          have h4 : ({a, b, c, d} : Finset ℂ).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
              Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
          have := Finset.card_le_card hsub
          omega
        · exact Or.inr (Or.inr (Or.inr (l14b_range_sub (sub ha h))))
      · refine Or.inr (Or.inr (Or.inl (l14b_range_sub ?_)))
        intro y hy
        rcases h hy with rfl | rfl | h'
        · simp
        · exact absurd hy hb
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h' ⊢; tauto
    · refine Or.inr (Or.inl (l14b_range_sub ?_))
      intro y hy
      rcases h hy with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact absurd hy hc
      · simp
  · refine Or.inl (l14b_range_sub ?_)
    intro y hy
    rcases h hy with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · exact absurd hy hd
/-! ### The Mathlib-only statements -/

section Config

variable {a b c d : ℂ} (habc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
  (habd : ¬ Collinear ℝ ({a, b, d} : Set ℂ)) (hacd : ¬ Collinear ℝ ({a, c, d} : Set ℂ))
  (hbcd : ¬ Collinear ℝ ({b, c, d} : Set ℂ))
  {Tabc Tabd Tacd Tbcd : Affine.Triangle ℝ ℂ}
  (eabc : Tabc.points = ![a, b, c]) (eabd : Tabd.points = ![a, b, d])
  (eacd : Tacd.points = ![a, c, d]) (ebcd : Tbcd.points = ![b, c, d])
include habc habd hacd hbcd eabc eabd eacd ebcd

theorem l14b_transfer (w : ℂ) :
    (w ∈ Tabc.ninePointCircle ↔ w ∈ (tri (l14b_QGen habc habd hacd hbcd).ncol_abc).ninePointCircle) ∧
    (w ∈ Tabd.ninePointCircle ↔ w ∈ (tri (l14b_QGen habc habd hacd hbcd).ncol_abd).ninePointCircle) ∧
    (w ∈ Tacd.ninePointCircle ↔ w ∈ (tri (l14b_QGen habc habd hacd hbcd).ncol_acd).ninePointCircle) ∧
    (w ∈ Tbcd.ninePointCircle ↔ w ∈ (tri (l14b_QGen habc habd hacd hbcd).ncol_bcd).ninePointCircle) := by
  rw [l14b_npc eabc habc, l14b_npc eabd habd, l14b_npc eacd hacd, l14b_npc ebcd hbcd]
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

omit eabc eabd eacd ebcd in
/-- The Mathlib triangles exist (non-collinear triples are affinely independent). -/
theorem l14_triangles_exist :
    ∃ T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ, T₁.points = ![a, b, c] ∧ T₂.points = ![a, b, d] ∧
      T₃.points = ![a, c, d] ∧ T₄.points = ![b, c, d] := by
  exact ⟨tri habc, tri habd, tri hacd, tri hbcd, rfl, rfl, rfl, rfl⟩

theorem l14b_poncelet_mem (ho : d ≠ Tabc.orthocenter) :
    poncelet a b c d ∈ Tabc.ninePointCircle ∧ poncelet a b c d ∈ Tabd.ninePointCircle ∧
      poncelet a b c d ∈ Tacd.ninePointCircle ∧ poncelet a b c d ∈ Tbcd.ninePointCircle := by
  have h := l14b_QGen habc habd hacd hbcd
  rw [l14b_orthocenter eabc habc] at ho
  obtain ⟨t1, t2, t3, t4⟩ := l14b_transfer habc habd hacd hbcd eabc eabd eacd ebcd (poncelet a b c d)
  obtain ⟨k1, k2, k3, k4⟩ := ninepoint_concur h ho
  exact ⟨t1.2 k1, t2.2 k2, t3.2 k3, t4.2 k4⟩

theorem l14b_poncelet_eq (ho : d ≠ Tabc.orthocenter) {w : ℂ} (h1 : w ∈ Tabc.ninePointCircle)
    (h2 : w ∈ Tabd.ninePointCircle) (h3 : w ∈ Tacd.ninePointCircle) : w = poncelet a b c d := by
  have h := l14b_QGen habc habd hacd hbcd
  rw [l14b_orthocenter eabc habc] at ho
  obtain ⟨t1, t2, t3, -⟩ := l14b_transfer habc habd hacd hbcd eabc eabd eacd ebcd w
  exact ninepoint_unique h ho (t1.1 h1) (t2.1 h2) (t3.1 h3)

/-- **D2 (concurrence)**, Mathlib form. -/
theorem l14_ninepoint_concur (ho : d ≠ Tabc.orthocenter) :
    ∃ P : ℂ, P ∈ Tabc.ninePointCircle ∧ P ∈ Tabd.ninePointCircle ∧ P ∈ Tacd.ninePointCircle ∧
      P ∈ Tbcd.ninePointCircle :=
  ⟨_, l14b_poncelet_mem habc habd hacd hbcd eabc eabd eacd ebcd ho⟩

/-- **D2 (uniqueness)**, Mathlib form: the nine-point circles of `abc`, `abd`, `acd` have at most
one common point. -/
theorem l14_ninepoint_unique (ho : d ≠ Tabc.orthocenter) {w w' : ℂ}
    (h1 : w ∈ Tabc.ninePointCircle) (h2 : w ∈ Tabd.ninePointCircle) (h3 : w ∈ Tacd.ninePointCircle)
    (h1' : w' ∈ Tabc.ninePointCircle) (h2' : w' ∈ Tabd.ninePointCircle)
    (h3' : w' ∈ Tacd.ninePointCircle) : w = w' := by
  rw [l14b_poncelet_eq habc habd hacd hbcd eabc eabd eacd ebcd ho h1 h2 h3,
    l14b_poncelet_eq habc habd hacd hbcd eabc eabd eacd ebcd ho h1' h2' h3']

/-- **D1**, Mathlib form: exactly one point lies on the four nine-point circles. -/
theorem l14_poncelet_on_ninepoint (ho : d ≠ Tabc.orthocenter) :
    ∃! P : ℂ, P ∈ Tabc.ninePointCircle ∧ P ∈ Tabd.ninePointCircle ∧ P ∈ Tacd.ninePointCircle ∧
      P ∈ Tbcd.ninePointCircle :=
  ⟨_, l14b_poncelet_mem habc habd hacd hbcd eabc eabd eacd ebcd ho,
    fun w hw => l14b_poncelet_eq habc habd hacd hbcd eabc eabd eacd ebcd ho hw.1 hw.2.1 hw.2.2.1⟩

/-- **D3 (circles)**, Mathlib form. -/
theorem l14_orthocentric_ninePointCircle_eq (ho : d = Tabc.orthocenter) :
    Tabd.ninePointCircle = Tabc.ninePointCircle ∧ Tacd.ninePointCircle = Tabc.ninePointCircle ∧
      Tbcd.ninePointCircle = Tabc.ninePointCircle := by
  have h := l14b_QGen habc habd hacd hbcd
  rw [l14b_orthocenter eabc habc] at ho
  rw [l14b_npc eabc habc, l14b_npc eabd habd, l14b_npc eacd hacd, l14b_npc ebcd hbcd]
  exact orthocentric_ninePointCircle_eq h ho

/-- **D3 (finding)**, Mathlib form of `ponDen_eq_zero_iff`: the four nine-point circles have a
unique common point iff `d` is not the orthocentre of `abc`; in the orthocentric case the midpoints
of `ab` and `ac` are two distinct common points. -/
theorem l14_ponDen_eq_zero_iff :
    (∃! P : ℂ, P ∈ Tabc.ninePointCircle ∧ P ∈ Tabd.ninePointCircle ∧ P ∈ Tacd.ninePointCircle ∧
      P ∈ Tbcd.ninePointCircle) ↔ d ≠ Tabc.orthocenter := by
  refine ⟨fun hu ho => ?_, l14_poncelet_on_ninepoint habc habd hacd hbcd eabc eabd eacd ebcd⟩
  obtain ⟨e2, e3, e4⟩ := l14_orthocentric_ninePointCircle_eq habc habd hacd hbcd eabc eabd eacd
    ebcd ho
  have hm1 : midpoint ℝ a b ∈ Tabc.ninePointCircle := by
    rw [l14b_mem_npc eabc habc, midpoint_eq_smul_add ℝ a b, invOf_eq_inv, Complex.real_smul]
    push_cast; ring_nf
  have hm2 : midpoint ℝ a c ∈ Tabc.ninePointCircle := by
    rw [l14b_mem_npc eabc habc, midpoint_eq_smul_add ℝ a c, invOf_eq_inv, Complex.real_smul]
    obtain ⟨-, m2⟩ := npc_mid (l14b_cr_ne habc)
    push_cast; rw [← m2]; ring_nf
  obtain ⟨-, -, hbc⟩ := l14b_ne_of_ncol habc
  apply hbc
  have := hu.unique (y₁ := midpoint ℝ a b) (y₂ := midpoint ℝ a c)
    ⟨hm1, by rw [e2]; exact hm1, by rw [e3]; exact hm1, by rw [e4]; exact hm1⟩
    ⟨hm2, by rw [e2]; exact hm2, by rw [e3]; exact hm2, by rw [e4]; exact hm2⟩
  have := congrArg (fun z => 2 * z - a) this
  simp only [midpoint_eq_smul_add ℝ, invOf_eq_inv, Complex.real_smul] at this
  push_cast at this
  linear_combination this

variable (ho : d ≠ Tabc.orthocenter) {P : ℂ}
  (hP : P ∈ Tabc.ninePointCircle ∧ P ∈ Tabd.ninePointCircle ∧ P ∈ Tacd.ninePointCircle ∧
    P ∈ Tbcd.ninePointCircle)
include ho hP

theorem l14b_P : P = poncelet a b c d :=
  l14b_poncelet_eq habc habd hacd hbcd eabc eabd eacd ebcd ho hP.1 hP.2.1 hP.2.2.1

/-- **D4 (vertex `d`)**, Mathlib form. -/
theorem l14_poncelet_on_pedal_d (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical ({(EuclideanGeometry.orthogonalProjection line[ℝ, a, b] d : ℂ),
      (EuclideanGeometry.orthogonalProjection line[ℝ, b, c] d : ℂ),
      (EuclideanGeometry.orthogonalProjection line[ℝ, c, a] d : ℂ), P} : Set ℂ) := by
  obtain ⟨hab, hac, hbc⟩ := l14b_ne_of_ncol habc
  rw [l14b_P habc habd hacd hbcd eabc eabd eacd ebcd ho hP, l14b_foot hab, l14b_foot hbc,
    l14b_foot hac.symm]
  exact poncelet_on_pedal_d (l14b_QGen habc habd hacd hbcd)
    (by rwa [l14b_orthocenter eabc habc] at ho) hc

/-- **D4 (vertex `c`)**, Mathlib form. -/
theorem l14_poncelet_on_pedal_c (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical ({(EuclideanGeometry.orthogonalProjection line[ℝ, a, b] c : ℂ),
      (EuclideanGeometry.orthogonalProjection line[ℝ, b, d] c : ℂ),
      (EuclideanGeometry.orthogonalProjection line[ℝ, d, a] c : ℂ), P} : Set ℂ) := by
  obtain ⟨hab, had, hbd⟩ := l14b_ne_of_ncol habd
  rw [l14b_P habc habd hacd hbcd eabc eabd eacd ebcd ho hP, l14b_foot hab, l14b_foot hbd,
    l14b_foot had.symm]
  exact poncelet_on_pedal_c (l14b_QGen habc habd hacd hbcd)
    (by rwa [l14b_orthocenter eabc habc] at ho) hc

/-- **D4 (vertex `b`)**, Mathlib form. -/
theorem l14_poncelet_on_pedal_b (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical ({(EuclideanGeometry.orthogonalProjection line[ℝ, a, c] b : ℂ),
      (EuclideanGeometry.orthogonalProjection line[ℝ, c, d] b : ℂ),
      (EuclideanGeometry.orthogonalProjection line[ℝ, d, a] b : ℂ), P} : Set ℂ) := by
  obtain ⟨hac, had, hcd⟩ := l14b_ne_of_ncol hacd
  rw [l14b_P habc habd hacd hbcd eabc eabd eacd ebcd ho hP, l14b_foot hac, l14b_foot hcd,
    l14b_foot had.symm]
  exact poncelet_on_pedal_b (l14b_QGen habc habd hacd hbcd)
    (by rwa [l14b_orthocenter eabc habc] at ho) hc

/-- **D4 (vertex `a`)**, Mathlib form. -/
theorem l14_poncelet_on_pedal_a (hc : ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set ℂ)) :
    EuclideanGeometry.Cospherical ({(EuclideanGeometry.orthogonalProjection line[ℝ, b, c] a : ℂ),
      (EuclideanGeometry.orthogonalProjection line[ℝ, c, d] a : ℂ),
      (EuclideanGeometry.orthogonalProjection line[ℝ, d, b] a : ℂ), P} : Set ℂ) := by
  obtain ⟨hbc, hbd, hcd⟩ := l14b_ne_of_ncol hbcd
  rw [l14b_P habc habd hacd hbcd eabc eabd eacd ebcd ho hP, l14b_foot hbc, l14b_foot hcd,
    l14b_foot hbd.symm]
  exact poncelet_on_pedal_a (l14b_QGen habc habd hacd hbcd)
    (by rwa [l14b_orthocenter eabc habc] at ho) hc

/-- **D5**, Mathlib form: with opposite sides non-parallel, the three diagonal points (any points
of `ab ∩ cd`, `ac ∩ bd`, `ad ∩ bc`) and the common point `P` of the nine-point circles are
cospherical. -/
theorem l14_poncelet_on_diagonal_circle
    (p1 : ¬ (line[ℝ, a, b]).Parallel (line[ℝ, c, d])) (p2 : ¬ (line[ℝ, a, c]).Parallel (line[ℝ, b, d]))
    (p3 : ¬ (line[ℝ, a, d]).Parallel (line[ℝ, b, c])) {x₁ x₂ x₃ : ℂ}
    (hx₁ : x₁ ∈ line[ℝ, a, b] ∧ x₁ ∈ line[ℝ, c, d]) (hx₂ : x₂ ∈ line[ℝ, a, c] ∧ x₂ ∈ line[ℝ, b, d])
    (hx₃ : x₃ ∈ line[ℝ, a, d] ∧ x₃ ∈ line[ℝ, b, c]) :
    EuclideanGeometry.Cospherical ({x₁, x₂, x₃, P} : Set ℂ) := by
  obtain ⟨hab, hac, hbc⟩ := l14b_ne_of_ncol habc
  obtain ⟨-, had, hbd⟩ := l14b_ne_of_ncol habd
  obtain ⟨-, -, hcd⟩ := l14b_ne_of_ncol hacd
  rw [l14b_P habc habd hacd hbcd eabc eabd eacd ebcd ho hP, l14b_diag hab hcd p1 hx₁,
    l14b_diag hac hbd p2 hx₂, l14b_diag had hbc p3 hx₃]
  exact poncelet_on_diagonal_circle (l14b_QGen habc habd hacd hbcd)
    (by rwa [l14b_orthocenter eabc habc] at ho) p1 p2 p3

/-- **S2 (`S₄`-invariance)**, Mathlib form: the common point `P` of the four nine-point circles is a
property of the *set* `{a, b, c, d}`: it lies on the nine-point circle of every Mathlib triangle
whose vertices are three of the four points (in any order), and any point with that property
(for all such triangles) is `P`. -/
theorem l14_poncelet_S4 :
    (∀ T : Affine.Triangle ℝ ℂ, Set.range T.points ⊆ {a, b, c, d} → P ∈ T.ninePointCircle) ∧
    ∀ w : ℂ, (∀ T : Affine.Triangle ℝ ℂ, Set.range T.points ⊆ {a, b, c, d} →
      w ∈ T.ninePointCircle) → w = P := by
  have hr : ∀ {T₀ : Affine.Triangle ℝ ℂ} {p q r : ℂ}, T₀.points = ![p, q, r] →
      Set.range T₀.points = {p, q, r} := fun e => by rw [l14b_range3, e]; rfl
  refine ⟨fun T hT => ?_, fun w hw => ?_⟩
  · rcases l14b_tri_cases habc habd hacd hT with h | h | h | h
    · rw [l14b_ninePointCircle_eq_of_range_eq (h.trans (hr eabc).symm)]; exact hP.1
    · rw [l14b_ninePointCircle_eq_of_range_eq (h.trans (hr eabd).symm)]; exact hP.2.1
    · rw [l14b_ninePointCircle_eq_of_range_eq (h.trans (hr eacd).symm)]; exact hP.2.2.1
    · rw [l14b_ninePointCircle_eq_of_range_eq (h.trans (hr ebcd).symm)]; exact hP.2.2.2
  · have sub : ∀ {T₀ : Affine.Triangle ℝ ℂ} {p q r : ℂ}, T₀.points = ![p, q, r] →
        ({p, q, r} : Set ℂ) ⊆ {a, b, c, d} → Set.range T₀.points ⊆ {a, b, c, d} :=
      fun e hs => by rw [hr e]; exact hs
    have h1 := hw _ (sub eabc (by intro x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto))
    have h2 := hw _ (sub eabd (by intro x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto))
    have h3 := hw _ (sub eacd (by intro x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto))
    rw [l14b_poncelet_eq habc habd hacd hbcd eabc eabd eacd ebcd ho h1 h2 h3,
      l14b_P habc habd hacd hbcd eabc eabd eacd ebcd ho hP]

end Config

/-! ### Witnesses (non-vacuity) -/

theorem l14b_mem_iff {p q z : ℂ} (h : p ≠ q) : z ∈ line[ℝ, p, q] ↔ cr (q - p) (z - p) = 0 := by
  rw [← SetLike.mem_coe, ← lineThrough_carrier h]; rfl

theorem l14b_ncol {a b c : ℂ} (h : cr (b - a) (c - a) ≠ 0) : ¬ Collinear ℝ ({a, b, c} : Set ℂ) :=
  ncol_of_cr h

theorem l14b_npc_center {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : T.ninePointCircle.center = npc a b c := by
  rw [l14b_tri e hn, npc_eq_ninePointCircle_center hn]; rfl

/-- The general witness `a = 0, b = -i, c = 2 - 2i, d = -1 + 2i` (no two of the six joining
segments are perpendicular; not orthocentric; not concyclic; opposite sides not parallel):
all hypotheses, the explicit common point `1 - i` of the four nine-point circles, the four
nine-point centres, feet and diagonal points. -/
theorem l14wbQ_master :
    ¬ Collinear ℝ ({0, -I, 2 - 2 * I} : Set ℂ) ∧ ¬ Collinear ℝ ({0, -I, -1 + 2 * I} : Set ℂ) ∧
    ¬ Collinear ℝ ({0, 2 - 2 * I, -1 + 2 * I} : Set ℂ) ∧
    ¬ Collinear ℝ ({-I, 2 - 2 * I, -1 + 2 * I} : Set ℂ) ∧
    ∃ Tabc Tabd Tacd Tbcd : Affine.Triangle ℝ ℂ,
      (Tabc.points = ![0, -I, 2 - 2 * I] ∧ Tabd.points = ![0, -I, -1 + 2 * I] ∧
        Tacd.points = ![0, 2 - 2 * I, -1 + 2 * I] ∧ Tbcd.points = ![-I, 2 - 2 * I, -1 + 2 * I]) ∧
      Tabc.orthocenter = -1 - 2 * I ∧ (-1 + 2 * I : ℂ) ≠ Tabc.orthocenter ∧
      ((1 - I : ℂ) ∈ Tabc.ninePointCircle ∧ (1 - I : ℂ) ∈ Tabd.ninePointCircle ∧
        (1 - I : ℂ) ∈ Tacd.ninePointCircle ∧ (1 - I : ℂ) ∈ Tbcd.ninePointCircle) ∧
      Tabc.ninePointCircle.center = 1/4 - 5/4 * I ∧ Tabd.ninePointCircle.center = 5/4 + 3/4 * I ∧
      Tacd.ninePointCircle.center = -11/4 - 9/4 * I ∧ Tbcd.ninePointCircle.center = -3/4 - 5/4 * I ∧
      ¬ EuclideanGeometry.Cospherical ({0, -I, 2 - 2 * I, -1 + 2 * I} : Set ℂ) ∧
      ¬ (line[ℝ, (0 : ℂ), -I]).Parallel (line[ℝ, 2 - 2 * I, -1 + 2 * I]) ∧
      ¬ (line[ℝ, (0 : ℂ), 2 - 2 * I]).Parallel (line[ℝ, -I, -1 + 2 * I]) ∧
      ¬ (line[ℝ, (0 : ℂ), -1 + 2 * I]).Parallel (line[ℝ, -I, 2 - 2 * I]) ∧
      ((2/3 * I : ℂ) ∈ line[ℝ, (0 : ℂ), -I] ∧ (2/3 * I : ℂ) ∈ line[ℝ, 2 - 2 * I, -1 + 2 * I]) ∧
      ((-1/2 + 1/2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), 2 - 2 * I] ∧
        (-1/2 + 1/2 * I : ℂ) ∈ line[ℝ, -I, -1 + 2 * I]) ∧
      ((2/3 - 4/3 * I : ℂ) ∈ line[ℝ, (0 : ℂ), -1 + 2 * I] ∧
        (2/3 - 4/3 * I : ℂ) ∈ line[ℝ, -I, 2 - 2 * I]) ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, (0 : ℂ), -I] (-1 + 2 * I) : ℂ) = 2 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, -I, 2 - 2 * I] (-1 + 2 * I) : ℂ) = -2 ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, 2 - 2 * I, (0 : ℂ)] (-1 + 2 * I) : ℂ) =
        -3/2 + 3/2 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, (0 : ℂ), -I] (2 - 2 * I) : ℂ) = -2 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, -I, -1 + 2 * I] (2 - 2 * I) : ℂ) =
        1/2 - 5/2 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, -1 + 2 * I, (0 : ℂ)] (2 - 2 * I) : ℂ) =
        6/5 - 12/5 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, (0 : ℂ), 2 - 2 * I] (-I) : ℂ) =
        1/2 - 1/2 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, 2 - 2 * I, -1 + 2 * I] (-I) : ℂ) =
        4/5 - 2/5 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, -1 + 2 * I, (0 : ℂ)] (-I) : ℂ) =
        2/5 - 4/5 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, -I, 2 - 2 * I] (0 : ℂ) : ℂ) =
        -2/5 - 4/5 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, 2 - 2 * I, -1 + 2 * I] (0 : ℂ) : ℂ) =
        8/25 + 6/25 * I ∧
      (EuclideanGeometry.orthogonalProjection line[ℝ, -1 + 2 * I, -I] (0 : ℂ) : ℂ) =
        -3/10 - 1/10 * I := by
  have n1 : ¬ Collinear ℝ ({0, -I, 2 - 2 * I} : Set ℂ) := l14b_ncol (by norm_num [cr])
  have n2 : ¬ Collinear ℝ ({0, -I, -1 + 2 * I} : Set ℂ) := l14b_ncol (by norm_num [cr])
  have n3 : ¬ Collinear ℝ ({0, 2 - 2 * I, -1 + 2 * I} : Set ℂ) := l14b_ncol (by norm_num [cr])
  have n4 : ¬ Collinear ℝ ({-I, 2 - 2 * I, -1 + 2 * I} : Set ℂ) := l14b_ncol (by norm_num [cr])
  refine ⟨n1, n2, n3, n4, tri n1, tri n2, tri n3, tri n4, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  have ho : (tri n1).orthocenter = -1 - 2 * I := by
    rw [l14b_orthocenter rfl n1]
    norm_num [ortho, circ, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hpon : poncelet 0 (-I) (2 - 2 * I) (-1 + 2 * I) = 1 - I := by
    norm_num [poncelet, ponDen, pD, pN, Complex.ext_iff, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, pow_two]
  have hne : (-1 + 2 * I : ℂ) ≠ (tri n1).orthocenter := by rw [ho]; norm_num [Complex.ext_iff]
  have hP := l14b_poncelet_mem n1 n2 n3 n4 (Tabc := tri n1) (Tabd := tri n2) (Tacd := tri n3)
    (Tbcd := tri n4) rfl rfl rfl rfl hne
  rw [hpon] at hP
  refine ⟨ho, hne, hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [l14b_npc_center rfl n1]
    norm_num [npc, circ, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_npc_center rfl n2]
    norm_num [npc, circ, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_npc_center rfl n3]
    norm_num [npc, circ, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_npc_center rfl n4]
    norm_num [npc, circ, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · intro hc
    have := l14b_cosph n1 hc
    have e : circ 0 (-I) (2 - 2 * I) = 3/2 - 1/2 * I := by
      norm_num [circ, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
    rw [e, Complex.dist_eq, Complex.dist_eq, Complex.norm_def, Complex.norm_def,
      Real.sqrt_inj (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)] at this
    norm_num [Complex.normSq_apply] at this
  · rw [l14b_parallel_iff (by norm_num [Complex.ext_iff]) (by norm_num [Complex.ext_iff])]; norm_num [cr]
  · rw [l14b_parallel_iff (by norm_num [Complex.ext_iff]) (by norm_num [Complex.ext_iff])]; norm_num [cr]
  · rw [l14b_parallel_iff (by norm_num [Complex.ext_iff]) (by norm_num [Complex.ext_iff])]; norm_num [cr]
  · rw [l14b_mem_iff (by norm_num [Complex.ext_iff]), l14b_mem_iff (by norm_num [Complex.ext_iff])]; norm_num [cr]
  · rw [l14b_mem_iff (by norm_num [Complex.ext_iff]), l14b_mem_iff (by norm_num [Complex.ext_iff])]; norm_num [cr]
  · rw [l14b_mem_iff (by norm_num [Complex.ext_iff]), l14b_mem_iff (by norm_num [Complex.ext_iff])]; norm_num [cr]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [l14b_foot (by norm_num [Complex.ext_iff])]; norm_num [cr, foot, lineThrough, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]

/-- Witness for `l14_poncelet_on_ninepoint`, `l14_ninepoint_concur`, `l14_ninepoint_unique`,
`l14_poncelet_S4` and the non-orthocentric direction of `l14_ponDen_eq_zero_iff`: all hypotheses
hold, `1 - i` is on the four nine-point circles, and the four nine-point circles are pairwise
distinct (distinct centres), so the concurrence is not a degenerate coincidence. -/
theorem l14w_poncelet_on_ninepoint :
    ¬ Collinear ℝ ({0, -I, 2 - 2 * I} : Set ℂ) ∧ ¬ Collinear ℝ ({0, -I, -1 + 2 * I} : Set ℂ) ∧
    ¬ Collinear ℝ ({0, 2 - 2 * I, -1 + 2 * I} : Set ℂ) ∧
    ¬ Collinear ℝ ({-I, 2 - 2 * I, -1 + 2 * I} : Set ℂ) ∧
    ∃ Tabc Tabd Tacd Tbcd : Affine.Triangle ℝ ℂ,
      (Tabc.points = ![0, -I, 2 - 2 * I] ∧ Tabd.points = ![0, -I, -1 + 2 * I] ∧
        Tacd.points = ![0, 2 - 2 * I, -1 + 2 * I] ∧ Tbcd.points = ![-I, 2 - 2 * I, -1 + 2 * I]) ∧
      (-1 + 2 * I : ℂ) ≠ Tabc.orthocenter ∧
      ((1 - I : ℂ) ∈ Tabc.ninePointCircle ∧ (1 - I : ℂ) ∈ Tabd.ninePointCircle ∧
        (1 - I : ℂ) ∈ Tacd.ninePointCircle ∧ (1 - I : ℂ) ∈ Tbcd.ninePointCircle) ∧
      Tabc.ninePointCircle ≠ Tabd.ninePointCircle ∧ Tabc.ninePointCircle ≠ Tacd.ninePointCircle ∧
      Tabc.ninePointCircle ≠ Tbcd.ninePointCircle ∧ Tabd.ninePointCircle ≠ Tacd.ninePointCircle ∧
      Tabd.ninePointCircle ≠ Tbcd.ninePointCircle ∧ Tacd.ninePointCircle ≠ Tbcd.ninePointCircle := by
  obtain ⟨n1, n2, n3, n4, T1, T2, T3, T4, E, -, hne, hP, c1, c2, c3, c4, -⟩ := l14wbQ_master
  refine ⟨n1, n2, n3, n4, T1, T2, T3, T4, E, hne, hP, ?_⟩
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · have := congrArg EuclideanGeometry.Sphere.center h
    simp only [c1, c2, c3, c4] at this
    norm_num [Complex.ext_iff] at this

/-- Witness for `l14_poncelet_on_pedal_d`: hypotheses hold (with `¬ Cospherical {a,b,c,d}`) and the
three feet and the common point `1 - i` are four pairwise distinct points. -/
theorem l14w_poncelet_on_pedal_d :
    ¬ EuclideanGeometry.Cospherical ({0, -I, 2 - 2 * I, -1 + 2 * I} : Set ℂ) ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, (0 : ℂ), -I] (-1 + 2 * I) : ℂ) = 2 * I ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, -I, 2 - 2 * I] (-1 + 2 * I) : ℂ) = -2 ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, 2 - 2 * I, (0 : ℂ)] (-1 + 2 * I) : ℂ) =
      -3/2 + 3/2 * I ∧
    (2 * I : ℂ) ≠ -2 ∧ (2 * I : ℂ) ≠ -3/2 + 3/2 * I ∧ (2 * I : ℂ) ≠ 1 - I ∧
    (-2 : ℂ) ≠ -3/2 + 3/2 * I ∧ (-2 : ℂ) ≠ 1 - I ∧ (-3/2 + 3/2 * I : ℂ) ≠ 1 - I := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc, -, -, -, -, -, -, f1, f2, f3, -⟩ :=
    l14wbQ_master
  exact ⟨hc, f1, f2, f3, by norm_num [Complex.ext_iff]⟩

/-- Witness for `l14_poncelet_on_pedal_c`. -/
theorem l14w_poncelet_on_pedal_c :
    ¬ EuclideanGeometry.Cospherical ({0, -I, 2 - 2 * I, -1 + 2 * I} : Set ℂ) ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, (0 : ℂ), -I] (2 - 2 * I) : ℂ) = -2 * I ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, -I, -1 + 2 * I] (2 - 2 * I) : ℂ) =
      1/2 - 5/2 * I ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, -1 + 2 * I, (0 : ℂ)] (2 - 2 * I) : ℂ) =
      6/5 - 12/5 * I ∧
    (-2 * I : ℂ) ≠ 1/2 - 5/2 * I ∧ (-2 * I : ℂ) ≠ 6/5 - 12/5 * I ∧ (-2 * I : ℂ) ≠ 1 - I ∧
    (1/2 - 5/2 * I : ℂ) ≠ 6/5 - 12/5 * I ∧ (1/2 - 5/2 * I : ℂ) ≠ 1 - I ∧
    (6/5 - 12/5 * I : ℂ) ≠ 1 - I := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc, -, -, -, -, -, -, -, -, -, f1, f2,
    f3, -⟩ := l14wbQ_master
  exact ⟨hc, f1, f2, f3, by norm_num [Complex.ext_iff]⟩

/-- Witness for `l14_poncelet_on_pedal_b`. -/
theorem l14w_poncelet_on_pedal_b :
    ¬ EuclideanGeometry.Cospherical ({0, -I, 2 - 2 * I, -1 + 2 * I} : Set ℂ) ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, (0 : ℂ), 2 - 2 * I] (-I) : ℂ) =
      1/2 - 1/2 * I ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, 2 - 2 * I, -1 + 2 * I] (-I) : ℂ) =
      4/5 - 2/5 * I ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, -1 + 2 * I, (0 : ℂ)] (-I) : ℂ) =
      2/5 - 4/5 * I ∧
    (1/2 - 1/2 * I : ℂ) ≠ 4/5 - 2/5 * I ∧ (1/2 - 1/2 * I : ℂ) ≠ 2/5 - 4/5 * I ∧
    (1/2 - 1/2 * I : ℂ) ≠ 1 - I ∧ (4/5 - 2/5 * I : ℂ) ≠ 2/5 - 4/5 * I ∧
    (4/5 - 2/5 * I : ℂ) ≠ 1 - I ∧ (2/5 - 4/5 * I : ℂ) ≠ 1 - I := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc, -, -, -, -, -, -, -, -, -, -, -, -,
    f1, f2, f3, -⟩ := l14wbQ_master
  exact ⟨hc, f1, f2, f3, by norm_num [Complex.ext_iff]⟩

/-- Witness for `l14_poncelet_on_pedal_a`. -/
theorem l14w_poncelet_on_pedal_a :
    ¬ EuclideanGeometry.Cospherical ({0, -I, 2 - 2 * I, -1 + 2 * I} : Set ℂ) ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, -I, 2 - 2 * I] (0 : ℂ) : ℂ) = -2/5 - 4/5 * I ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, 2 - 2 * I, -1 + 2 * I] (0 : ℂ) : ℂ) =
      8/25 + 6/25 * I ∧
    (EuclideanGeometry.orthogonalProjection line[ℝ, -1 + 2 * I, -I] (0 : ℂ) : ℂ) =
      -3/10 - 1/10 * I ∧
    (-2/5 - 4/5 * I : ℂ) ≠ 8/25 + 6/25 * I ∧ (-2/5 - 4/5 * I : ℂ) ≠ -3/10 - 1/10 * I ∧
    (-2/5 - 4/5 * I : ℂ) ≠ 1 - I ∧ (8/25 + 6/25 * I : ℂ) ≠ -3/10 - 1/10 * I ∧
    (8/25 + 6/25 * I : ℂ) ≠ 1 - I ∧ (-3/10 - 1/10 * I : ℂ) ≠ 1 - I := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, f1, f2, f3⟩ := l14wbQ_master
  exact ⟨hc, f1, f2, f3, by norm_num [Complex.ext_iff]⟩

/-- Witness for `l14_poncelet_on_diagonal_circle`: opposite sides are not parallel, the explicit
diagonal points lie on the right lines, and they and `1 - i` are pairwise distinct. -/
theorem l14w_poncelet_on_diagonal_circle :
    ¬ (line[ℝ, (0 : ℂ), -I]).Parallel (line[ℝ, 2 - 2 * I, -1 + 2 * I]) ∧
    ¬ (line[ℝ, (0 : ℂ), 2 - 2 * I]).Parallel (line[ℝ, -I, -1 + 2 * I]) ∧
    ¬ (line[ℝ, (0 : ℂ), -1 + 2 * I]).Parallel (line[ℝ, -I, 2 - 2 * I]) ∧
    ((2/3 * I : ℂ) ∈ line[ℝ, (0 : ℂ), -I] ∧ (2/3 * I : ℂ) ∈ line[ℝ, 2 - 2 * I, -1 + 2 * I]) ∧
    ((-1/2 + 1/2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), 2 - 2 * I] ∧
      (-1/2 + 1/2 * I : ℂ) ∈ line[ℝ, -I, -1 + 2 * I]) ∧
    ((2/3 - 4/3 * I : ℂ) ∈ line[ℝ, (0 : ℂ), -1 + 2 * I] ∧
      (2/3 - 4/3 * I : ℂ) ∈ line[ℝ, -I, 2 - 2 * I]) ∧
    (2/3 * I : ℂ) ≠ -1/2 + 1/2 * I ∧ (2/3 * I : ℂ) ≠ 2/3 - 4/3 * I ∧ (2/3 * I : ℂ) ≠ 1 - I ∧
    (-1/2 + 1/2 * I : ℂ) ≠ 2/3 - 4/3 * I ∧ (-1/2 + 1/2 * I : ℂ) ≠ 1 - I ∧
    (2/3 - 4/3 * I : ℂ) ≠ 1 - I := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p1, p2, p3, x1, x2, x3, -⟩ :=
    l14wbQ_master
  exact ⟨p1, p2, p3, x1, x2, x3, by norm_num [Complex.ext_iff]⟩

/-- Witness for the orthocentric theorems (`l14_orthocentric_ninePointCircle_eq` and the orthocentric
direction of `l14_ponDen_eq_zero_iff`): the paper's example `0, 4, 1 + 2i, 1 + 3i/2`. No three
points are collinear, `d` is the Mathlib orthocentre of `abc`, the four nine-point circles coincide
and the two distinct points `2` and `1/2 + i` lie on all four, so the common point is not unique. -/
theorem l14w_orthocentric :
    ¬ Collinear ℝ ({0, 4, 1 + 2 * I} : Set ℂ) ∧ ¬ Collinear ℝ ({0, 4, 1 + 3/2 * I} : Set ℂ) ∧
    ¬ Collinear ℝ ({0, 1 + 2 * I, 1 + 3/2 * I} : Set ℂ) ∧
    ¬ Collinear ℝ ({4, 1 + 2 * I, 1 + 3/2 * I} : Set ℂ) ∧
    ∃ Tabc Tabd Tacd Tbcd : Affine.Triangle ℝ ℂ,
      (Tabc.points = ![0, 4, 1 + 2 * I] ∧ Tabd.points = ![0, 4, 1 + 3/2 * I] ∧
        Tacd.points = ![0, 1 + 2 * I, 1 + 3/2 * I] ∧ Tbcd.points = ![4, 1 + 2 * I, 1 + 3/2 * I]) ∧
      (1 + 3/2 * I : ℂ) = Tabc.orthocenter ∧
      (Tabd.ninePointCircle = Tabc.ninePointCircle ∧ Tacd.ninePointCircle = Tabc.ninePointCircle ∧
        Tbcd.ninePointCircle = Tabc.ninePointCircle) ∧
      ((2 : ℂ) ∈ Tabc.ninePointCircle ∧ (2 : ℂ) ∈ Tabd.ninePointCircle ∧
        (2 : ℂ) ∈ Tacd.ninePointCircle ∧ (2 : ℂ) ∈ Tbcd.ninePointCircle) ∧
      ((1/2 + I : ℂ) ∈ Tabc.ninePointCircle ∧ (1/2 + I : ℂ) ∈ Tabd.ninePointCircle ∧
        (1/2 + I : ℂ) ∈ Tacd.ninePointCircle ∧ (1/2 + I : ℂ) ∈ Tbcd.ninePointCircle) ∧
      (2 : ℂ) ≠ 1/2 + I ∧
      ¬ ∃! P : ℂ, P ∈ Tabc.ninePointCircle ∧ P ∈ Tabd.ninePointCircle ∧
        P ∈ Tacd.ninePointCircle ∧ P ∈ Tbcd.ninePointCircle := by
  have n1 : ¬ Collinear ℝ ({0, 4, 1 + 2 * I} : Set ℂ) := l14b_ncol (by norm_num [cr])
  have n2 : ¬ Collinear ℝ ({0, 4, 1 + 3/2 * I} : Set ℂ) := l14b_ncol (by norm_num [cr])
  have n3 : ¬ Collinear ℝ ({0, 1 + 2 * I, 1 + 3/2 * I} : Set ℂ) := l14b_ncol (by norm_num [cr])
  have n4 : ¬ Collinear ℝ ({4, 1 + 2 * I, 1 + 3/2 * I} : Set ℂ) := l14b_ncol (by norm_num [cr])
  refine ⟨n1, n2, n3, n4, tri n1, tri n2, tri n3, tri n4, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  have ho : (1 + 3/2 * I : ℂ) = (tri n1).orthocenter := by
    rw [l14b_orthocenter rfl n1]
    norm_num [ortho, circ, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  obtain ⟨e2, e3, e4⟩ := l14_orthocentric_ninePointCircle_eq n1 n2 n3 n4 (Tabc := tri n1)
    (Tabd := tri n2) (Tacd := tri n3) (Tbcd := tri n4) rfl rfl rfl rfl ho
  have m1 : (2 : ℂ) ∈ (tri n1).ninePointCircle := by
    rw [l14b_mem_npc rfl n1]
    norm_num [npc, circ, Complex.dist_eq, Complex.ext_iff, Complex.normSq_apply, Complex.div_re,
      Complex.div_im]
  have m2 : (1/2 + I : ℂ) ∈ (tri n1).ninePointCircle := by
    rw [l14b_mem_npc rfl n1]
    have e : npc 0 4 (1 + 2 * I) = 3/2 + 7/8 * I := by
      norm_num [npc, circ, Complex.ext_iff, Complex.normSq_apply, Complex.div_re, Complex.div_im]
    rw [e, Complex.dist_eq, Complex.dist_eq, Complex.norm_def, Complex.norm_def]
    norm_num [Complex.normSq_apply]
  have hne : (2 : ℂ) ≠ 1/2 + I := by norm_num [Complex.ext_iff]
  refine ⟨ho, ⟨e2, e3, e4⟩, ⟨m1, by rw [e2]; exact m1, by rw [e3]; exact m1, by rw [e4]; exact m1⟩,
    ⟨m2, by rw [e2]; exact m2, by rw [e3]; exact m2, by rw [e4]; exact m2⟩, hne, ?_⟩
  rw [l14_ponDen_eq_zero_iff n1 n2 n3 n4 rfl rfl rfl rfl]
  exact fun h => h ho

end QuadMiquel
