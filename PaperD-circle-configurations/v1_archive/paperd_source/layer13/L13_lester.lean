import Lester

/-! L13 comparer scratch: blind_8 vs `Lester.lester`.
Repo definitions unfolded: `Lester.ω`, `Lester.Ccw`, `Lester.apexOut`, `Lester.apexIn`,
`Lester.IsFermatOuter`, `Lester.IsFermatInner`, `Lester.ninePointCenter`.
Repo bridge lemma used: `Lester.bridge_ninePointCenter` (ninePointCenter = Mathlib's centre). -/

open Affine EuclideanGeometry

abbrev BlindPlane := EuclideanSpace ℝ (Fin 2)

/-- verbatim from the blind file -/
def BlindApex (outward : Bool) (A B C D : BlindPlane) : Prop :=
  dist D B = dist B C ∧ dist D C = dist B C ∧
    (if outward then (line[ℝ, B, C]).SOppSide A D else (line[ℝ, B, C]).SSameSide A D)

/-- verbatim from the blind file -/
def BlindIsFermat (t : Affine.Triangle ℝ BlindPlane) (outward : Bool) (F : BlindPlane) : Prop :=
  ∃ Da Db Dc : BlindPlane,
    BlindApex outward (t.points 0) (t.points 1) (t.points 2) Da ∧
    BlindApex outward (t.points 1) (t.points 2) (t.points 0) Db ∧
    BlindApex outward (t.points 2) (t.points 0) (t.points 1) Dc ∧
    F ∈ line[ℝ, t.points 0, Da] ∧ F ∈ line[ℝ, t.points 1, Db] ∧ F ∈ line[ℝ, t.points 2, Dc]

/-- blind_8 verbatim. -/
def blind8_stmt : Prop :=
  ∀ (t : Affine.Triangle ℝ BlindPlane)
    (hscalene : dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2) ∧
      dist (t.points 1) (t.points 2) ≠ dist (t.points 2) (t.points 0) ∧
      dist (t.points 2) (t.points 0) ≠ dist (t.points 0) (t.points 1))
    (F₁ F₂ : BlindPlane) (hF₁ : BlindIsFermat t true F₁) (hF₂ : BlindIsFermat t false F₂),
    Concyclic ({t.circumcenter, t.ninePointCircle.center, F₁, F₂} : Set BlindPlane)

/-! ### The same apex notion, stated in `ℂ` -/

def CApex (outward : Bool) (A B C D : ℂ) : Prop :=
  dist D B = dist B C ∧ dist D C = dist B C ∧
    (if outward then (line[ℝ, B, C]).SOppSide A D else (line[ℝ, B, C]).SSameSide A D)

/-- signed distance (times `|C - B|`) of `z` from the line `BC` -/
def sig (B C z : ℂ) : ℝ := ((starRingEnd ℂ) (C - B) * (z - B)).im

lemma decomp_aux (u w : ℂ) (hw : w ≠ 0) :
    u - (((starRingEnd ℂ) w * u).re / Complex.normSq w) • w =
      (((starRingEnd ℂ) w * u).im / Complex.normSq w) • (Complex.I * w) := by
  have hn : Complex.normSq w ≠ 0 := (Complex.normSq_pos.mpr hw).ne'
  obtain ⟨u1, u2⟩ := u
  obtain ⟨w1, w2⟩ := w
  rw [Complex.normSq_mk] at hn ⊢
  have hn2 : w1 ^ 2 + w2 ^ 2 ≠ 0 := by rw [sq, sq]; exact hn
  have hn3 : w2 ^ 2 + w1 ^ 2 ≠ 0 := by rw [add_comm]; exact hn2
  apply Complex.ext <;>
  · simp only [Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, smul_eq_mul]
    field_simp
    ring

lemma decomp (B C z : ℂ) (hBC : B ≠ C) :
    z -ᵥ (AffineMap.lineMap B C (((starRingEnd ℂ) (C - B) * (z - B)).re / Complex.normSq (C - B)))
      = (sig B C z / Complex.normSq (C - B)) • (Complex.I * (C - B)) := by
  rw [AffineMap.lineMap_apply, sig, ← decomp_aux (z - B) (C - B) (sub_ne_zero.mpr hBC.symm)]
  simp only [vsub_eq_sub, vadd_eq_add]
  abel

lemma lineMap_mem (B C : ℂ) (r : ℝ) : AffineMap.lineMap B C r ∈ line[ℝ, B, C] :=
  AffineMap.lineMap_mem_affineSpan_pair _ _ _

lemma sig_of_mem {B C z : ℂ} (h : z ∈ line[ℝ, B, C]) : sig B C z = 0 := by
  obtain ⟨r, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).mp h
  rw [AffineMap.lineMap_apply]
  simp only [sig, vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

lemma not_mem_of_sig {B C z : ℂ} (h : sig B C z ≠ 0) : z ∉ line[ℝ, B, C] :=
  fun hm => h (sig_of_mem hm)

lemma opp_of_sig {B C x y : ℂ} (hBC : B ≠ C) (h : sig B C x * sig B C y < 0) :
    (line[ℝ, B, C]).SOppSide x y := by
  have hw : 0 < Complex.normSq (C - B) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hBC.symm)
  refine AffineSubspace.sOppSide_of_vsub_eq_smul (lineMap_mem B C _) (lineMap_mem B C _)
    (decomp B C x hBC) (decomp B C y hBC) ?_
    (not_mem_of_sig (by rintro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h))
    (not_mem_of_sig (by rintro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h))
  rw [div_mul_div_comm]
  exact (div_neg_of_neg_of_pos h (by positivity)).le

lemma same_of_sig {B C x y : ℂ} (hBC : B ≠ C) (h : 0 < sig B C x * sig B C y) :
    (line[ℝ, B, C]).SSameSide x y := by
  have hw : 0 < Complex.normSq (C - B) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hBC.symm)
  refine AffineSubspace.sSameSide_of_vsub_eq_smul (lineMap_mem B C _) (lineMap_mem B C _)
    (decomp B C x hBC) (decomp B C y hBC) ?_
    (not_mem_of_sig (by rintro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h))
    (not_mem_of_sig (by rintro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h))
  rw [div_mul_div_comm]
  exact (div_pos h (by positivity)).le

lemma sig_ne_zero {A B C : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) (hBC : B ≠ C) :
    sig B C A ≠ 0 := by
  intro h0
  apply h
  apply collinear_insert_of_mem_affineSpan_pair
  have := decomp B C A hBC
  rw [h0, zero_div, zero_smul, vsub_eq_zero_iff_eq] at this
  rw [this]; exact lineMap_mem B C _

lemma ccw_iff (A B C : ℂ) : Lester.Ccw A B C ↔ 0 < sig B C A := by
  unfold Lester.Ccw sig
  constructor <;> intro h <;>
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
      Complex.sub_im] at h ⊢
    linarith

lemma sig_ω (B C : ℂ) : sig B C (B + (C - B) * Lester.ω) =
    Complex.normSq (C - B) * (Real.sqrt 3 / 2) := by
  simp only [sig, add_sub_cancel_left, Lester.ω, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

lemma sig_conj_ω (B C : ℂ) : sig B C (B + (C - B) * (starRingEnd ℂ) Lester.ω) =
    -(Complex.normSq (C - B) * (Real.sqrt 3 / 2)) := by
  simp only [sig, add_sub_cancel_left, Lester.ω, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- the only two equilateral apices on `BC` -/
lemma apex_cases {B C D : ℂ} (hBC : B ≠ C) (h1 : dist D B = dist B C) (h2 : dist D C = dist B C) :
    D = B + (C - B) * Lester.ω ∨ D = B + (C - B) * (starRingEnd ℂ) Lester.ω := by
  have e1 := congrArg (· ^ 2) h1
  have e2 := congrArg (· ^ 2) h2
  simp only [Complex.dist_eq_re_im] at e1 e2
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at e1 e2
  set p1 := D.re - B.re; set p2 := D.im - B.im
  set w1 := C.re - B.re; set w2 := C.im - B.im
  have hw : w1 ^ 2 + w2 ^ 2 ≠ 0 := by
    have : C - B ≠ 0 := sub_ne_zero.mpr hBC.symm
    rw [← Complex.normSq_pos, Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.sub_im] at this
    intro h0; simp only [w1, w2] at h0; nlinarith
  have eB : p1 ^ 2 + p2 ^ 2 = w1 ^ 2 + w2 ^ 2 := by
    simp only [p1, p2, w1, w2]; nlinarith
  have eC : (p1 - w1) ^ 2 + (p2 - w2) ^ 2 = w1 ^ 2 + w2 ^ 2 := by
    simp only [p1, p2, w1, w2]; nlinarith
  have dot : p1 * w1 + p2 * w2 = (w1 ^ 2 + w2 ^ 2) / 2 := by linarith
  set q := w1 * p2 - w2 * p1
  have lag : q ^ 2 = (w1 ^ 2 + w2 ^ 2) ^ 2 * (3 / 4) := by
    have : (p1 * w1 + p2 * w2) ^ 2 + q ^ 2 = (w1 ^ 2 + w2 ^ 2) * (p1 ^ 2 + p2 ^ 2) := by
      simp only [q]; ring
    rw [dot, eB] at this; linarith
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : q = (w1 ^ 2 + w2 ^ 2) * (Real.sqrt 3 / 2) ∨ q = -((w1 ^ 2 + w2 ^ 2) * (Real.sqrt 3 / 2)) := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [lag]; ring_nf; rw [hs]; ring
  -- recover `p` from its dot and cross products with `w`
  have r1 : p1 * (w1 ^ 2 + w2 ^ 2) = w1 * (p1 * w1 + p2 * w2) - w2 * q := by simp only [q]; ring
  have r2 : p2 * (w1 ^ 2 + w2 ^ 2) = w2 * (p1 * w1 + p2 * w2) + w1 * q := by simp only [q]; ring
  rcases hq with hq | hq
  · left
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Lester.ω]
      have : p1 = w1 * (1 / 2) - w2 * (Real.sqrt 3 / 2) := by
        apply mul_right_cancel₀ hw; rw [r1, dot, hq]; ring
      simp only [p1, w1, w2] at this; linarith
    · simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Lester.ω]
      have : p2 = w2 * (1 / 2) + w1 * (Real.sqrt 3 / 2) := by
        apply mul_right_cancel₀ hw; rw [r2, dot, hq]; ring
      simp only [p2, w1, w2] at this; linarith
  · right
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Lester.ω,
        Complex.conj_re, Complex.conj_im]
      have : p1 = w1 * (1 / 2) + w2 * (Real.sqrt 3 / 2) := by
        apply mul_right_cancel₀ hw; rw [r1, dot, hq]; ring
      simp only [p1, w1, w2] at this; linarith
    · simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Lester.ω, Complex.conj_re, Complex.conj_im]
      have : p2 = w2 * (1 / 2) - w1 * (Real.sqrt 3 / 2) := by
        apply mul_right_cancel₀ hw; rw [r2, dot, hq]; ring
      simp only [p2, w1, w2] at this; linarith

lemma dist_ω {B C : ℂ} :
    dist (B + (C - B) * Lester.ω) B = dist B C ∧ dist (B + (C - B) * Lester.ω) C = dist B C := by
  have := Lester.bridge_apexIn 0 B C
  have h2 := Lester.bridge_apexOut 0 B C
  unfold Lester.apexIn at this; unfold Lester.apexOut at h2
  by_cases hc : Lester.Ccw 0 B C
  · rw [if_pos hc] at this; exact this
  · rw [if_neg hc] at h2; exact h2

lemma dist_conj_ω {B C : ℂ} :
    dist (B + (C - B) * (starRingEnd ℂ) Lester.ω) B = dist B C ∧
      dist (B + (C - B) * (starRingEnd ℂ) Lester.ω) C = dist B C := by
  have := Lester.bridge_apexIn 0 B C
  have h2 := Lester.bridge_apexOut 0 B C
  unfold Lester.apexIn at this; unfold Lester.apexOut at h2
  by_cases hc : Lester.Ccw 0 B C
  · rw [if_pos hc] at h2; exact h2
  · rw [if_neg hc] at this; exact this

lemma n3 : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity

lemma opp_iff {B C x y : ℂ} (hBC : B ≠ C) (hx : sig B C x ≠ 0) (hy : sig B C y ≠ 0) :
    (line[ℝ, B, C]).SOppSide x y ↔ sig B C x * sig B C y < 0 := by
  constructor
  · intro h
    by_contra hc
    have hp : 0 < sig B C x * sig B C y :=
      lt_of_le_of_ne (not_lt.mp hc) (mul_ne_zero hx hy).symm
    exact (same_of_sig hBC hp).not_sOppSide h
  · exact opp_of_sig hBC

lemma same_iff {B C x y : ℂ} (hBC : B ≠ C) (hx : sig B C x ≠ 0) (hy : sig B C y ≠ 0) :
    (line[ℝ, B, C]).SSameSide x y ↔ 0 < sig B C x * sig B C y := by
  constructor
  · intro h
    by_contra hc
    have hp : sig B C x * sig B C y < 0 :=
      lt_of_le_of_ne (not_lt.mp hc) (mul_ne_zero hx hy)
    exact (opp_of_sig hBC hp).not_sSameSide h
  · exact same_of_sig hBC

/-- The blind apex notion (in `ℂ`) is exactly the repo's explicit apex. -/
lemma capex_iff (o : Bool) {A B C D : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) (hBC : B ≠ C) :
    CApex o A B C D ↔ D = (if o then Lester.apexOut A B C else Lester.apexIn A B C) := by
  have hw : 0 < Complex.normSq (C - B) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hBC.symm)
  have hA := sig_ne_zero h hBC
  have pω := sig_ω B C; have pcω := sig_conj_ω B C
  have k := mul_pos hw n3
  have hω : sig B C (B + (C - B) * Lester.ω) ≠ 0 := by rw [pω]; exact k.ne'
  have hcω : sig B C (B + (C - B) * (starRingEnd ℂ) Lester.ω) ≠ 0 := by
    rw [pcω]; exact (neg_neg_of_pos k).ne
  unfold CApex Lester.apexOut Lester.apexIn
  rw [ccw_iff]
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · have hc : ¬ 0 < sig B C A := not_lt.mpr hneg.le
    simp only [if_neg hc]
    constructor
    · rintro ⟨h1, h2, hs⟩
      rcases apex_cases hBC h1 h2 with rfl | rfl
      · cases o
        · exfalso
          simp only [Bool.false_eq_true, if_false] at hs
          rw [same_iff hBC hA hω, pω] at hs; nlinarith
        · rfl
      · cases o
        · rfl
        · exfalso
          simp only [if_true] at hs
          rw [opp_iff hBC hA hcω, pcω] at hs; nlinarith
    · intro hD
      cases o
      · simp only [Bool.false_eq_true, if_false] at hD ⊢
        subst hD
        exact ⟨dist_conj_ω.1, dist_conj_ω.2, by rw [same_iff hBC hA hcω, pcω]; nlinarith⟩
      · simp only [if_true] at hD ⊢
        subst hD
        exact ⟨dist_ω.1, dist_ω.2, by rw [opp_iff hBC hA hω, pω]; nlinarith⟩
  · simp only [if_pos hpos]
    constructor
    · rintro ⟨h1, h2, hs⟩
      rcases apex_cases hBC h1 h2 with rfl | rfl
      · cases o
        · rfl
        · exfalso
          simp only [if_true] at hs
          rw [opp_iff hBC hA hω, pω] at hs; nlinarith
      · cases o
        · exfalso
          simp only [Bool.false_eq_true, if_false] at hs
          rw [same_iff hBC hA hcω, pcω] at hs; nlinarith
        · rfl
    · intro hD
      cases o
      · simp only [Bool.false_eq_true, if_false] at hD ⊢
        subst hD
        exact ⟨dist_ω.1, dist_ω.2, by rw [same_iff hBC hA hω, pω]; nlinarith⟩
      · simp only [if_true] at hD ⊢
        subst hD
        exact ⟨dist_conj_ω.1, dist_conj_ω.2, by rw [opp_iff hBC hA hcω, pcω]; nlinarith⟩

/-! ### Transport along an affine isometry equivalence -/

section Transport

variable {V P V' P' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [MetricSpace P']
  [NormedAddTorsor V' P']

/-- generic form of `BlindApex` / `CApex` -/
def GApex (outward : Bool) (A B C D : P) : Prop :=
  dist D B = dist B C ∧ dist D C = dist B C ∧
    (if outward then (line[ℝ, B, C]).SOppSide A D else (line[ℝ, B, C]).SSameSide A D)

lemma line_map (e : P ≃ᵃⁱ[ℝ] P') (A D : P) :
    (line[ℝ, A, D]).map (e.toAffineEquiv : P →ᵃ[ℝ] P') = line[ℝ, e A, e D] := by
  rw [AffineSubspace.map_span, Set.image_pair]; rfl

lemma mem_line_map (e : P ≃ᵃⁱ[ℝ] P') (A D F : P) :
    e F ∈ line[ℝ, e A, e D] ↔ F ∈ line[ℝ, A, D] := by
  rw [← line_map]
  exact AffineSubspace.mem_map_iff_mem_of_injective (f := (e.toAffineEquiv : P →ᵃ[ℝ] P'))
    e.injective

lemma gapex_map (e : P ≃ᵃⁱ[ℝ] P') (o : Bool) (A B C D : P) :
    GApex o (e A) (e B) (e C) (e D) ↔ GApex o A B C D := by
  unfold GApex
  simp only [e.dist_map]
  rw [← line_map]
  have h1 := AffineEquiv.sOppSide_map_iff (s := line[ℝ, B, C]) (x := A) (y := D) e.toAffineEquiv
  have h2 := AffineEquiv.sSameSide_map_iff (s := line[ℝ, B, C]) (x := A) (y := D) e.toAffineEquiv
  simp only [AffineIsometryEquiv.coe_toAffineEquiv] at h1 h2
  cases o <;> simp only [Bool.false_eq_true, if_false, if_true, h1, h2]

lemma cospherical_map (e : P ≃ᵃⁱ[ℝ] P') (a b c d : P)
    (h : Cospherical ({e a, e b, e c, e d} : Set P')) : Cospherical ({a, b, c, d} : Set P) := by
  have := e.symm.isometry.cospherical h
  simpa [Set.image_insert_eq] using this

lemma not_collinear_tri (t : Affine.Triangle ℝ P) :
    ¬ Collinear ℝ ({t.points 0, t.points 1, t.points 2} : Set P) := by
  have : t.points = ![t.points 0, t.points 1, t.points 2] := by
    ext i : 1; fin_cases i <;> rfl
  have hi := t.independent
  rw [this] at hi
  exact affineIndependent_iff_not_collinear_set.mp hi

end Transport

attribute [local instance] Complex.finrank_real_complex_fact

/-- the standard identification `BlindPlane ≃ ℂ` -/
noncomputable def eC : BlindPlane ≃ᵃⁱ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm.toAffineIsometryEquiv

lemma not_col_map {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (e : X ≃ᵃⁱ[ℝ] Y) {A B C : X}
    (h : ¬ Collinear ℝ ({A, B, C} : Set X)) :
    ¬ Collinear ℝ ({e A, e B, e C} : Set Y) := by
  rw [← affineIndependent_iff_not_collinear_set] at h ⊢
  have heq : ![e A, e B, e C] = (e.toAffineEquiv.toAffineMap : X → Y) ∘ ![A, B, C] := by
    funext i; fin_cases i <;> rfl
  rw [heq]
  exact h.map' _ e.injective

lemma ne_of_not_col {X : Type*} [AddCommGroup X] [Module ℝ X] {A B C : X}
    (h : ¬ Collinear ℝ ({A, B, C} : Set X)) : B ≠ C := by
  rintro rfl; apply h; simp [collinear_pair]

lemma rot1 {X : Type*} [AddCommGroup X] [Module ℝ X] {A B C : X}
    (h : ¬ Collinear ℝ ({A, B, C} : Set X)) : ¬ Collinear ℝ ({B, C, A} : Set X) := by
  have : ({B, C, A} : Set X) = {A, B, C} := by ext; simp; tauto
  rwa [this]

lemma rot2 {X : Type*} [AddCommGroup X] [Module ℝ X] {A B C : X}
    (h : ¬ Collinear ℝ ({A, B, C} : Set X)) : ¬ Collinear ℝ ({C, A, B} : Set X) :=
  rot1 (rot1 h)

/-- Fermat point condition "with some apices" in `ℂ` is exactly the repo's definition. -/
lemma fermat_C (o : Bool) {A B C F : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) :
    (∃ Da Db Dc : ℂ, GApex o A B C Da ∧ GApex o B C A Db ∧ GApex o C A B Dc ∧
      F ∈ line[ℝ, A, Da] ∧ F ∈ line[ℝ, B, Db] ∧ F ∈ line[ℝ, C, Dc]) ↔
    (if o then Lester.IsFermatOuter A B C F else Lester.IsFermatInner A B C F) := by
  have e1 : ∀ D, GApex o A B C D ↔ _ := fun D => capex_iff o (D := D) h (ne_of_not_col h)
  have e2 : ∀ D, GApex o B C A D ↔ _ := fun D => capex_iff o (D := D) (rot1 h) (ne_of_not_col (rot1 h))
  have e3 : ∀ D, GApex o C A B D ↔ _ := fun D => capex_iff o (D := D) (rot2 h) (ne_of_not_col (rot2 h))
  simp only [e1, e2, e3]
  constructor
  · rintro ⟨_, _, _, rfl, rfl, rfl, h1, h2, h3⟩
    cases o
    · exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, h3⟩
  · intro hF
    cases o
    · exact ⟨_, _, _, rfl, rfl, rfl, hF.1, hF.2.1, hF.2.2⟩
    · exact ⟨_, _, _, rfl, rfl, rfl, hF.1, hF.2.1, hF.2.2⟩

section Transport2

variable {V P V' P' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [MetricSpace P']
  [NormedAddTorsor V' P']

lemma fermat_transport (e : P ≃ᵃⁱ[ℝ] P') (o : Bool) (A B C F : P) :
    (∃ Da Db Dc : P, GApex o A B C Da ∧ GApex o B C A Db ∧ GApex o C A B Dc ∧
      F ∈ line[ℝ, A, Da] ∧ F ∈ line[ℝ, B, Db] ∧ F ∈ line[ℝ, C, Dc]) ↔
    (∃ Da Db Dc : P', GApex o (e A) (e B) (e C) Da ∧ GApex o (e B) (e C) (e A) Db ∧
      GApex o (e C) (e A) (e B) Dc ∧
      e F ∈ line[ℝ, e A, Da] ∧ e F ∈ line[ℝ, e B, Db] ∧ e F ∈ line[ℝ, e C, Dc]) := by
  constructor
  · rintro ⟨Da, Db, Dc, ha, hb, hc, h1, h2, h3⟩
    exact ⟨e Da, e Db, e Dc, (gapex_map e o _ _ _ _).2 ha, (gapex_map e o _ _ _ _).2 hb,
      (gapex_map e o _ _ _ _).2 hc, (mem_line_map e _ _ _).2 h1, (mem_line_map e _ _ _).2 h2,
      (mem_line_map e _ _ _).2 h3⟩
  · rintro ⟨Da, Db, Dc, ha, hb, hc, h1, h2, h3⟩
    have r : ∀ x : P', e (e.symm x) = x := e.apply_symm_apply
    rw [← r Da] at ha h1; rw [← r Db] at hb h2; rw [← r Dc] at hc h3
    exact ⟨e.symm Da, e.symm Db, e.symm Dc, (gapex_map e o _ _ _ _).1 ha,
      (gapex_map e o _ _ _ _).1 hb, (gapex_map e o _ _ _ _).1 hc, (mem_line_map e _ _ _).1 h1,
      (mem_line_map e _ _ _).1 h2, (mem_line_map e _ _ _).1 h3⟩

end Transport2

lemma blindFermat_iff (o : Bool) (t : Affine.Triangle ℝ BlindPlane) (F : BlindPlane) :
    BlindIsFermat t o F ↔
      (if o then Lester.IsFermatOuter else Lester.IsFermatInner)
        (eC (t.points 0)) (eC (t.points 1)) (eC (t.points 2)) (eC F) := by
  have := fermat_transport eC o (t.points 0) (t.points 1) (t.points 2) F
  have h2 := fermat_C o (not_col_map eC (not_collinear_tri t)) (F := eC F)
  unfold BlindIsFermat
  rw [show (∃ Da Db Dc : BlindPlane, BlindApex o (t.points 0) (t.points 1) (t.points 2) Da ∧
      BlindApex o (t.points 1) (t.points 2) (t.points 0) Db ∧
      BlindApex o (t.points 2) (t.points 0) (t.points 1) Dc ∧
      F ∈ line[ℝ, t.points 0, Da] ∧ F ∈ line[ℝ, t.points 1, Db] ∧ F ∈ line[ℝ, t.points 2, Dc]) =
    (∃ Da Db Dc : BlindPlane, GApex o (t.points 0) (t.points 1) (t.points 2) Da ∧
      GApex o (t.points 1) (t.points 2) (t.points 0) Db ∧
      GApex o (t.points 2) (t.points 0) (t.points 1) Dc ∧
      F ∈ line[ℝ, t.points 0, Da] ∧ F ∈ line[ℝ, t.points 1, Db] ∧ F ∈ line[ℝ, t.points 2, Dc])
    from rfl, this, h2]
  cases o <;> rfl

lemma concyclic_of_cosph {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [Fact (Module.finrank ℝ X = 2)] {s : Set X} (h : Cospherical s) : Concyclic s :=
  ⟨h, coplanar_of_fact_finrank_eq_two s⟩

instance : Fact (Module.finrank ℝ BlindPlane = 2) := ⟨by simp⟩

/-- type of `Lester.lester`, verbatim -/
def real8_stmt : Prop :=
  ∀ (t : Affine.Triangle ℝ ℂ)
    (h01 : dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2))
    (h12 : dist (t.points 1) (t.points 2) ≠ dist (t.points 2) (t.points 0))
    (h20 : dist (t.points 2) (t.points 0) ≠ dist (t.points 0) (t.points 1))
    (F₁ F₂ : ℂ)
    (h₁ : Lester.IsFermatOuter (t.points 0) (t.points 1) (t.points 2) F₁)
    (h₂ : Lester.IsFermatInner (t.points 0) (t.points 1) (t.points 2) F₂),
    Concyclic ({Lester.ninePointCenter t, t.circumcenter, F₁, F₂} : Set ℂ)

example : real8_stmt := @Lester.lester  -- type check only

theorem rb_8 : real8_stmt → blind8_stmt := by
  intro h t hsc F₁ F₂ hF₁ hF₂
  let f : BlindPlane →ᵃⁱ[ℝ] ℂ := eC.toAffineIsometry
  let tC := t.map f.toAffineMap f.injective
  have hp : ∀ i, tC.points i = eC (t.points i) := fun i => rfl
  have hcc : tC.circumcenter = eC t.circumcenter := Affine.Simplex.circumcenter_map t f
  have hnp : Lester.ninePointCenter tC = eC t.ninePointCircle.center := by
    rw [Lester.bridge_ninePointCenter, Affine.Simplex.ninePointCircle_map]; rfl
  have := h tC (by simp only [hp, eC.dist_map]; exact hsc.1)
    (by simp only [hp, eC.dist_map]; exact hsc.2.1)
    (by simp only [hp, eC.dist_map]; exact hsc.2.2) (eC F₁) (eC F₂)
    (by simp only [hp]; simpa using (blindFermat_iff true t F₁).1 hF₁)
    (by simp only [hp]; simpa using (blindFermat_iff false t F₂).1 hF₂)
  rw [hcc, hnp, Set.insert_comm] at this
  exact concyclic_of_cosph (cospherical_map eC _ _ _ _ this.1)

theorem br_8 : blind8_stmt → real8_stmt := by
  intro h t h01 h12 h20 F₁ F₂ h₁ h₂
  let f : ℂ →ᵃⁱ[ℝ] BlindPlane := eC.symm.toAffineIsometry
  let tB := t.map f.toAffineMap f.injective
  have hp : ∀ i, tB.points i = eC.symm (t.points i) := fun i => rfl
  have hcc : tB.circumcenter = eC.symm t.circumcenter := Affine.Simplex.circumcenter_map t f
  have hnp : tB.ninePointCircle.center = eC.symm (Lester.ninePointCenter t) := by
    rw [Lester.bridge_ninePointCenter, Affine.Simplex.ninePointCircle_map]; rfl
  have r : ∀ x : ℂ, eC (eC.symm x) = x := eC.apply_symm_apply
  have := h tB (by simp only [hp, eC.symm.dist_map]; exact ⟨h01, h12, h20⟩)
    (eC.symm F₁) (eC.symm F₂)
    ((blindFermat_iff true tB _).2 (by simp only [hp, r]; simpa using h₁))
    ((blindFermat_iff false tB _).2 (by simp only [hp, r]; simpa using h₂))
  rw [hcc, hnp, Set.insert_comm] at this
  exact concyclic_of_cosph (cospherical_map eC.symm _ _ _ _ this.1)
