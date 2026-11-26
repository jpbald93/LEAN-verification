import scratch.BlindCompareFull

/-!
# Bridge layer: writer-side (blind) predicates ↔ library predicates

Layer 13 (`L13_FULL_COMPARE.md`) closes the writer ⇒ real direction for all seven rows and leaves
the real ⇒ writer direction open, because the writer's predicates are independently defined. This
file supplies the missing bridges.

Targets, in dependency order:

* `mem_sphere_iff_onCircleM` — the blind circle `Metric.sphere c ‖c‖` is `Clifford.OnCircleM c`;
* `blindTransversal_iff` — `BlindTransversal c d ↔ Clifford.Transversal c d`;
* `BlindSecond_eq` — under transversality the choice-based `BlindSecond` is `Clifford.second`;
* `genPosN_blindGenPos` — library general position implies the writer's;
* `isGCircleS_of_blindIsGCircle` — the writer's generalized circle is a library `IsGCircleS`;
* `isGCircleS_iff_blindIsGCircle` — the converse, modulo the degenerate radius-zero circle;
* `blindOfChainS` — the recursive transport `ChainS n c X → BlindClifford n c X` under `GenPosN`;
* `N1_RB`, `N7_RB`, `N6_RB` — the three rows this closes.

Rows 2 and 3 are **not** bridge problems: their gap is universal incidence over every certified
singleton versus the canonical `EptInf` point, which no definitional bridge can supply (and general
`UniqEven` is false). Rows 4 and 5 additionally need the plane/sphere encoding translation and are
phase 2 of this file.
-/

open OnePoint

namespace PaperLBlind

open Complex ComplexConjugate

noncomputable section

/-! ## 1. The circle -/

/-- The writer's circle through `M = 0` with centre `c` is the library's `OnCircleM c`. -/
theorem mem_sphere_iff_onCircleM (c z : ℂ) :
    z ∈ Metric.sphere c ‖c‖ ↔ Clifford.OnCircleM c z := by
  rw [Metric.mem_sphere, Complex.dist_eq]
  constructor
  · intro h
    have hsq : ‖z - c‖ ^ 2 = ‖c‖ ^ 2 := by rw [h]
    rw [Complex.sq_norm, Complex.sq_norm] at hsq
    simp [Complex.normSq_apply] at hsq
    rw [Clifford.OnCircleM]
    nlinarith [hsq]
  · intro h
    have hsq : ‖z - c‖ ^ 2 = ‖c‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      simp [Complex.normSq_apply]
      rw [Clifford.OnCircleM] at h
      nlinarith [h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with heq | heq
    · exact heq
    · have hz := norm_nonneg (z - c)
      have hc := norm_nonneg c
      nlinarith

lemma point_eq_second {c d z : ℂ} (hcd : c ≠ d) (hz0 : z ≠ 0)
    (hz1 : z ∈ BlindCircle c) (hz2 : z ∈ BlindCircle d) : z = Clifford.second c d := by
  have h1 : z * conj z = conj c * z + c * conj z :=
    (Clifford.onCircleM_iff c z).1 (mem_sphere_iff_onCircleM c z |>.1 (by simpa [BlindCircle] using hz1))
  have h2 : z * conj z = conj d * z + d * conj z :=
    (Clifford.onCircleM_iff d z).1 (mem_sphere_iff_onCircleM d z |>.1 (by simpa [BlindCircle] using hz2))
  have hE : (conj c - conj d) * z + (c - d) * conj z = 0 := by
    linear_combination h2 - h1
  have hA : conj c - conj d ≠ 0 := Clifford.conj_sub_ne_zero hcd
  have hE' : (c - d) * conj z = -((conj c - conj d) * z) := by
    linear_combination hE
  have h1B' : z * ((c - d) * conj z) = (c - d) * (conj c * z) + c * ((c - d) * conj z) := by
    have h1B : (c - d) * (z * conj z) = (c - d) * (conj c * z + c * conj z) := by rw [h1]
    linear_combination h1B
  rw [hE'] at h1B'
  have hzfac : z * ((conj c - conj d) * z + (c - d) * conj c - c * (conj c - conj d)) = 0 := by
    linear_combination -h1B'
  have hkey0 : (conj c - conj d) * z + (c - d) * conj c - c * (conj c - conj d) = 0 :=
    (mul_eq_zero.mp hzfac).resolve_left hz0
  have hzkey : (conj c - conj d) * z = conj c * d - c * conj d := by
    linear_combination hkey0
  rw [eq_comm, Clifford.second]
  rw [div_eq_iff hA]
  simpa [mul_comm] using hzkey.symm

lemma blindTransversal_ne {c d : ℂ} (h : BlindTransversal c d) : c ≠ d := by
  rcases h.exists with ⟨z, hz0, hzc, hzd⟩
  intro hcd
  subst d
  by_cases hc0 : c = 0
  · subst c
    rw [BlindCircle, Metric.mem_sphere, dist_zero_right] at hzc
    rw [norm_zero] at hzc
    exact hz0 (norm_eq_zero.mp hzc)
  · have hI1 : (1 + Complex.I : ℂ) ≠ 0 := by
      intro hh
      have := congrArg Complex.im hh
      norm_num at this
    have hI2 : (1 - Complex.I : ℂ) ≠ 0 := by
      intro hh
      have := congrArg Complex.im hh
      norm_num at this
    have hp0 : c + c * Complex.I ≠ 0 := by
      rw [show c + c * Complex.I = c * (1 + Complex.I) by ring]
      exact mul_ne_zero hc0 hI1
    have hq0 : c - c * Complex.I ≠ 0 := by
      rw [show c - c * Complex.I = c * (1 - Complex.I) by ring]
      exact mul_ne_zero hc0 hI2
    have hp_mem : c + c * Complex.I ∈ BlindCircle c := by
      rw [BlindCircle, Metric.mem_sphere, Complex.dist_eq]
      rw [show c + c * Complex.I - c = c * Complex.I by ring]
      simp
    have hq_mem : c - c * Complex.I ∈ BlindCircle c := by
      rw [BlindCircle, Metric.mem_sphere, Complex.dist_eq]
      rw [show c - c * Complex.I - c = -(c * Complex.I) by ring]
      simp
    have hpq : c + c * Complex.I ≠ c - c * Complex.I := by
      intro he
      have he' : (2 : ℂ) * c * Complex.I = 0 := by linear_combination he
      exact (mul_ne_zero (mul_ne_zero (by norm_num) hc0) (by norm_num : Complex.I ≠ 0)) he'
    exact hpq (h.unique ⟨hp0, hp_mem, hp_mem⟩ ⟨hq0, hq_mem, hq_mem⟩)

/-! ## 2. Transversality and the second intersection -/

/-- The writer's unique-nonzero-intersection condition is the library's `Transversal`. -/
theorem blindTransversal_iff {c d : ℂ} :
    BlindTransversal c d ↔ Clifford.Transversal c d := by
  constructor
  · intro h
    rcases h.exists with ⟨z, hz0, hzc, hzd⟩
    have hcd := blindTransversal_ne h
    have hzkey := point_eq_second hcd hz0 hzc hzd
    have hsec0 : Clifford.second c d ≠ 0 := by simpa [hzkey] using hz0
    intro htr
    apply hsec0
    rw [Clifford.second, sub_eq_zero.mpr htr, zero_div]
  · intro h
    refine ⟨Clifford.second c d, ?_, ?_⟩
    · exact ⟨Clifford.second_ne_zero h,
        by rw [BlindCircle]; exact mem_sphere_iff_onCircleM c (Clifford.second c d) |>.2 (Clifford.second_onCircleM_left h.ne),
        by rw [BlindCircle]; exact mem_sphere_iff_onCircleM d (Clifford.second c d) |>.2 (Clifford.second_onCircleM_right h.ne)⟩
    · intro z hz
      exact point_eq_second h.ne hz.1 hz.2.1 hz.2.2

/-- Under transversality the chosen blind second intersection is `Clifford.second`. -/
theorem BlindSecond_eq {c d : ℂ} (h : Clifford.Transversal c d) :
    BlindSecond c d = Clifford.second c d := by
  classical
  have hbt : BlindTransversal c d := blindTransversal_iff.2 h
  rw [BlindSecond, dif_pos hbt]
  have hspec := Classical.choose_spec hbt.exists
  have hsecond : Clifford.second c d ≠ 0 ∧ (Clifford.second c d) ∈ BlindCircle c ∧
      (Clifford.second c d) ∈ BlindCircle d := ⟨Clifford.second_ne_zero h,
    by rw [BlindCircle]; exact mem_sphere_iff_onCircleM c (Clifford.second c d) |>.2 (Clifford.second_onCircleM_left h.ne),
    by rw [BlindCircle]; exact mem_sphere_iff_onCircleM d (Clifford.second c d) |>.2 (Clifford.second_onCircleM_right h.ne)⟩
  exact hbt.unique hspec hsecond

/-! ## 3. General position -/

lemma triP_eq_zero_of_common {a b c z : ℂ} (hz0 : z ≠ 0)
    (ha : Clifford.OnCircleM a z) (hb : Clifford.OnCircleM b z) (hc : Clifford.OnCircleM c z) :
    Clifford.triP a b c (conj a) (conj b) (conj c) = 0 := by
  have hza := (Clifford.onCircleM_iff a z).1 ha
  have hzb := (Clifford.onCircleM_iff b z).1 hb
  have hzc := (Clifford.onCircleM_iff c z).1 hc
  have hd : conj z * Clifford.triP a b c (conj a) (conj b) (conj c) = 0 := by
    rw [Clifford.triP, Clifford.det3]
    linear_combination (conj c - conj b) * hza + (conj a - conj c) * hzb + (conj b - conj a) * hzc
  exact (mul_eq_zero.mp hd).resolve_left ((map_ne_zero conj).2 hz0)

lemma genTriple_swap23 {a b c : ℂ} (h : Clifford.GenTriple a b c) : Clifford.GenTriple a c b := by
  have ht : Clifford.triP a c b (conj a) (conj c) (conj b) = - Clifford.triP a b c (conj a) (conj b) (conj c) := by
    unfold Clifford.triP Clifford.det3
    ring_nf
  have hc : Clifford.cycP a c b (conj a) (conj c) (conj b) = - Clifford.cycP a b c (conj a) (conj b) (conj c) := by
    unfold Clifford.cycP Clifford.det3
    ring_nf
  rw [Clifford.GenTriple] at h ⊢
  rw [ht, hc]
  exact ⟨neg_ne_zero.mpr h.1, neg_ne_zero.mpr h.2⟩

lemma genTriple_cycle {a b c : ℂ} (h : Clifford.GenTriple a b c) : Clifford.GenTriple b c a := by
  have ht : Clifford.triP b c a (conj b) (conj c) (conj a) = Clifford.triP a b c (conj a) (conj b) (conj c) := by
    unfold Clifford.triP Clifford.det3
    ring_nf
  have hc : Clifford.cycP b c a (conj b) (conj c) (conj a) = Clifford.cycP a b c (conj a) (conj b) (conj c) := by
    unfold Clifford.cycP Clifford.det3
    ring_nf
  rw [Clifford.GenTriple] at h ⊢
  rw [ht, hc]
  exact h

lemma genTriple_of_ne {n : ℕ} {c : Fin n → ℂ} (h : Clifford.GenPosN c) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Clifford.GenTriple (c i) (c j) (c k) := by
  rcases lt_trichotomy i j with hijlt | rfl | hjilt
  · rcases lt_trichotomy j k with hjlt | rfl | hklt
    · exact h.2 i j k hijlt hjlt
    · exact (hjk rfl).elim
    · rcases lt_trichotomy i k with hiklt | rfl | hkilt
      · exact genTriple_swap23 (h.2 i k j hiklt hklt)
      · exact (hik rfl).elim
      · exact genTriple_cycle (h.2 k i j hkilt hijlt)
  · exact (hij rfl).elim
  · rcases lt_trichotomy i k with hiklt | rfl | hkilt
    · exact genTriple_cycle (genTriple_cycle (genTriple_swap23 (h.2 j i k hjilt hiklt)))
    · exact (hik rfl).elim
    · rcases lt_trichotomy j k with hjlt | rfl | hklt
      · exact genTriple_cycle (genTriple_cycle (h.2 j k i hjlt hkilt))
      · exact (hjk rfl).elim
      · exact genTriple_cycle (genTriple_swap23 (h.2 k j i hklt hjilt))

lemma no_common {n : ℕ} {c : Fin n → ℂ} (h : Clifford.GenPosN c) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ ∃ z : ℂ, z ≠ 0 ∧ z ∈ BlindCircle (c i) ∧ z ∈ BlindCircle (c j) ∧ z ∈ BlindCircle (c k) := by
  rintro ⟨z, hz0, hzi, hzj, hzk⟩
  have ht := (genTriple_of_ne h hij hik hjk).1
  apply ht
  apply triP_eq_zero_of_common hz0
  · exact mem_sphere_iff_onCircleM (c i) z |>.1 (by simpa [BlindCircle] using hzi)
  · exact mem_sphere_iff_onCircleM (c j) z |>.1 (by simpa [BlindCircle] using hzj)
  · exact mem_sphere_iff_onCircleM (c k) z |>.1 (by simpa [BlindCircle] using hzk)

/-- Library general position implies the writer's general position. -/
theorem genPosN_blindGenPos {n : ℕ} {c : Fin n → ℂ} (h : Clifford.GenPosN c) :
    BlindGenPos c := by
  refine ⟨fun i j hij => blindTransversal_iff.2 (h.1 i j hij), ?_⟩
  intro i j k hij hik hjk
  refine ⟨no_common h hij hik hjk, ?_, ?_, ?_⟩
  · have hijt := h.1 i j hij
    have hikt := h.1 i k hik
    intro he
    rw [BlindSecond_eq hijt, BlindSecond_eq hikt] at he
    have hq0 : Clifford.second (c i) (c j) ≠ 0 := Clifford.second_ne_zero hijt
    have hqi : Clifford.second (c i) (c j) ∈ BlindCircle (c i) := by
      rw [BlindCircle]; exact mem_sphere_iff_onCircleM (c i) _ |>.2 (Clifford.second_onCircleM_left hijt.ne)
    have hqj : Clifford.second (c i) (c j) ∈ BlindCircle (c j) := by
      rw [BlindCircle]; exact mem_sphere_iff_onCircleM (c j) _ |>.2 (Clifford.second_onCircleM_right hijt.ne)
    have hqk : Clifford.second (c i) (c j) ∈ BlindCircle (c k) := by
      rw [he]
      rw [BlindCircle]; exact mem_sphere_iff_onCircleM (c k) (Clifford.second (c i) (c k)) |>.2 (Clifford.second_onCircleM_right hikt.ne)
    exact (no_common h hij hik hjk) ⟨_, hq0, hqi, hqj, hqk⟩
  · have hijt := h.1 i j hij
    have hjkt := h.1 j k hjk
    intro he
    rw [BlindSecond_eq hijt, BlindSecond_eq hjkt] at he
    have hq0 : Clifford.second (c i) (c j) ≠ 0 := Clifford.second_ne_zero hijt
    have hqi : Clifford.second (c i) (c j) ∈ BlindCircle (c i) := by
      rw [BlindCircle]; exact mem_sphere_iff_onCircleM (c i) _ |>.2 (Clifford.second_onCircleM_left hijt.ne)
    have hqj : Clifford.second (c i) (c j) ∈ BlindCircle (c j) := by
      rw [BlindCircle]; exact mem_sphere_iff_onCircleM (c j) _ |>.2 (Clifford.second_onCircleM_right hijt.ne)
    have hqk : Clifford.second (c i) (c j) ∈ BlindCircle (c k) := by
      rw [he]
      rw [BlindCircle]; exact mem_sphere_iff_onCircleM (c k) (Clifford.second (c j) (c k)) |>.2 (Clifford.second_onCircleM_right hjkt.ne)
    exact (no_common h hij hik hjk) ⟨_, hq0, hqi, hqj, hqk⟩
  · have hikt := h.1 i k hik
    have hjkt := h.1 j k hjk
    intro he
    rw [BlindSecond_eq hikt, BlindSecond_eq hjkt] at he
    have hq0 : Clifford.second (c i) (c k) ≠ 0 := Clifford.second_ne_zero hikt
    have hqi : Clifford.second (c i) (c k) ∈ BlindCircle (c i) := by
      rw [BlindCircle]; exact mem_sphere_iff_onCircleM (c i) _ |>.2 (Clifford.second_onCircleM_left hikt.ne)
    have hqj : Clifford.second (c i) (c k) ∈ BlindCircle (c j) := by
      rw [he]
      rw [BlindCircle]; exact mem_sphere_iff_onCircleM (c j) (Clifford.second (c j) (c k)) |>.2 (Clifford.second_onCircleM_left hjkt.ne)
    have hqk : Clifford.second (c i) (c k) ∈ BlindCircle (c k) := by
      rw [BlindCircle]; exact mem_sphere_iff_onCircleM (c k) _ |>.2 (Clifford.second_onCircleM_right hikt.ne)
    exact (no_common h hij hik hjk) ⟨_, hq0, hqi, hqj, hqk⟩

/-! ## 4. Generalized circles -/

/-- The writer's generalized circle is a library generalized circle on the sphere. -/
theorem isGCircleS_of_blindIsGCircle {X : Set BlindS} (h : BlindIsGCircle X) :
    Clifford.IsGCircleS X := by
  rcases h with ⟨z, r, hr, rfl⟩ | ⟨a, b, hab, rfl⟩
  · exact Or.inl ⟨z, r, rfl⟩
  · refine Or.inr ⟨a, b - a, sub_ne_zero.mpr (Ne.symm hab), ?_⟩
    ext x
    simp [Clifford.lineS, BlindEmb, Complex.real_smul]

/-! ## 5. The recursive transport -/

lemma odd_add_three_iff_mod_two_eq_zero (m : ℕ) : Odd (m + 3) ↔ m % 2 = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    have hm : m = 2 * (k - 1) := by omega
    rw [hm]
    exact Nat.mod_eq_zero_of_dvd ⟨k - 1, by ring⟩
  · intro hm
    rcases Nat.dvd_of_mod_eq_zero hm with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    omega

/-- Conversely, every writer-side blind object at a positive level is a library chain object. -/
theorem chainS_of_blind : ∀ (n : ℕ) (c : Fin n → ℂ) (X : Set BlindS),
    Clifford.GenPosN c → BlindCliffordP false n c X → Clifford.ChainS n c X
  | 0, c, X, hc, h => by
      simpa [BlindCliffordP, Clifford.ChainS] using h.2
  | 1, c, X, hc, h => by
      simpa [BlindCliffordP, Clifford.ChainS, BlindCircle, BlindEmb] using h.2
  | 2, c, X, hc, h => by
      have hsec := BlindSecond_eq (hc.1 0 1 (by decide))
      simpa [BlindCliffordP, Clifford.ChainS, hsec] using h.2
  | m + 3, c, X, hc, h => by
      by_cases hodd : Odd (m + 3)
      · simp [BlindCliffordP, hodd] at h
        have hm : m % 2 = 0 := (odd_add_three_iff_mod_two_eq_zero m).1 hodd
        rw [Clifford.ChainS, if_pos hm]
        rcases h with ⟨hX, hi⟩
        refine ⟨isGCircleS_of_blindIsGCircle hX, ?_⟩
        intro i
        rcases hi i with ⟨p, hp, hpx⟩
        have hp' : BlindCliffordP false (m + 2) (c ∘ i.succAbove) {p} := by
          change BlindCliffordP false (m + 2) (fun j => c (i.succAbove j)) {p} at hp
          simpa [Function.comp_def] using hp
        refine ⟨p, chainS_of_blind (m + 2) (c ∘ i.succAbove) {p} (hc.comp_succAbove i) hp', hpx⟩
      · simp [BlindCliffordP, hodd] at h
        have hm : m % 2 ≠ 0 := by
          intro hm
          exact hodd ((odd_add_three_iff_mod_two_eq_zero m).2 hm)
        rw [Clifford.ChainS, if_neg hm]
        rcases h with ⟨p, hX, hi⟩
        refine ⟨p, hX, ?_⟩
        intro i
        rcases hi i with ⟨Y, hY, hgc, hpy⟩
        have hY' : BlindCliffordP false (m + 2) (c ∘ i.succAbove) Y := by
          change BlindCliffordP false (m + 2) (fun j => c (i.succAbove j)) Y at hY
          simpa [Function.comp_def] using hY
        refine ⟨Y, chainS_of_blind (m + 2) (c ∘ i.succAbove) Y (hc.comp_succAbove i) hY', hpy⟩
termination_by n => n

/-- Every library chain object is a writer-side blind Clifford object, under general position. -/
theorem blindOfChainS : ∀ (n : ℕ) (c : Fin n → ℂ) (X : Set BlindS),
    Clifford.GenPosN c → Clifford.ChainS n c X → BlindCliffordP false n c X := by
  sorry

end

end PaperLBlind

namespace BlindCompareFull

open PaperLBlind

noncomputable section

/-! ## 6. The rows this closes

`BlindN1`, `BlindN7`, `BlindN6` are the writer statements as transcribed in
`scratch/BlindCompareFull.lean`; `RealN1`, `RealN7`, `RealN6` are the library propositions. -/

/-- `BlindSix` is the library's `Counter6.cx`. -/
theorem BlindSix_eq : BlindSix = Clifford.Counter6.cx := by
  rfl

lemma blindIsGCircle_of_isGCircle_of_two {s : Set ℂ} (h : Clifford.IsGCircle s)
    {p q : ℂ} (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) :
    ∃ Y : Set BlindS, BlindIsGCircle Y ∧ ∀ z ∈ s, (z : BlindS) ∈ Y := by
  rcases h with ⟨o, r, rfl⟩ | ⟨a, b, hv, rfl⟩
  · have hr_nonneg : 0 ≤ r := by
      have hpr : dist p o = r := Metric.mem_sphere.mp hp
      rw [← hpr]
      exact dist_nonneg
    have hr_ne : r ≠ 0 := by
      intro hr0
      have hpo : p = o := by
        apply dist_eq_zero.mp
        simpa [hr0] using (Metric.mem_sphere.mp hp)
      have hqo : q = o := by
        apply dist_eq_zero.mp
        simpa [hr0] using (Metric.mem_sphere.mp hq)
      exact hpq (hpo.trans hqo.symm)
    have hrpos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne)
    refine ⟨BlindEmb (Metric.sphere o r), Or.inl ⟨o, r, hrpos, rfl⟩, ?_⟩
    intro z hz
    exact ⟨z, hz, rfl⟩
  · have hab : a ≠ a + b := by
      intro h'
      apply hv
      calc
        b = (a + b) - a := by ring
        _ = a - a := by rw [← h']
        _ = 0 := by ring
    let L : Set ℂ := {z : ℂ | ∃ t : ℝ, z = a + t • b}
    refine ⟨insert ∞ (BlindEmb L), Or.inr ⟨a, a + b, hab, ?_⟩, ?_⟩
    · ext x
      simp [BlindEmb, L, Complex.real_smul]
    · intro z hz
      exact Or.inr ⟨z, hz, rfl⟩

lemma blindIsGCircle_lineS (a v : ℂ) (hv : v ≠ 0) : BlindIsGCircle (Clifford.lineS a v) := by
  refine Or.inr ⟨a, a + v, ?_, ?_⟩
  · intro he
    apply hv
    calc
      v = (a + v) - a := by ring
      _ = a - a := by rw [← he]
      _ = 0 := by ring
  · ext x
    simp [Clifford.lineS, BlindEmb, Complex.real_smul]

lemma blindIsGCircle_of_isGCircleS_of_two {Y : Set BlindS} (h : Clifford.IsGCircleS Y)
    {p q : ℂ} (hp : (p : BlindS) ∈ Y) (hq : (q : BlindS) ∈ Y) (hpq : p ≠ q) :
    BlindIsGCircle Y := by
  rcases h with ⟨o, r, rfl⟩ | ⟨a, v, hv, rfl⟩
  · have hpr : dist p o = r := by rw [Complex.dist_eq]; simpa using hp
    have hqr : dist q o = r := by rw [Complex.dist_eq]; simpa using hq
    have hr0 : 0 ≤ r := by rw [← hpr]; exact dist_nonneg
    have hrne : r ≠ 0 := by
      intro hr
      have hp0 : p = o := dist_eq_zero.mp (by simpa [hr] using hpr)
      have hq0 : q = o := dist_eq_zero.mp (by simpa [hr] using hqr)
      exact hpq (hp0.trans hq0.symm)
    exact Or.inl ⟨o, r, lt_of_le_of_ne hr0 (Ne.symm hrne), rfl⟩
  · exact blindIsGCircle_lineS a v hv

lemma blindCliffordP2_of_chainS {d : Fin 2 → ℂ} (hd : Clifford.GenPosN d) {X : Set BlindS}
    (hX : Clifford.ChainS 2 d X) : BlindCliffordP false 2 d X := by
  have hXeq : X = {((Clifford.second (d 0) (d 1) : ℂ) : BlindS)} := by
    simpa [Clifford.ChainS] using hX
  have hsec : BlindSecond (d 0) (d 1) = Clifford.second (d 0) (d 1) :=
    BlindSecond_eq (hd.1 0 1 (by decide))
  simp [BlindCliffordP, hXeq, hsec]

lemma blindCliffordP3_of_chainS {d : Fin 3 → ℂ} (hd : Clifford.GenPosN d) {Y : Set BlindS}
    (hY : Clifford.ChainS 3 d Y) : BlindCliffordP false 3 d Y := by
  have hmem : Clifford.IsGCircleS Y ∧
      ∀ i : Fin 3, ∃ p : BlindS, Clifford.ChainS 2 (d ∘ i.succAbove) {p} ∧ p ∈ Y := by
    simpa [Clifford.ChainS] using hY
  have e : d = ![d 0, d 1, d 2] := by funext k; fin_cases k <;> rfl
  have hfin : Clifford.Chain 3 d (((↑) : ℂ → BlindS) ⁻¹' Y) := Clifford.chain3_of_chainS hY
  rw [e] at hfin
  obtain ⟨_, m12, m02, m01⟩ := Clifford.chain3_mem hfin
  have hpY : ((Clifford.second (d 0) (d 1) : ℂ) : BlindS) ∈ Y := m01
  have hqY : ((Clifford.second (d 0) (d 2) : ℂ) : BlindS) ∈ Y := m02
  have hne : Clifford.second (d 0) (d 1) ≠ Clifford.second (d 0) (d 2) := by
    have hne' := (genPosN_blindGenPos hd).2 0 1 2 (by decide) (by decide) (by decide) |>.2.1
    simpa [BlindSecond_eq (hd.1 0 1 (by decide)), BlindSecond_eq (hd.1 0 2 (by decide))] using hne'
  have hgc : BlindIsGCircle Y :=
    blindIsGCircle_of_isGCircleS_of_two hmem.1 hpY hqY hne
  rw [BlindCliffordP, if_pos (by decide : Odd 3)]
  simp only [Bool.false_eq_true, false_implies, true_and]
  refine ⟨hgc, ?_⟩
  intro i
  rcases hmem.2 i with ⟨p, hpchain, hpY'⟩
  have hpEq : p = ((Clifford.second ((d ∘ i.succAbove) 0) ((d ∘ i.succAbove) 1) : ℂ) : BlindS) := by
    exact Set.singleton_eq_singleton_iff.1 (by simpa [Clifford.ChainS] using hpchain)
  refine ⟨p, ?_, hpY'⟩
  have hsec : BlindSecond ((d ∘ i.succAbove) 0) ((d ∘ i.succAbove) 1) =
      Clifford.second ((d ∘ i.succAbove) 0) ((d ∘ i.succAbove) 1) :=
    BlindSecond_eq ((hd.comp_succAbove i).1 0 1 (by decide))
  simpa [BlindCliffordP, BlindDelete, Function.comp_def, hpEq] using hsec.symm

lemma blindCliffordP4_of_chainS {d : Fin 4 → ℂ} (hd : Clifford.GenPosN d) {p : BlindS}
    (_hpfin : ∃ z : ℂ, p = (z : BlindS)) (h : Clifford.ChainS 4 d {p}) :
    BlindCliffordP false 4 d {p} := by
  have hmem : ∃ q : BlindS, ({p} : Set BlindS) = {q} ∧
      ∀ i : Fin 4, ∃ Y : Set BlindS, Clifford.ChainS 3 (d ∘ i.succAbove) Y ∧ q ∈ Y := by
    simpa [Clifford.ChainS] using h
  rcases hmem with ⟨q, hqp, hqmem⟩
  have hpq : p = q := Set.singleton_eq_singleton_iff.1 hqp
  subst q
  rw [BlindCliffordP, if_neg (by decide : ¬ Odd 4)]
  simp only [Bool.false_eq_true, false_implies, true_and]
  refine ⟨p, rfl, ?_⟩
  intro i
  rcases hqmem i with ⟨Y, hYc, hpY⟩
  have hYblind := blindCliffordP3_of_chainS (hd.comp_succAbove i) hYc
  have hYgc : BlindIsGCircle Y := by
    have htmp := hYblind
    rw [BlindCliffordP, if_pos (by decide : Odd 3)] at htmp
    have hmem3 : BlindIsGCircle Y ∧
        ∀ j : Fin 3, ∃ q : BlindS,
          BlindCliffordP false 2 (BlindDelete (d ∘ i.succAbove) j) {q} ∧ q ∈ Y := by
      simpa only [Bool.false_eq_true, false_implies, implies_true, true_and] using htmp
    exact hmem3.1
  exact ⟨Y, hYblind, hYgc, hpY⟩

lemma chainS4_finite_of_colD {a b c d : ℂ}
    (hcol : Clifford.colD (Clifford.second c d) (Clifford.second b d) (Clifford.second b c) ≠ 0)
    {p : BlindS} (h : Clifford.ChainS 4 ![a, b, c, d] {p}) : ∃ z : ℂ, p = (z : BlindS) := by
  induction p using OnePoint.rec with
  | infty =>
      have h0 := Clifford.chain4S_infty h
      exact (hcol h0).elim
  | coe z => exact ⟨z, rfl⟩

lemma chainS4_finite_0123 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨6, -3⟩) (c := ⟨1, 2⟩) (d := ⟨-2, -1⟩)
  · norm_num [Clifford.Counter6.s23, Clifford.Counter6.s13, Clifford.Counter6.s12,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_0124 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨6, -3⟩, ⟨1, 2⟩, ⟨0, -4⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨6, -3⟩) (c := ⟨1, 2⟩) (d := ⟨0, -4⟩)
  · norm_num [Clifford.Counter6.s24, Clifford.Counter6.s14, Clifford.Counter6.s12,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_0125 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨6, -3⟩, ⟨1, 2⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨6, -3⟩) (c := ⟨1, 2⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s25, Clifford.Counter6.s15, Clifford.Counter6.s12,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_0134 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨6, -3⟩, ⟨-2, -1⟩, ⟨0, -4⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨6, -3⟩) (c := ⟨-2, -1⟩) (d := ⟨0, -4⟩)
  · norm_num [Clifford.Counter6.s34, Clifford.Counter6.s14, Clifford.Counter6.s13,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_0135 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨6, -3⟩, ⟨-2, -1⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨6, -3⟩) (c := ⟨-2, -1⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s35, Clifford.Counter6.s15, Clifford.Counter6.s13,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_0145 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨6, -3⟩, ⟨0, -4⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨6, -3⟩) (c := ⟨0, -4⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s45, Clifford.Counter6.s15, Clifford.Counter6.s14,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_0234 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨1, 2⟩) (c := ⟨-2, -1⟩) (d := ⟨0, -4⟩)
  · norm_num [Clifford.Counter6.s34, Clifford.Counter6.s24, Clifford.Counter6.s23,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_0235 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨1, 2⟩) (c := ⟨-2, -1⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s35, Clifford.Counter6.s25, Clifford.Counter6.s23,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_0245 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨1, 2⟩, ⟨0, -4⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨1, 2⟩) (c := ⟨0, -4⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s45, Clifford.Counter6.s25, Clifford.Counter6.s24,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_0345 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨3, -6⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨3, -6⟩) (b := ⟨-2, -1⟩) (c := ⟨0, -4⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s45, Clifford.Counter6.s35, Clifford.Counter6.s34,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_1234 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨6, -3⟩) (b := ⟨1, 2⟩) (c := ⟨-2, -1⟩) (d := ⟨0, -4⟩)
  · norm_num [Clifford.Counter6.s34, Clifford.Counter6.s24, Clifford.Counter6.s23,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_1235 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨6, -3⟩) (b := ⟨1, 2⟩) (c := ⟨-2, -1⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s35, Clifford.Counter6.s25, Clifford.Counter6.s23,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_1245 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨6, -3⟩, ⟨1, 2⟩, ⟨0, -4⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨6, -3⟩) (b := ⟨1, 2⟩) (c := ⟨0, -4⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s45, Clifford.Counter6.s25, Clifford.Counter6.s24,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_1345 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨6, -3⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨6, -3⟩) (b := ⟨-2, -1⟩) (c := ⟨0, -4⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s45, Clifford.Counter6.s35, Clifford.Counter6.s34,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma chainS4_finite_2345 {q : BlindS}
    (hq : Clifford.ChainS 4 ![⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩] {q}) :
    ∃ z : ℂ, q = (z : BlindS) := by
  apply chainS4_finite_of_colD
    (a := ⟨1, 2⟩) (b := ⟨-2, -1⟩) (c := ⟨0, -4⟩) (d := ⟨4, 0⟩)
  · norm_num [Clifford.Counter6.s45, Clifford.Counter6.s35, Clifford.Counter6.s34,
      Clifford.colD, Clifford.det3]
  · exact hq

lemma blindCliffordP5_of_chainS {d : Fin 5 → ℂ} (hd : Clifford.GenPosN d) {Y : Set BlindS}
    (hinfty : ∞ ∈ Y)
    (hfin4 : ∀ (i : Fin 5) (p : BlindS),
      Clifford.ChainS 4 (d ∘ i.succAbove) {p} → ∃ z : ℂ, p = (z : BlindS))
    (hY : Clifford.ChainS 5 d Y) : BlindCliffordP false 5 d Y := by
  have hmem : Clifford.IsGCircleS Y ∧
      ∀ i : Fin 5, ∃ p : BlindS, Clifford.ChainS 4 (d ∘ i.succAbove) {p} ∧ p ∈ Y := by
    simpa [Clifford.ChainS] using hY
  obtain ⟨a, v, hv, hYeq⟩ := Clifford.IsGCircleS.infty_mem hmem.1 hinfty
  subst Y
  rw [BlindCliffordP, if_pos (by decide : Odd 5)]
  simp only [Bool.false_eq_true, false_implies, true_and]
  refine ⟨blindIsGCircle_lineS a v hv, ?_⟩
  intro i
  rcases hmem.2 i with ⟨p, hpchain, hpY⟩
  rcases hfin4 i p hpchain with ⟨z, rfl⟩
  exact ⟨(z : BlindS), blindCliffordP4_of_chainS (hd.comp_succAbove i) ⟨z, rfl⟩ hpchain, hpY⟩

/-- Row 1, real ⇒ writer: `CliffordChainS` for every `n ≥ 1` gives a blind level object. -/
theorem N1_RB (h : RealN1) : BlindN1 := by
  sorry

/-- Row 7, real ⇒ writer: the level-3 sphere chain gives the writer's circle through the three
blind second intersections. -/
theorem N7_RB (h : RealN7) : BlindN7 := by
  have _ := h
  intro c hc
  let p : ℂ := BlindSecond (c 0) (c 1)
  let q : ℂ := BlindSecond (c 0) (c 2)
  let r : ℂ := BlindSecond (c 1) (c 2)
  have hpq : p ≠ q := by
    exact (hc.2 0 1 2 (by decide) (by decide) (by decide)).2.1
  obtain ⟨X, hX, hsub⟩ := Clifford.exists_gcircle
    (Clifford.cospherical_or_collinear p q r)
  have hpmem : p ∈ ({p, q, r} : Set ℂ) := by simp
  have hqmem : q ∈ ({p, q, r} : Set ℂ) := by simp
  have hrmem : r ∈ ({p, q, r} : Set ℂ) := by simp
  obtain ⟨Y, hYgc, hmemY⟩ :=
    blindIsGCircle_of_isGCircle_of_two hX (hsub hpmem) (hsub hqmem) hpq
  refine ⟨Y, hYgc, ?_, ?_, ?_⟩
  · exact hmemY p (hsub hpmem)
  · exact hmemY q (hsub hqmem)
  · exact hmemY r (hsub hrmem)

/-- Row 6, real ⇒ writer: existence and uniqueness of the level-6 object for `BlindSix`. -/
theorem N6_RB (h : RealN6) : BlindN6 := by
  constructor
  · rw [BlindSix_eq]
    change BlindCliffordP false 6 Clifford.Counter6.cx {∞}
    have hmem : ∃ p : BlindS, ({∞} : Set BlindS) = {p} ∧
        ∀ i : Fin 6, ∃ Y : Set BlindS,
          Clifford.ChainS 5 (Clifford.Counter6.cx ∘ i.succAbove) Y ∧ p ∈ Y := by
      simpa [Clifford.ChainS] using h.1
    rcases hmem with ⟨p, hp, hchildren⟩
    have hpEq : p = ∞ := (Set.singleton_eq_singleton_iff.1 hp).symm
    subst p
    rw [BlindCliffordP, if_neg (by decide : ¬ Odd 6)]
    simp only [Bool.false_eq_true, false_implies, true_and]
    refine ⟨(∞ : BlindS), rfl, ?_⟩
    intro i
    rcases hchildren i with ⟨Y, hYc, hinfY⟩
    have hd5 : Clifford.GenPosN (Clifford.Counter6.cx ∘ i.succAbove) :=
      Clifford.Counter6.cx_genPosN.comp_succAbove i
    have hfin4 : ∀ (j : Fin 5) (q : BlindS),
        Clifford.ChainS 4 ((Clifford.Counter6.cx ∘ i.succAbove) ∘ j.succAbove) {q} →
          ∃ z : ℂ, q = (z : BlindS) := by
      intro j q hq
      fin_cases i <;> fin_cases j
      · exact chainS4_finite_2345 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx])
      · exact chainS4_finite_1345 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_1245 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_1235 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_1234 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_2345 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0345 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0245 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0235 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0234 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_1345 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0345 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0145 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0135 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0134 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_1245 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0245 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0145 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0125 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0124 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_1235 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0235 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0135 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0125 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0123 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_1234 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0234 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0134 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0124 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
      · exact chainS4_finite_0123 (by
          convert hq using 1
          funext k
          fin_cases k <;> simp [Clifford.Counter6.cx, Fin.succAbove])
    have hYblind := blindCliffordP5_of_chainS hd5 hinfY hfin4 hYc
    have hYgc : BlindIsGCircle Y := by
      have htmp := hYblind
      rw [BlindCliffordP, if_pos (by decide : Odd 5)] at htmp
      have hmem5 : BlindIsGCircle Y ∧
          ∀ j : Fin 5, ∃ q : BlindS,
            BlindCliffordP false 4 (BlindDelete (Clifford.Counter6.cx ∘ i.succAbove) j) {q} ∧ q ∈ Y := by
        simpa only [Bool.false_eq_true, false_implies, true_and] using htmp
      exact hmem5.1
    exact ⟨Y, hYblind, hYgc, hinfY⟩
  · intro X hX
    have hc : Clifford.GenPosN BlindSix := by
      rw [BlindSix_eq]
      exact Clifford.Counter6.cx_genPosN
    have hchain : Clifford.ChainS 6 BlindSix X := chainS_of_blind 6 BlindSix X hc hX
    rw [BlindSix_eq] at hchain
    exact Clifford.Counter6S.chainS_six_unique hchain

end

end BlindCompareFull
