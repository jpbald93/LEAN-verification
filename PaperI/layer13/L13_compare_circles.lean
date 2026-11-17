import CircleSystems

/-!
# L13 comparison (J), circle systems: blind statements (PaperIBlind.lean) vs `CircleSystems`.
No theorem of the `CircleSystems` library is used in any proof body; library names occur only
inside `type_of%` to state goals. Library *definitions* (`radicalAxis`, `powPt`, `pencilCenter`,
`pencilRadSq`, `cross`, `cx`, `cy`) are unfolded.
-/

noncomputable section
open scoped RealInnerProductSpace
open Set Metric EuclideanGeometry

universe u
set_option linter.unusedVariables false

namespace L13JC

/-! ## Blind definitions (verbatim from Blind.lean) -/

def BlindPlane (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] : Prop :=
  Module.finrank ℝ V = 2

def BlindCross {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e : OrthonormalBasis (Fin 2) ℝ V) (v w : V) : ℝ :=
  inner ℝ v (e 0) * inner ℝ w (e 1) -
    inner ℝ v (e 1) * inner ℝ w (e 0)

def BlindVectorPower {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (X O : V) (R : ℝ) : ℝ :=
  ‖X - O‖ ^ 2 - R ^ 2

def BlindVectorRadicalAxis {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (O₁ O₂ : V) (R₁ R₂ : ℝ) : Set V :=
  {X | BlindVectorPower X O₁ R₁ = BlindVectorPower X O₂ R₂}

def BlindPencilPower {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (O₁ O₂ : V) (R₁ R₂ t : ℝ) (X : V) : ℝ :=
  (1 - t) * BlindVectorPower X O₁ R₁ + t * BlindVectorPower X O₂ R₂

def BlindPerpendicularFoot {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (P X Y D : V) : Prop :=
  (∃ t : ℝ, D = X + t • (Y - X)) ∧
    inner ℝ (P - D) (Y - X) = 0

/-! ## Blind statements as closed propositions (verbatim; the proof placeholder dropped) -/

-- thm:radical  (blind_43)
def blind43_stmt : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ O₃ : V) (R₁ R₂ R₃ : ℝ)
    (hV : Module.finrank ℝ V = 2)
    (hO : ¬ Collinear ℝ ({O₁, O₂, O₃} : Set V)),
    ∃! X : V,
      X ∈ BlindVectorRadicalAxis O₁ O₂ R₁ R₂ ∧
      X ∈ BlindVectorRadicalAxis O₂ O₃ R₂ R₃ ∧
      X ∈ BlindVectorRadicalAxis O₃ O₁ R₃ R₁

-- thm:coaxal  (blind_46)
def blind46_stmt : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ X : V) (R₁ R₂ t : ℝ)
    (h₁ : dist X O₁ = R₁) (h₂ : dist X O₂ = R₂),
    BlindPencilPower O₁ O₂ R₁ R₂ t X = 0

-- thm:johnson  (blind_48)
def blind48_stmt : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ O₃ H : V) (R : ℝ)
    (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R),
    let A := O₂ + O₃ - H
    let B := O₃ + O₁ - H
    let C := O₁ + O₂ - H
    let J := O₁ + O₂ + O₃ - (2 : ℝ) • H
    dist A J = R ∧ dist B J = R ∧ dist C J = R

-- thm:johnson  (blind_49)
def blind49_stmt : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ O₃ H : V) (R : ℝ)
    (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R),
    let A := O₂ + O₃ - H
    let B := O₃ + O₁ - H
    let C := O₁ + O₂ - H
    dist A O₂ = R ∧ dist A O₃ = R ∧
    dist B O₃ = R ∧ dist B O₁ = R ∧
    dist C O₁ = R ∧ dist C O₂ = R

-- thm:johnson  (blind_51)
def blind51_stmt : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (O₁ O₂ O₃ H : V) (R : ℝ)
    (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R),
    let A := O₂ + O₃ - H
    let B := O₃ + O₁ - H
    let C := O₁ + O₂ - H
    inner ℝ (H - A) (C - B) = 0 ∧
    inner ℝ (H - B) (A - C) = 0 ∧
    inner ℝ (H - C) (B - A) = 0

-- thm:simson  (blind_52)
def blind52_stmt : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (β : OrthonormalBasis (Fin 2) ℝ V)
    (A B C O P D E F : V) (R : ℝ)
    (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hD : BlindPerpendicularFoot P B C D)
    (hE : BlindPerpendicularFoot P C A E)
    (hF : BlindPerpendicularFoot P A B F),
    4 * R ^ 2 * BlindCross β (E - D) (F - D) =
      -BlindCross β (B - A) (C - A) * BlindVectorPower P O R

-- thm:simson  (blind_53)
def blind53_stmt : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C O P D E F : V) (R : ℝ)
    (hV : Module.finrank ℝ V = 2)
    (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set V))
    (hD : BlindPerpendicularFoot P B C D)
    (hE : BlindPerpendicularFoot P C A E)
    (hF : BlindPerpendicularFoot P A B F),
    Collinear ℝ ({D, E, F} : Set V) ↔ dist P O = R

-- thm:steinerline  (blind_55)
def blind55_stmt : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C O P D E F : V) (R : ℝ)
    (hV : Module.finrank ℝ V = 2)
    (hA : dist A O = R) (hB : dist B O = R)
    (hC : dist C O = R) (hP : dist P O = R)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hD : BlindPerpendicularFoot P B C D)
    (hE : BlindPerpendicularFoot P C A E)
    (hF : BlindPerpendicularFoot P A B F),
    Collinear ℝ
      ({A + B + C - (2 : ℝ) • O,
        (2 : ℝ) • D - P, (2 : ℝ) • E - P,
        (2 : ℝ) • F - P} : Set V)

/-! ## Bridging lemmas (Mathlib only) -/

section Bridges
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem foot_iff (P X Y D : V) :
    BlindPerpendicularFoot P X Y D ↔ D = (orthogonalProjection line[ℝ, X, Y] P : V) := by
  rw [eq_comm, coe_orthogonalProjection_eq_iff_mem, direction_affineSpan, vectorSpan_pair,
    Submodule.mem_orthogonal_singleton_iff_inner_right, mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [BlindPerpendicularFoot, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  constructor
  · rintro ⟨⟨t, ht⟩, h⟩
    refine ⟨⟨t, by rw [ht]; abel⟩, ?_⟩
    rw [show X - Y = -(Y - X) by abel, inner_neg_left, real_inner_comm, h, neg_zero]
  · rintro ⟨⟨t, ht⟩, h⟩
    refine ⟨⟨t, by rw [← ht]; abel⟩, ?_⟩
    rw [show X - Y = -(Y - X) by abel, inner_neg_left, real_inner_comm] at h
    linarith

theorem foot_proj (P X Y : V) :
    BlindPerpendicularFoot P X Y (orthogonalProjection line[ℝ, X, Y] P : V) :=
  (foot_iff P X Y _).2 rfl

theorem cross_eq (b : OrthonormalBasis (Fin 2) ℝ V) (v w : V) :
    CircleSystems.cross b v w = BlindCross b v w := by
  simp only [CircleSystems.cross, CircleSystems.cx, CircleSystems.cy, BlindCross,
    real_inner_comm (b 0), real_inner_comm (b 1)]

theorem powPt_eq (P O : V) (R : ℝ) : CircleSystems.powPt P O R = BlindVectorPower P O R := by
  simp only [CircleSystems.powPt, BlindVectorPower, dist_eq_norm]

theorem radicalAxis_eq (O₁ O₂ : V) (R₁ R₂ : ℝ) :
    CircleSystems.radicalAxis O₁ R₁ O₂ R₂ = BlindVectorRadicalAxis O₁ O₂ R₁ R₂ := by
  ext X; simp only [CircleSystems.radicalAxis, BlindVectorRadicalAxis, Set.mem_ofPred_eq, powPt_eq]

/-- Pure inner-product identity: the pencil power function is a circle power function. -/
theorem pencil_identity (O₁ O₂ X : V) (R₁ R₂ t : ℝ) :
    BlindPencilPower O₁ O₂ R₁ R₂ t X =
      dist X (CircleSystems.pencilCenter O₁ O₂ t) ^ 2 - CircleSystems.pencilRadSq O₁ R₁ O₂ R₂ t := by
  simp only [BlindPencilPower, BlindVectorPower, CircleSystems.pencilCenter,
    CircleSystems.pencilRadSq, dist_eq_norm]
  have e1 : X - ((1 - t) • O₁ + t • O₂) = (1 - t) • (X - O₁) + t • (X - O₂) := by module
  have e2 : O₁ - O₂ = (X - O₂) - (X - O₁) := by abel
  rw [e1, e2]
  generalize X - O₁ = a
  generalize X - O₂ = b
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm a b]
  ring

theorem ne_of_not_collinear {A B C : V} (h : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  refine ⟨?_, ?_, ?_⟩ <;> intro he <;> apply h
  · rw [he, Set.insert_eq_of_mem (Set.mem_insert _ _)]; exact collinear_pair ℝ _ _
  · rw [he, Set.pair_eq_singleton]; exact collinear_pair ℝ _ _
  · rw [← he, Set.insert_eq_of_mem (Set.mem_insert_of_mem _ (Set.mem_singleton _))]
    exact collinear_pair ℝ _ _

theorem reflection_eq (X Y P : V) :
    (reflection line[ℝ, X, Y] P : V) = (2 : ℝ) • (orthogonalProjection line[ℝ, X, Y] P : V) - P := by
  rw [reflection_apply', vsub_eq_sub, vadd_eq_add, two_smul]; abel

end Bridges

/-! ## Comparisons -/

-- thm:radical : blind_43 ↔ radical_center_concurrent
theorem r43_to_b : type_of% @CircleSystems.radical_center_concurrent.{u} → blind43_stmt.{u} := by
  intro hR V _ _ O₁ O₂ O₃ R₁ R₂ R₃ hV hO
  have : Fact (Module.finrank ℝ V = 2) := ⟨hV⟩
  simpa only [radicalAxis_eq] using hR R₁ R₂ R₃ hO

theorem b43_to_r : blind43_stmt.{u} → type_of% @CircleSystems.radical_center_concurrent.{u} := by
  intro hB V _ _ hF O₁ O₂ O₃ R₁ R₂ R₃ hO
  simpa only [radicalAxis_eq] using hB V O₁ O₂ O₃ R₁ R₂ R₃ hF.out hO

-- thm:coaxal : blind_46 ↔ pencil_through_common_point
theorem r46_to_b : type_of% @CircleSystems.pencil_through_common_point.{u} → blind46_stmt.{u} := by
  intro hR V _ _ O₁ O₂ X R₁ R₂ t h₁ h₂
  rw [pencil_identity, hR h₁ h₂ t, sub_self]

theorem b46_to_r : blind46_stmt.{u} → type_of% @CircleSystems.pencil_through_common_point.{u} := by
  intro hB V _ _ O₁ O₂ X R₁ R₂ h₁ h₂ t
  have := hB V O₁ O₂ X R₁ R₂ t h₁ h₂
  rw [pencil_identity] at this
  linarith

-- thm:johnson : blind_48 ↔ johnson_circle
theorem r48_to_b : type_of% @CircleSystems.johnson_circle.{u} → blind48_stmt.{u} := by
  intro hR V _ _ O₁ O₂ O₃ H R h₁ h₂ h₃
  exact hR h₁ h₂ h₃

theorem b48_to_r : blind48_stmt.{u} → type_of% @CircleSystems.johnson_circle.{u} := by
  intro hB V _ _ H O₁ O₂ O₃ R h₁ h₂ h₃
  exact hB V O₁ O₂ O₃ H R h₁ h₂ h₃

-- thm:johnson : blind_49 ↔ johnson_mem_circles.
-- The library lemma omits `[InnerProductSpace ℝ V]` (it holds in any normed group), so the
-- blind → real direction can only be proved for inner product spaces.
theorem r49_to_b : type_of% @CircleSystems.johnson_mem_circles.{u} → blind49_stmt.{u} := by
  intro hR V _ _ O₁ O₂ O₃ H R h₁ h₂ h₃
  obtain ⟨a1, a2⟩ := hR h₂ h₃
  obtain ⟨b1, b2⟩ := hR h₃ h₁
  obtain ⟨c1, c2⟩ := hR h₁ h₂
  exact ⟨a1, a2, b1, b2, c1, c2⟩

/-- `johnson_mem_circles` restricted to inner product spaces (the blind statement's setting). -/
def johnson_mem_circles_ips : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {H O₂ O₃ : V} {R : ℝ},
    dist H O₂ = R → dist H O₃ = R → dist (O₂ + O₃ - H) O₂ = R ∧ dist (O₂ + O₃ - H) O₃ = R

theorem b49_to_r_ips : blind49_stmt.{u} → johnson_mem_circles_ips.{u} := by
  intro hB V _ _ H O₂ O₃ R h₂ h₃
  obtain ⟨a1, a2, -⟩ := hB V O₂ O₂ O₃ H R h₂ h₂ h₃
  exact ⟨a1, a2⟩

theorem r_to_r_ips : type_of% @CircleSystems.johnson_mem_circles.{u} → johnson_mem_circles_ips.{u} :=
  fun h _ _ _ _ _ _ _ h₂ h₃ => h h₂ h₃

-- thm:johnson : blind_51 ↔ johnson_orthocenter
theorem r51_to_b : type_of% @CircleSystems.johnson_orthocenter.{u} → blind51_stmt.{u} := by
  intro hR V _ _ O₁ O₂ O₃ H R h₁ h₂ h₃
  obtain ⟨a, b, c⟩ := hR h₁ h₂ h₃
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [show H - (O₂ + O₃ - H) = -((O₂ + O₃ - H) - H) by abel,
      show O₁ + O₂ - H - (O₃ + O₁ - H) = -((O₃ + O₁ - H) - (O₁ + O₂ - H)) by abel, inner_neg_neg, a]
  · rw [show H - (O₃ + O₁ - H) = -((O₃ + O₁ - H) - H) by abel,
      show O₂ + O₃ - H - (O₁ + O₂ - H) = -((O₁ + O₂ - H) - (O₂ + O₃ - H)) by abel, inner_neg_neg, b]
  · rw [show H - (O₁ + O₂ - H) = -((O₁ + O₂ - H) - H) by abel,
      show O₃ + O₁ - H - (O₂ + O₃ - H) = -((O₂ + O₃ - H) - (O₃ + O₁ - H)) by abel, inner_neg_neg, c]

theorem b51_to_r : blind51_stmt.{u} → type_of% @CircleSystems.johnson_orthocenter.{u} := by
  intro hB V _ _ H O₁ O₂ O₃ R h₁ h₂ h₃
  obtain ⟨a, b, c⟩ := hB V O₁ O₂ O₃ H R h₁ h₂ h₃
  refine ⟨?_, ?_, ?_⟩
  · rw [show (O₂ + O₃ - H) - H = -(H - (O₂ + O₃ - H)) by abel,
      show O₃ + O₁ - H - (O₁ + O₂ - H) = -((O₁ + O₂ - H) - (O₃ + O₁ - H)) by abel, inner_neg_neg, a]
  · rw [show (O₃ + O₁ - H) - H = -(H - (O₃ + O₁ - H)) by abel,
      show O₁ + O₂ - H - (O₂ + O₃ - H) = -((O₂ + O₃ - H) - (O₁ + O₂ - H)) by abel, inner_neg_neg, b]
  · rw [show (O₁ + O₂ - H) - H = -(H - (O₁ + O₂ - H)) by abel,
      show O₂ + O₃ - H - (O₃ + O₁ - H) = -((O₃ + O₁ - H) - (O₂ + O₃ - H)) by abel, inner_neg_neg, c]

-- thm:simson : blind_52 ↔ simson_det_eq_circumcircle_power
theorem r52_to_b : type_of% @CircleSystems.simson_det_eq_circumcircle_power.{u} → blind52_stmt.{u} := by
  intro hR V _ _ β A B C O P D E F R hA hB hC hAB hBC hCA hD hE hF
  rw [foot_iff] at hD hE hF
  subst hD hE hF
  have := hR β (P := P) hA hB hC hAB hBC hCA
  simpa only [cross_eq, powPt_eq] using this

theorem b52_to_r : blind52_stmt.{u} → type_of% @CircleSystems.simson_det_eq_circumcircle_power.{u} := by
  intro hB V _ _ β A B C O P R hA hB' hC hAB hBC hCA
  have := hB V β A B C O P _ _ _ R hA hB' hC hAB hBC hCA (foot_proj P B C) (foot_proj P C A)
    (foot_proj P A B)
  simpa only [cross_eq, powPt_eq] using this

-- thm:simson : blind_53 ↔ simson_wallace
theorem r53_to_b : type_of% @CircleSystems.simson_wallace.{u} → blind53_stmt.{u} := by
  intro hR V _ _ A B C O P D E F R hV hA hB hC hAB hBC hCA hnc hD hE hF
  have : Fact (Module.finrank ℝ V = 2) := ⟨hV⟩
  rw [foot_iff] at hD hE hF
  subst hD hE hF
  exact hR hA hB hC hnc

theorem b53_to_r : blind53_stmt.{u} → type_of% @CircleSystems.simson_wallace.{u} := by
  intro hB V _ _ A B C O P R hF hA hB' hC hnc
  obtain ⟨hAB, hBC, hCA⟩ := ne_of_not_collinear hnc
  exact hB V A B C O P _ _ _ R hF.out hA hB' hC hAB hBC hCA hnc (foot_proj P B C) (foot_proj P C A)
    (foot_proj P A B)

-- thm:steinerline : blind_55 ↔ steiner_line
theorem r55_to_b : type_of% @CircleSystems.steiner_line.{u} → blind55_stmt.{u} := by
  intro hR V _ _ A B C O P D E F R hV hA hB hC hP hAB hBC hCA hD hE hF
  have : Fact (Module.finrank ℝ V = 2) := ⟨hV⟩
  rw [foot_iff] at hD hE hF
  subst hD hE hF
  have := hR hA hB hC hP hAB hBC hCA
  simpa only [reflection_eq] using this

theorem b55_to_r : blind55_stmt.{u} → type_of% @CircleSystems.steiner_line.{u} := by
  intro hB V _ _ A B C O P R hF hA hB' hC hP hAB hBC hCA
  have := hB V A B C O P _ _ _ R hF.out hA hB' hC hP hAB hBC hCA (foot_proj P B C)
    (foot_proj P C A) (foot_proj P A B)
  simpa only [reflection_eq] using this


/-! ## Pairs stated with Mathlib's `Affine.Triangle` -/

section Triangle
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Mathlib only: orthocenter = Monge point = `A + B + C − 2·circumcenter` (vector plane). -/
theorem orthocenter_formula (t : Affine.Triangle ℝ V) :
    t.orthocenter = t.points 0 + t.points 1 + t.points 2 - (2 : ℝ) • t.circumcenter := by
  rw [Affine.Triangle.orthocenter_eq_mongePoint,
    Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter, Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_card_ne_zero ℝ _ (by simp))]
  simp only [Finset.centroidWeights_apply, Finset.card_univ, Fintype.card_fin,
    vsub_eq_sub, vadd_eq_add]
  rw [Fin.sum_univ_three]
  norm_num
  change _ = t.points (0 : Fin 3) + t.points (1 : Fin 3) + t.points (2 : Fin 3) -
    (2 : ℝ) • t.circumcenter
  module

theorem span_top [Fact (Module.finrank ℝ V = 2)] (t : Affine.Triangle ℝ V) :
    affineSpan ℝ (Set.range t.points) = ⊤ := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_fin,
    (Fact.out : Module.finrank ℝ V = 2)]

end Triangle

/-- `johnson_orthocenter_eq` restated with its universe. -/
theorem b48_to_r_orthocenter_eq :
    blind48_stmt.{u} → type_of% @CircleSystems.johnson_orthocenter_eq.{u} := by
  intro hB V _ _ H O₁ O₂ O₃ R hF h₁ h₂ h₃ hind
  set t : Affine.Triangle ℝ V := ⟨_, hind⟩
  obtain ⟨d1, d2, d3⟩ := hB V O₁ O₂ O₃ H R h₁ h₂ h₃
  have hJ : O₁ + O₂ + O₃ - (2 : ℝ) • H = t.circumcenter := by
    apply t.eq_circumcenter_of_dist_eq (r := R)
    · rw [span_top t]; exact AffineSubspace.mem_top _ _ _
    · intro i; fin_cases i
      · exact d1
      · exact d2
      · exact d3
  refine ⟨hJ.symm, ?_⟩
  rw [orthocenter_formula, ← hJ]
  simp only [t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  module

-- thm:steinerline : blind_55 ↔ steiner_line_orthocenter
theorem b55_to_r_orthocenter :
    blind55_stmt.{u} → type_of% @CircleSystems.steiner_line_orthocenter.{u} := by
  intro hB V _ _ hF t P hP
  have hinj := t.independent.injective
  have hA := t.dist_circumcenter_eq_circumradius 0
  have hB' := t.dist_circumcenter_eq_circumradius 1
  have hC := t.dist_circumcenter_eq_circumradius 2
  have := hB V (t.points 0) (t.points 1) (t.points 2) t.circumcenter P _ _ _ t.circumradius hF.out
    hA hB' hC hP (fun h => by simpa using hinj h) (fun h => by simpa using hinj h)
    (fun h => by simpa using hinj h) (foot_proj P _ _) (foot_proj P _ _) (foot_proj P _ _)
  rw [orthocenter_formula]
  simpa only [reflection_eq] using this

theorem r55_orthocenter_to_b :
    type_of% @CircleSystems.steiner_line_orthocenter.{u} → blind55_stmt.{u} := by
  intro hR V _ _ A B C O P D E F R hV hA hB hC hP hAB hBC hCA hD hE hF
  have : Fact (Module.finrank ℝ V = 2) := ⟨hV⟩
  rw [foot_iff] at hD hE hF
  subst hD hE hF
  have hcos : Cospherical ({A, B, C} : Set V) := ⟨O, R, by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption⟩
  have hind := hcos.affineIndependent_of_ne hAB hCA.symm hBC
  set t : Affine.Triangle ℝ V := ⟨_, hind⟩
  have hdist : ∀ i, dist (t.points i) O = R := by
    intro i; fin_cases i
    · exact hA
    · exact hB
    · exact hC
  have hO : O = t.circumcenter := t.eq_circumcenter_of_dist_eq (by rw [span_top t]; trivial) hdist
  have hRr : R = t.circumradius := t.eq_circumradius_of_dist_eq (by rw [span_top t]; trivial) hdist
  have := hR t (P := P) (by rw [← hO, ← hRr]; exact hP)
  rw [orthocenter_formula, ← hO] at this
  simpa only [reflection_eq, t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using this

end L13JC

/-! ## Audit: no theorem of the paper's library occurs in any proof term of this file.
Collects, for every declaration of namespace `NS` defined in this file, all constants occurring
(transitively through other declarations of this file) in its value, and reports those that are
theorems of the library namespace `LIB`. The `type_of%` goals are types, not values, so library
theorem names there are not counted. Expected output: `library theorems used: []`. (Self-tested: a
declaration `(CircleSystems.johnson_reflection H O₁ O₂ O₃).1` IS reported.) -/
open Lean Meta Elab Command in
elab "#audit_lib " ns:ident lib:ident : command => do
  let env ← getEnv
  let nsN := ns.getId
  let libN := lib.getId
  let mine := env.constants.map₂.foldl (fun acc n _ => if nsN.isPrefixOf n then acc.push n else acc) #[]
  let mut bad : Array (Name × Name) := #[]
  let mut aux : Array Name := #[]
  for n in mine do
    let some ci := env.find? n | continue
    let some v := ci.value? (allowOpaque := true) | continue
    for c in v.getUsedConstants do
      if libN.isPrefixOf c then
        if let some (.thmInfo _) := env.find? c then
          -- compiler-generated pieces of a library *definition* (side proofs `_proof_N`,
          -- equation lemmas `eq_N` / `eq_def` used by `rw [def]`) count as unfolding it.
          let isDefAux : Bool := match c with
            | .str p s =>
              (s.startsWith "_proof_" || s.startsWith "eq_") &&
                (match env.find? p with | some (.defnInfo _) => true | _ => false)
            | _ => false
          if isDefAux then aux := aux.push c else bad := bad.push (n, c)
  logInfo m!"checked {mine.size} declarations; definition auxiliaries (unfolding only): {aux.toList.eraseDups}; library theorems used: {bad.toList}"

#audit_lib L13JC CircleSystems

#print axioms L13JC.r43_to_b
#print axioms L13JC.b43_to_r
#print axioms L13JC.r46_to_b
#print axioms L13JC.b46_to_r
#print axioms L13JC.r48_to_b
#print axioms L13JC.b48_to_r
#print axioms L13JC.r49_to_b
#print axioms L13JC.b49_to_r_ips
#print axioms L13JC.r51_to_b
#print axioms L13JC.b51_to_r
#print axioms L13JC.r52_to_b
#print axioms L13JC.b52_to_r
#print axioms L13JC.r53_to_b
#print axioms L13JC.b53_to_r
#print axioms L13JC.r55_to_b
#print axioms L13JC.b55_to_r
#print axioms L13JC.b48_to_r_orthocenter_eq
#print axioms L13JC.b55_to_r_orthocenter
#print axioms L13JC.r55_orthocenter_to_b
