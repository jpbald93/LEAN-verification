import Clifford

/-! L13 comparer scratch: blind_5 / blind_6 vs `Clifford.cliffordChain_four` / `_five`
(repo `~/clifford_j`).  Repo definitions unfolded: `Clifford.Chain`, `Clifford.IsGCircle`,
`Clifford.GenPosN`, `Clifford.CliffordChain`, `Clifford.second`.
Repo bridge lemmas used: `Clifford.transversal_iff`, `Clifford.genTriple_iff`. -/

open Affine EuclideanGeometry

noncomputable section

/-! Blind definitions, verbatim. -/

def BlindP (ci cj : ℂ) : ℂ :=
  ((starRingEnd ℂ) ci * cj - ci * (starRingEnd ℂ) cj) / ((starRingEnd ℂ) ci - (starRingEnd ℂ) cj)

inductive BlindGenCircle
  | circle (o : ℂ) (r : ℝ) (hr : 0 ≤ r)
  | line (p v : ℂ) (hv : v ≠ 0)

def BlindGenCircle.carrier : BlindGenCircle → Set ℂ
  | .circle o r _ => Metric.sphere o r
  | .line p v _ => {z | ∃ t : ℝ, z = p + t * v}

inductive BlindObj
  | pt (z : ℂ)
  | gc (g : BlindGenCircle)

def BlindChain : (n : ℕ) → (Fin n → ℂ) → BlindObj → Prop
  | 0, _, X => X = .pt 0
  | 1, c, X => X = .gc (.circle (c 0) ‖c 0‖ (norm_nonneg _))
  | 2, c, X => X = .pt (BlindP (c 0) (c 1))
  | n + 3, c, X =>
    if Odd (n + 3) then
      ∃ g : BlindGenCircle, X = .gc g ∧ ∀ i : Fin (n + 3), ∃ z ∈ g.carrier,
        BlindChain (n + 2) (fun j => c (i.succAbove j)) (.pt z)
    else
      ∃ z : ℂ, X = .pt z ∧ ∀ i : Fin (n + 3), ∃ g : BlindGenCircle, z ∈ g.carrier ∧
        BlindChain (n + 2) (fun j => c (i.succAbove j)) (.gc g)

def BlindGeneralPosition {n : ℕ} (c : Fin n → ℂ) : Prop :=
  (∀ i j : Fin n, i < j → ¬ Collinear ℝ ({0, c i, c j} : Set ℂ)) ∧
  (∀ i j k : Fin n, i < j → j < k →
    ¬ Collinear ℝ ({c i, c j, c k} : Set ℂ) ∧
    ¬ Collinear ℝ ({BlindP (c i) (c j), BlindP (c i) (c k), BlindP (c j) (c k)} : Set ℂ))

def BlindCliffordChain (n : ℕ) : Prop :=
  ∀ c : Fin n → ℂ, BlindGeneralPosition c → ∃ X : BlindObj, BlindChain n c X

/-! General position. -/

lemma transversal_symm {a b : ℂ} (h : Clifford.Transversal a b) : Clifford.Transversal b a := by
  unfold Clifford.Transversal at *
  intro e; apply h; rw [mul_comm, ← e, mul_comm]

lemma genpos_iff {n : ℕ} (c : Fin n → ℂ) : BlindGeneralPosition c ↔ Clifford.GenPosN c := by
  constructor
  · rintro ⟨h1, h2⟩
    have t : ∀ i j : Fin n, i < j → Clifford.Transversal (c i) (c j) :=
      fun i j hij => (Clifford.transversal_iff _ _).2 (h1 i j hij)
    refine ⟨fun i j hij => ?_, fun i j k hij hjk => ?_⟩
    · rcases lt_or_gt_of_ne hij with h | h
      · exact t i j h
      · exact transversal_symm (t j i h)
    · exact (Clifford.genTriple_iff (t i j hij) (t i k (hij.trans hjk)) (t j k hjk)).2
        (h2 i j k hij hjk)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => (Clifford.transversal_iff _ _).1 (h1 i j hij.ne), fun i j k hij hjk => ?_⟩
    exact (Clifford.genTriple_iff (h1 i j hij.ne) (h1 i k (hij.trans hjk).ne) (h1 j k hjk.ne)).1
      (h2 i j k hij hjk)

/-! Generalised circles. -/

lemma gcircle_carrier (g : BlindGenCircle) : Clifford.IsGCircle g.carrier := by
  cases g with
  | circle o r hr => exact Or.inl ⟨o, r, rfl⟩
  | line p v hv =>
    refine Or.inr ⟨p, v, hv, ?_⟩
    ext z; simp [BlindGenCircle.carrier, Complex.real_smul]

lemma gcircle_of {Y : Set ℂ} (h : Clifford.IsGCircle Y) (hne : Y.Nonempty) :
    ∃ g : BlindGenCircle, Y = g.carrier := by
  rcases h with ⟨o, r, rfl⟩ | ⟨p, v, hv, rfl⟩
  · obtain ⟨x, hx⟩ := hne
    have hr : 0 ≤ r := by rw [← Metric.mem_sphere.1 hx]; exact dist_nonneg
    exact ⟨.circle o r hr, rfl⟩
  · refine ⟨.line p v hv, ?_⟩
    ext z; simp [BlindGenCircle.carrier, Complex.real_smul]

/-! Level-by-level translation. -/

lemma bc3 (c : Fin 3 → ℂ) (g : BlindGenCircle) :
    BlindChain 3 c (.gc g) ↔ (∀ i : Fin 3, ∃ z ∈ g.carrier,
      z = BlindP (c (i.succAbove 0)) (c (i.succAbove 1))) := by
  simp only [BlindChain, show Odd (0 + 3) by decide, if_true, BlindObj.gc.injEq, BlindObj.pt.injEq]
  constructor
  · rintro ⟨g', rfl, h⟩; exact h
  · intro h; exact ⟨g, rfl, h⟩

lemma rc3 (c : Fin 3 → ℂ) (Y : Set ℂ) :
    Clifford.Chain 3 c Y ↔ Clifford.IsGCircle Y ∧ (∀ i : Fin 3, ∃ p,
      p = Clifford.second (c (i.succAbove 0)) (c (i.succAbove 1)) ∧ p ∈ Y) := by
  simp only [Clifford.Chain, Nat.zero_mod, if_true, Function.comp, Set.singleton_eq_singleton_iff]

lemma l3_fw (c : Fin 3 → ℂ) (g : BlindGenCircle) (h : BlindChain 3 c (.gc g)) :
    Clifford.Chain 3 c g.carrier := by
  rw [bc3] at h; rw [rc3]
  exact ⟨gcircle_carrier g, fun i => by obtain ⟨z, hz, rfl⟩ := h i; exact ⟨_, rfl, hz⟩⟩

lemma l3_bw (c : Fin 3 → ℂ) (Y : Set ℂ) (h : Clifford.Chain 3 c Y) :
    ∃ g : BlindGenCircle, Y = g.carrier ∧ BlindChain 3 c (.gc g) := by
  rw [rc3] at h
  obtain ⟨hY, hp⟩ := h
  obtain ⟨p, -, hp0⟩ := hp 0
  obtain ⟨g, rfl⟩ := gcircle_of hY ⟨p, hp0⟩
  refine ⟨g, rfl, (bc3 c g).2 fun i => ?_⟩
  obtain ⟨q, rfl, hq⟩ := hp i
  exact ⟨_, hq, rfl⟩

lemma bc3_obj (c : Fin 3 → ℂ) (X : BlindObj) (h : BlindChain 3 c X) : ∃ g, X = .gc g := by
  simp only [BlindChain, show Odd (0 + 3) by decide, if_true] at h
  obtain ⟨g, rfl, -⟩ := h; exact ⟨g, rfl⟩

lemma bc4 (c : Fin 4 → ℂ) (X : BlindObj) :
    BlindChain 4 c X ↔ ∃ z : ℂ, X = .pt z ∧ ∀ i : Fin 4, ∃ g : BlindGenCircle, z ∈ g.carrier ∧
        BlindChain 3 (fun j => c (i.succAbove j)) (.gc g) := by
  simp only [BlindChain.eq_4, show ¬ Odd (1 + 3) by decide, if_false]

lemma rc4 (c : Fin 4 → ℂ) (Y : Set ℂ) :
    Clifford.Chain 4 c Y ↔ ∃ p, Y = {p} ∧ ∀ i : Fin 4, ∃ Z, Clifford.Chain 3 (c ∘ i.succAbove) Z ∧ p ∈ Z := by
  simp only [Clifford.Chain.eq_4, show ¬ (1 % 2 = 0) by decide, if_false]

lemma l4_fw (c : Fin 4 → ℂ) (z : ℂ) (h : BlindChain 4 c (.pt z)) : Clifford.Chain 4 c {z} := by
  rw [bc4] at h; rw [rc4]
  obtain ⟨z', hz', h⟩ := h
  cases hz'
  exact ⟨z, rfl, fun i => by
    obtain ⟨g, hg, hc⟩ := h i
    exact ⟨g.carrier, l3_fw _ g hc, hg⟩⟩

lemma l4_bw (c : Fin 4 → ℂ) (Y : Set ℂ) (h : Clifford.Chain 4 c Y) :
    ∃ z, Y = {z} ∧ BlindChain 4 c (.pt z) := by
  rw [rc4] at h
  obtain ⟨p, rfl, h⟩ := h
  refine ⟨p, rfl, (bc4 c _).2 ⟨p, rfl, fun i => ?_⟩⟩
  obtain ⟨Z, hZ, hp⟩ := h i
  obtain ⟨g, rfl, hg⟩ := l3_bw _ Z hZ
  exact ⟨g, hp, hg⟩

lemma bc5 (c : Fin 5 → ℂ) (X : BlindObj) :
    BlindChain 5 c X ↔ ∃ g : BlindGenCircle, X = .gc g ∧ ∀ i : Fin 5, ∃ z ∈ g.carrier,
        BlindChain 4 (fun j => c (i.succAbove j)) (.pt z) := by
  simp only [BlindChain.eq_4, show Odd (2 + 3) by decide, if_true]

lemma rc5 (c : Fin 5 → ℂ) (Y : Set ℂ) :
    Clifford.Chain 5 c Y ↔ Clifford.IsGCircle Y ∧
      ∀ i : Fin 5, ∃ p, Clifford.Chain 4 (c ∘ i.succAbove) {p} ∧ p ∈ Y := by
  simp only [Clifford.Chain.eq_4, show (2 % 2 = 0) by decide, if_true]

/-- blind_5 / blind_6 verbatim -/
def blind5_stmt : Prop := BlindCliffordChain 4
def blind6_stmt : Prop := BlindCliffordChain 5

theorem rb_5 : (type_of% @Clifford.cliffordChain_four) → blind5_stmt := by
  intro h c hc
  obtain ⟨Y, hY⟩ := h c ((genpos_iff c).1 hc)
  obtain ⟨z, -, hz⟩ := l4_bw c Y hY
  exact ⟨_, hz⟩

theorem br_5 : blind5_stmt → (type_of% @Clifford.cliffordChain_four) := by
  intro h c hc
  obtain ⟨X, hX⟩ := h c ((genpos_iff c).2 hc)
  obtain ⟨z, rfl, -⟩ := (bc4 c X).1 hX
  exact ⟨_, l4_fw c z hX⟩

theorem rb_6 : (type_of% @Clifford.cliffordChain_five) → blind6_stmt := by
  intro h c hc
  obtain ⟨Y, hY⟩ := h c ((genpos_iff c).1 hc)
  rw [rc5] at hY
  obtain ⟨hG, hp⟩ := hY
  obtain ⟨p, -, hp0⟩ := hp 0
  obtain ⟨g, rfl⟩ := gcircle_of hG ⟨p, hp0⟩
  refine ⟨.gc g, (bc5 c _).2 ⟨g, rfl, fun i => ?_⟩⟩
  obtain ⟨q, hq, hqg⟩ := hp i
  obtain ⟨z, hz, hb⟩ := l4_bw _ _ hq
  rw [Set.singleton_eq_singleton_iff] at hz
  subst hz
  exact ⟨q, hqg, hb⟩

theorem br_6 : blind6_stmt → (type_of% @Clifford.cliffordChain_five) := by
  intro h c hc
  obtain ⟨X, hX⟩ := h c ((genpos_iff c).2 hc)
  obtain ⟨g, rfl, hg⟩ := (bc5 c X).1 hX
  refine ⟨g.carrier, (rc5 c _).2 ⟨gcircle_carrier g, fun i => ?_⟩⟩
  obtain ⟨z, hz, hb⟩ := hg i
  exact ⟨z, l4_fw _ z hb, hz⟩
