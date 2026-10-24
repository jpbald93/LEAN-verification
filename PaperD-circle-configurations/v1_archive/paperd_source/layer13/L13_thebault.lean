import Thebault3

/-! L13 comparer scratch: blind_9 vs `Thebault3.sawayama_thebault`.
Repo definitions used: `Thebault3.IsThebaultCircle`, `Thebault3.tri` (unfolded only). -/

open Affine EuclideanGeometry

abbrev BlindPlane := EuclideanSpace ℝ (Fin 2)

/-- verbatim from the blind file -/
def BlindThebaultCentre (t : Affine.Triangle ℝ BlindPlane) (D Y P : BlindPlane) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    Metric.infDist P (line[ℝ, t.points 0, D] : Set BlindPlane) = r ∧
    Metric.infDist P (line[ℝ, t.points 1, t.points 2] : Set BlindPlane) = r ∧
    dist P t.circumcenter = t.circumradius - r ∧
    (line[ℝ, t.points 0, D]).SSameSide P Y ∧
    (line[ℝ, t.points 1, t.points 2]).SSameSide P (t.points 0)

/-- blind_9 verbatim. -/
def blind9_stmt : Prop :=
  ∀ (t : Affine.Triangle ℝ BlindPlane) (D : BlindPlane)
    (hD : Sbtw ℝ (t.points 1) D (t.points 2)) (P Q : BlindPlane)
    (hP : BlindThebaultCentre t D (t.points 1) P)
    (hQ : BlindThebaultCentre t D (t.points 2) Q),
    Collinear ℝ ({P, Q, t.incenter} : Set BlindPlane)

lemma tri_eq (t : Affine.Triangle ℝ BlindPlane)
    (h : AffineIndependent ℝ ![t.points 0, t.points 1, t.points 2]) :
    Thebault3.tri (t.points 0) (t.points 1) (t.points 2) h = t := by
  ext i : 2
  fin_cases i <;> rfl

lemma indep (t : Affine.Triangle ℝ BlindPlane) :
    AffineIndependent ℝ ![t.points 0, t.points 1, t.points 2] := by
  have : t.points = ![t.points 0, t.points 1, t.points 2] := by
    ext i : 1; fin_cases i <;> rfl
  rw [← this]; exact t.independent

theorem rb_9 : (type_of% @Thebault3.sawayama_thebault) → blind9_stmt := by
  intro h t D hD P Q hP hQ
  have := h (t.points 0) (t.points 1) (t.points 2) D P Q (indep t) hD
    (by unfold Thebault3.IsThebaultCircle; rw [tri_eq]; exact hP)
    (by unfold Thebault3.IsThebaultCircle; rw [tri_eq]; exact hQ)
  rwa [tri_eq] at this

theorem br_9 : blind9_stmt → (type_of% @Thebault3.sawayama_thebault) := by
  intro h A B C D P Q hi hD hP hQ
  exact h (Thebault3.tri A B C hi) D hD P Q hP hQ
