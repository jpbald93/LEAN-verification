import Blundon

open Affine EuclideanGeometry

universe u v

/-- blind_11 verbatim (statement only). -/
def blind11_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P),
    let R := t.circumradius
    let r := t.inradius
    let s := (dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2) +
      dist (t.points 2) (t.points 0)) / 2
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2 ∧
    s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r)

def real11_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P),
    2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 -
        2 * (t.circumradius - 2 * t.inradius) *
          Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius) ≤
      Blundon.semiperimeter t ^ 2 ∧
    Blundon.semiperimeter t ^ 2 ≤
      2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 +
        2 * (t.circumradius - 2 * t.inradius) *
          Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius)

/-- sanity: real11_stmt is literally the type of `Blundon.blundon` -/
example : real11_stmt.{u, v} := fun t => Blundon.blundon t

theorem rb_11 : real11_stmt.{u, v} → blind11_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  exact h t

theorem br_11 : blind11_stmt.{u, v} → real11_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  exact h t
