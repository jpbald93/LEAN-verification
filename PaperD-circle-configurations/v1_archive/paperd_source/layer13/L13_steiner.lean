import SteinerLehmus

open Affine EuclideanGeometry

universe u v

def blind12_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (A B C E F : P) (hABC : AffineIndependent ℝ ![A, B, C])
    (hE : E ∈ affineSegment ℝ A C) (hEb : ∠ A B E = ∠ E B C)
    (hF : F ∈ affineSegment ℝ A B) (hFb : ∠ A C F = ∠ F C B)
    (h : dist B E = dist C F), dist A B = dist A C

def real12_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {A B C E F : P} (hABC : ¬Collinear ℝ ({A, B, C} : Set P))
    (hE : Wbtw ℝ A E C) (hbisB : ∠ A B E = ∠ E B C)
    (hF : Wbtw ℝ A F B) (hbisC : ∠ A C F = ∠ F C B)
    (heq : dist B E = dist C F), dist A B = dist A C

-- typing check only (not used in rb/br)
example : real12_stmt.{u, v} := @SteinerLehmus.steiner_lehmus

theorem rb_12 : real12_stmt.{u, v} → blind12_stmt.{u, v} := by
  intro h V P _ _ _ _ A B C E F hABC hE hEb hF hFb hd
  exact h (affineIndependent_iff_not_collinear_set.mp hABC) hE hEb hF hFb hd

theorem br_12 : blind12_stmt.{u, v} → real12_stmt.{u, v} := by
  intro h V P _ _ _ _ A B C E F hABC hE hEb hF hFb hd
  exact h A B C E F (affineIndependent_iff_not_collinear_set.mpr hABC) hE hEb hF hFb hd
