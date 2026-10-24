# REPORT — Paper F, part 1: the inscribed parabola of the complete quadrilateral

Repo: `jack:~/quadparabola` (namespace `QuadMiquel`, Lean v4.33.1, Mathlib pinned, no `lake update` / cache get).
New file: **`QuadMiquel/Parabola.lean`** (602 lines). No existing `.lean` file was edited.
Root file: one line, `import QuadMiquel.Parabola`, appended at the end of `QuadMiquel.lean`. `gate.sh`: only the `REQUIRED=` line changed (30 names appended).

## Result summary

| Target | Status |
|---|---|
| F1 coordinate form (all three `cr (Hᵢ−H₄)(R_k−H₄)=0`, every k) | **proved** |
| F1 Mathlib form (`R_k ∈ affineSpan ℝ {H₁,H₂,H₃,H₄}`, `Collinear ℝ {R₁,…,R₄}`) | **proved** |
| F2 `M ∉ affineSpan ℝ {H₁,…,H₄}` | **proved**, with no extra hypothesis |
| F3 the parabola (definition via `Metric.infDist`, bridge to the point-direction form, tangency of each `L_k` as `∃!`) | **proved** for k = 1..4 |
| F4 the Newton–Gauss line is perpendicular to the directrix, i.e. parallel to the axis (stated with `inner ℝ`) | **proved** |
| F4 explicit tangency points `Q_k` / vertex | not stated as separate theorems. `Q_k` is constructed explicitly inside `existsUnique_parabola` (`L.p + r·L.d` with `r = ⟨W, R−L.p⟩/⟨W, L.d⟩`), but there is no standalone named lemma for it |

`bash gate.sh` → **`PASS (92 declarations, standard axioms only)`** (62 pre-existing + 30 new; every one depends only on `[propext, Classical.choice, Quot.sound]`).
`bash tests/tamper.sh` → **`ALL TAMPERING TESTS REJECTED`**.

## Definitions (QuadMiquel/Parabola.lean)

```lean
-- :16
noncomputable def reflPt (z : ℂ) (L : Line) : ℂ := 2 * foot z L - z
-- :19   (the directrix = orthocentre line)
noncomputable def orthoLine (L₁ L₂ L₃ L₄ : Line) : AffineSubspace ℝ ℂ :=
  affineSpan ℝ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),      -- H₁
    ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),                   -- H₂
    ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),                   -- H₃
    ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ)          -- H₄
-- :26
def OnParabola (f : ℂ) (S : AffineSubspace ℝ ℂ) (z : ℂ) : Prop :=
  dist z f = Metric.infDist z (S : Set ℂ)
-- :30
def Tangent (L : Line) (f : ℂ) (S : AffineSubspace ℝ ℂ) : Prop :=
  ∃! z, z ∈ L.carrier ∧ OnParabola f S z
```
`orthoLine` is a pure abbreviation for the Mathlib `affineSpan`. The headline F1/F2 results are also restated with the `affineSpan` spelled out in full (see below).

## Main statements (file:line)

Below, `M = miquelPt L₁ L₂ L₃ L₄`, `F_k = foot M L_k`, `W = F₂ − F₁` (the Simson direction), and `Hᵢ` as above. Every theorem assumes `h : GenPos L₁ L₂ L₃ L₄`.

**F1**
* `reflPt_cr` (:285): `cr W (reflPt M L_k − H₄) = 0` for k = 1,2,3,4.
* `reflections_collinear_orthos` (:318), `(L) (hL : L = L₁ ∨ L = L₂ ∨ L = L₃ ∨ L = L₄)`:
  `cr (H₃ − H₄) (reflPt M L − H₄) = 0 ∧ cr (H₁ − H₄) (reflPt M L − H₄) = 0 ∧ cr (H₂ − H₄) (reflPt M L − H₄) = 0`.
  This is meaningful even when `H₃ = H₄`, because it comes from `cr W (·) = 0` with `W ≠ 0`.
* `reflPt_mem_orthoLine` (:341): `reflPt M L_k ∈ orthoLine L₁ L₂ L₃ L₄` for k = 1..4.
* `reflections_mem_affineSpan` (:573): `∀ L ∈ ({L₁,L₂,L₃,L₄} : Set Line), reflPt M L ∈ affineSpan ℝ {H₁,H₂,H₃,H₄}`.
* `reflections_collinear` (:350): `Collinear ℝ {reflPt M L₁, reflPt M L₂, reflPt M L₃, reflPt M L₄}`.

**F2**
* `miquel_cr_ne` (:375): `cr W (M − H₄) ≠ 0`.
* `miquel_not_mem_orthoLine` (:396): `M ∉ orthoLine L₁ L₂ L₃ L₄`.
* `miquel_not_mem_affineSpan` (:589): `M ∉ affineSpan ℝ {H₁,H₂,H₃,H₄}`.

**F3**
* `infDist_line` (:140): `W ≠ 0 → Metric.infDist z line[ℝ, h₀, h₀ + W] = |cr W (z − h₀)| / ‖W‖`.
* `onParabola_line_iff` (:598): `OnParabola f line[ℝ,h₀,h₀+W] z ↔ dist z f = |cr W (z − h₀)| / ‖W‖`. This bridges the two forms.
* `orthoLine_eq` (:242): `orthoLine … = line[ℝ, H₄, H₄ + W]`. `mem_orthoLine` (:268) and `infDist_orthoLine` (:275) follow from it.
* `existsUnique_parabola` (:196) is the abstract tangency lemma. If `R` is on the directrix, `dist z f = dist z R` on `L`, and `L` is not perpendicular to the directrix, then `∃! z ∈ L` on the parabola.
* `dist_reflPt` (:167): each point of `L` is equidistant from `x` and `reflPt x L`.
* `line_not_perp` (:404): `(conj W * L_k.d).re ≠ 0`. Proof: if `L_k` were perpendicular to the directrix, then `M − R_k` would be parallel to it, so `M` would lie on it, contradicting F2.
* **`parabola_tangent`** (:428), `(L) (hL : L = L₁ ∨ … ∨ L = L₄)`: `Tangent L M (orthoLine L₁ L₂ L₃ L₄)`.
  It is also stated separately as `parabola_tangent₁ … ₄` (:446, :449, :453, :457).

**F4**
* `newton_perp_cr` (:539): `inner ℝ W (N₂ − N₁) = 0 ∧ inner ℝ W (N₃ − N₁) = 0`, where `N₁ = (A12+A34)/2`, `N₂ = (A13+A24)/2`, `N₃ = (A14+A23)/2`.
* `newton_perp_orthoLine` (:556): for all `x y ∈ orthoLine`, `inner ℝ (x − y) (N₂ − N₁) = 0 ∧ inner ℝ (x − y) (N₃ − N₁) = 0`. So the Newton–Gauss line is perpendicular to the directrix, which means it is parallel to the axis of the parabola (the axis is the perpendicular to the directrix through `M`).

**Frame lemmas** (normal-frame method; `conj` treated as an independent atom; closed by `field_simp; ring`):
* `parR1` (:39): `R₁ = u·M̄/ū` lies on `H₄ + ℝW`.
* `parM` (:52): `W̄(M−H₄) − W(M̄−H̄₄) = −(s−1)(s−t)(t−1)K³ / (2E²D²)`, which is nonzero under GenPos.
* `newton2` (:466), `newton3` (:478); `parab_frame` (:69), `newton_frame` (:493).

**Proof route for F1.** The frame identity `parR1` gives `R₁` on `H₄ + ℝW`. Since `R_k − R₁ = 2(F_k − F₁) ∈ ℝW` (`simson_cr`), the other three `R_k` follow, which avoids three more frame computations. The three-orthocentre form then follows from `steiner_parallel_all`.

## Numeric checks (scratch/)

* `scratch/sym.py` (sympy, exact over ℚ(u,ū,v,v̄,s,t)):
  * `R₁ − u·M̄/ū ≡ 0`
  * `cr_W(R₁ − H₄) ≡ 0`
  * `cr_W(M − H₄) = −(s−1)(s−t)(t−1)(V u − U v)³ / (2E²D²)`
* `scratch/newton.py` (sympy): `W̄(N₂−N₁) + W(N̄₂−N̄₁) ≡ 0`, and the same for `N₃`.
* `scratch/check.py` (mpmath at 50 digits, using the library's raw definitions `meet/circ/ortho/foot/miquelPt`). It checks every F1 statement (all `cr(Hᵢ−H₄, R_k−H₄)`), F2 (distance from `M` to the directrix), F3 (the tangency point has residual `dist(Q,M) − dist(Q,dir)` ≈ 0, and `dist(z,M) − dist(z,dir) > 0` at sampled `z ≠ Q` on `L_k`), and non-perpendicularity of each `L_k` to the directrix.
  * 200 random configurations: max residual 1.3e-42, tangency residual 1.4e-46, min gap > 0, min dist(M, directrix) 6.6e-5 > 0.
  * 90 forced near-degenerate configurations (`L₁ ⊥ L₂`, so `H₃ = H₄`; nearly parallel `L₃ ∥ L₄`; nearly concurrent triples): max residual 1.5e-38. All nondegeneracy quantities stay positive and shrink only as the configuration approaches a GenPos violation.

**FINDINGS.** No planned statement was false, and no extra hypothesis was needed.
* F2 holds under `GenPos` alone: by the factorisation above, `M` is on the directrix only if `s = 1`, `t = 1`, `s = t` or `K = 0`, and GenPos excludes each of these.
* "No `L_k` is perpendicular to the directrix" is a consequence of F2, so it also needs no hypothesis.
* The `L₁ ⊥ L₂` case (where `H₃ = H₄`) is covered, because every statement is phrased through `W ≠ 0`, not through `H₃ − H₄`.

## REQUIRED names added to gate.sh (30)
QuadMiquel.reflPt_cr QuadMiquel.reflections_collinear_orthos QuadMiquel.reflPt_mem_orthoLine QuadMiquel.reflections_mem_affineSpan QuadMiquel.reflections_collinear QuadMiquel.miquel_cr_ne QuadMiquel.miquel_not_mem_orthoLine QuadMiquel.miquel_not_mem_affineSpan QuadMiquel.parabola_tangent QuadMiquel.parabola_tangent₁ QuadMiquel.parabola_tangent₂ QuadMiquel.parabola_tangent₃ QuadMiquel.parabola_tangent₄ QuadMiquel.existsUnique_parabola QuadMiquel.infDist_line QuadMiquel.infDist_orthoLine QuadMiquel.onParabola_line_iff QuadMiquel.orthoLine_eq QuadMiquel.mem_orthoLine QuadMiquel.dist_reflPt QuadMiquel.line_not_perp QuadMiquel.parab_frame QuadMiquel.parR1 QuadMiquel.parM QuadMiquel.cr_abs_eq_iff QuadMiquel.newton2 QuadMiquel.newton3 QuadMiquel.newton_frame QuadMiquel.newton_perp_cr QuadMiquel.newton_perp_orthoLine

## Gate / tamper
```
PASS (92 declarations, standard axioms only)
ALL TAMPERING TESTS REJECTED
```

## Hashes (sha256)
Before (scratch/hash_before.txt):
```
95b548bc2ee7b7c87bbaa7ff03c74cf3722ce41ad2a26d634d9cf97101b47938  QuadMiquel/Algebra.lean
f7b4da7d2abf6c1f66b987defd25bf99be4bf10a6cf081c97af51dd1f52dcf12  QuadMiquel/Basic.lean
fb6f3e39230d5279dee671a62c70748ed1969d32df77815ba49f3145b68b29fa  QuadMiquel/Bridge.lean
1e7cbfc90348e6884806654ff0c60085c6b3d807a6c2dec15aa7d3e126703fc8  QuadMiquel/Frame.lean
5ce67f6891f4ec1c36c4ff6f1a789f076bef4fa567a579f63c03d7efa9f785a5  QuadMiquel/Miquel.lean
ea33070625a616859d0ac8e145c1fe6224af0f2c9bbc28a84f1e4505f9d49e5f  QuadMiquel/Parallel.lean
69b49c142ec7435ebfbea2fb2851f66a20c96fbdb9e48be3e67ecc0fae2936ce  QuadMiquel/Simson.lean
40e264fd0c8b0dd94ffdc95852d046541c22f480805c1d523fccdf6bc2bf67b8  QuadMiquel.lean
321aa825e3ded37a42f239c6ad18f5560fa634009f73d7fc3bf988f80411bc8c  gate.sh
5da507d51bdc4b18c7f4e11a3d25fd967b0fcb57bd972f9fcd3ca481bef32751  tests/tamper.sh
7241a353c784648d4845a08f094acb5899de8f9d92d8a53652db83ba4bcc1903  lakefile.toml
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
```
After (scratch/hash_after.txt):
```
95b548bc2ee7b7c87bbaa7ff03c74cf3722ce41ad2a26d634d9cf97101b47938  QuadMiquel/Algebra.lean
f7b4da7d2abf6c1f66b987defd25bf99be4bf10a6cf081c97af51dd1f52dcf12  QuadMiquel/Basic.lean
fb6f3e39230d5279dee671a62c70748ed1969d32df77815ba49f3145b68b29fa  QuadMiquel/Bridge.lean
1e7cbfc90348e6884806654ff0c60085c6b3d807a6c2dec15aa7d3e126703fc8  QuadMiquel/Frame.lean
5ce67f6891f4ec1c36c4ff6f1a789f076bef4fa567a579f63c03d7efa9f785a5  QuadMiquel/Miquel.lean
ea33070625a616859d0ac8e145c1fe6224af0f2c9bbc28a84f1e4505f9d49e5f  QuadMiquel/Parallel.lean
69b49c142ec7435ebfbea2fb2851f66a20c96fbdb9e48be3e67ecc0fae2936ce  QuadMiquel/Simson.lean
e57f46fccd5600d5482f2eb2a5359c76feca68261e1caadc44952219a5ff6e39  QuadMiquel.lean
e30b3651c2192694c46f249d9ea8ed5e43d8daceded8507ee54a232b260ef22b  gate.sh
5da507d51bdc4b18c7f4e11a3d25fd967b0fcb57bd972f9fcd3ca481bef32751  tests/tamper.sh
7241a353c784648d4845a08f094acb5899de8f9d92d8a53652db83ba4bcc1903  lakefile.toml
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
```
The seven pre-existing library files, tests/tamper.sh, lakefile.toml and lean-toolchain are identical. QuadMiquel.lean differs only by the appended import line: without it, it hashes back to 40e264fd…. gate.sh differs only in REQUIRED: with the 30 new names removed, it hashes back to 321aa825….
New file: QuadMiquel/Parabola.lean bd38d47896239808e8a3375d1eb53cc8032502845fab4ac177770d0508a7cbf2

## Not reached / caveats
* There is no separate named theorem for the tangency points `Q_k` or for the vertex of the parabola. `Q_k` only appears as the explicit witness inside `existsUnique_parabola`.
* `Tangent` means "exactly one common point". This is the right notion for a parabola and a non-axis-parallel line. Lines parallel to the axis also meet the parabola exactly once; `line_not_perp` shows that none of the four `L_k` is such a line.
* Build warnings: none in Parabola.lean.
