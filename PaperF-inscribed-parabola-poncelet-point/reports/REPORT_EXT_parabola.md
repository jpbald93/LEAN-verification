# REPORT_EXT — Paper F extension, Task 1 (quadparabola_ext)

Repo: `john:~/lean/quadparabola_ext`, a copy of `~/lean/quadparabola`; the original is untouched.
* **New file:** `QuadMiquel/ParabolaPoints.lean` (277 lines).
* `QuadMiquel.lean`: one line appended, `import QuadMiquel.ParabolaPoints`.
* `gate.sh`: only line 15 (`REQUIRED=`) changed, checked by diffing every other line against the original.
* No existing `.lean` file was edited. There is no sorry, admit, axiom, set_option, macro or notation.

## Result
* **Gate:** `PASS (110 declarations, standard axioms only)` (92 old + 18 new). Log: `scratch/ext_gate.log`.
* **Tamper:** `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, wrap, falsehyp). Log: `scratch/ext_tamper.log`.
* **Targets:**
  * P1: proved.
  * P2: proved, plus a closest-point theorem and an axis-perpendicularity lemma.
  * P3: stated as `lambert`, with a caveat (see P3 below).

## Definitions (`QuadMiquel/ParabolaPoints.lean`)
* `:20` `dirW L₁ L₂ L₃ L₄ := foot M L₂ − foot M L₁`: the Simson direction W. Here M is `miquelPt L₁ L₂ L₃ L₄`.
* `:24` `directrix L₁ L₂ L₃ L₄ : Line := ⟨H₄, dirW …⟩`, where H₄ = `ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)`.
* `:28` `perpMeet L W R := L.p + ((conj W * (R − L.p)).re / (conj W * L.d).re) * L.d`. This is exactly the witness used inside `existsUnique_parabola`: the point of L on the perpendicular to W through R.
* `:32` **`tanPt L L₁ L₂ L₃ L₄ := perpMeet L (dirW …) (reflPt M L)`**
* `:36` `axisLine L₁ L₂ L₃ L₄ : Line := ⟨M, I * dirW …⟩`: the line through the focus, perpendicular to the directrix.
* `:40` **`vertex L₁ L₂ L₃ L₄ := (M + foot M (directrix …)) / 2`**

## Main theorems
**P1**
* `:134` `tanPt_mem (L L₁ L₂ L₃ L₄ : Line) : tanPt L L₁ L₂ L₃ L₄ ∈ L.carrier`. This holds unconditionally.
* `:138` `tanPt_onParabola (h : GenPos L₁ L₂ L₃ L₄) (L) (hL : L = L₁ ∨ L = L₂ ∨ L = L₃ ∨ L = L₄) : OnParabola (miquelPt L₁ L₂ L₃ L₄) (orthoLine L₁ L₂ L₃ L₄) (tanPt L L₁ L₂ L₃ L₄)`
* `:144` `tanPt_unique (h) (L) (hL) : ∀ z, z ∈ L.carrier → OnParabola (miquelPt …) (orthoLine …) z → z = tanPt L L₁ L₂ L₃ L₄`
* `:151` `tanPt_all (h) : ∀ L ∈ {L₁, L₂, L₃, L₄}, tanPt … ∈ L.carrier ∧ OnParabola … ∧ ∀ z, …`
* Key lemmas:
  * `:59` `perpMeet_spec`: the explicit-witness strengthening of `existsUnique_parabola`, with the same hypotheses.
  * `:49` `perpMeet_perp`
  * `:113` `tanPt_spec`
  * `:106` `onParabola_iff`

**P2**
* `:224` `vertex_onParabola (h : GenPos …) : OnParabola (miquelPt …) (orthoLine …) (vertex L₁ L₂ L₃ L₄)`
* `:213` `dist_vertex (h) : dist (vertex …) (miquelPt …) = Metric.infDist (miquelPt …) (orthoLine … : Set ℂ) / 2`
* `:246` `vertex_closest (h) (hz : OnParabola (miquelPt …) (orthoLine …) z) : infDist (vertex …) (orthoLine …) ≤ infDist z (orthoLine …)`: the vertex is the point of the parabola closest to the directrix.
* `:185` `vertex_mem_axis : vertex … ∈ (axisLine …).carrier`
* `:205` `axis_perp : (conj (axisLine …).d * (directrix …).d).re = 0`
* Key lemmas:
  * `:173` `infDist_focus`: the distance from the focus to the directrix equals `dist M (foot M directrix)`.
  * `:87` `norm_sub_foot`
  * `:163` `directrix_carrier`: `(directrix …).carrier = orthoLine …`.
  * `:168` `foot_directrix_mem`

**P3**
* `:264` `lambert (h : GenPos …)` states the conjunction of:
  * `∀ L ∈ {L₁,L₂,L₃,L₄}, Tangent L (miquelPt …) (orthoLine …)`, and
  * the four memberships of `miquel`: M lies on the circumcircle of each of T₁ … T₄.

  The proof is one line: `⟨fun L hL => parabola_tangent h L (by simpa using hL), miquel h⟩`.
* **Honesty note.** This is a genuine restatement of Lambert's theorem *for the parabola constructed here*: the focus of this parabola, which is tangent to all four lines, lies on every circumcircle. It does **not** prove the classical uniqueness: that *every* parabola tangent to the four lines has this focus. Uniqueness of the inscribed parabola is not formalised. If the theorem is read as being about "the" parabola, it depends on that missing uniqueness.

## Numerics (`scratch/num.py`, `scratch/num2.py`; mpmath at 50 digits)
* Setup: 300 random line configurations. Every 50th configuration is near-degenerate, with L₂ nearly parallel to L₁ (relative perturbation 1e-6).
* tanPt on L: max residual 2.1e-44.
* tanPt on the parabola (relative): 3.9e-37.
* Vertex on the parabola: 6.7e-45.
* `dist V M = d(M, directrix)/2`: 3.2e-45.
* Axis ⟂ directrix and H₁ on the directrix: 3.8e-36.
* Uniqueness probe: at four other points of L, `dist − distline` was evaluated. It was always > 0. It got as small as 1e-25 only in the near-degenerate configurations, where the tangency point is extremely far away. The value scales as k² along L, which is the expected behaviour at a tangency, so this is not a counterexample.
* **Findings:** none. Every statement held as stated, with no extra hypotheses. (`tanPt_mem` and `vertex_mem_axis` hold even without GenPos.)

## REQUIRED names added (18, all `QuadMiquel.`-qualified)
tanPt_mem tanPt_onParabola tanPt_unique tanPt_all tanPt_spec perpMeet_spec perpMeet_perp norm_sub_foot onParabola_iff directrix_carrier foot_directrix_mem infDist_focus vertex_mem_axis axis_perp dist_vertex vertex_onParabola vertex_closest lambert

## Hashes (sha256). Pre-existing library files: identical before and after
```
95b548bc2ee7b7c87bbaa7ff03c74cf3722ce41ad2a26d634d9cf97101b47938  QuadMiquel/Algebra.lean
f7b4da7d2abf6c1f66b987defd25bf99be4bf10a6cf081c97af51dd1f52dcf12  QuadMiquel/Basic.lean
fb6f3e39230d5279dee671a62c70748ed1969d32df77815ba49f3145b68b29fa  QuadMiquel/Bridge.lean
1e7cbfc90348e6884806654ff0c60085c6b3d807a6c2dec15aa7d3e126703fc8  QuadMiquel/Frame.lean
5ce67f6891f4ec1c36c4ff6f1a789f076bef4fa567a579f63c03d7efa9f785a5  QuadMiquel/Miquel.lean
bd38d47896239808e8a3375d1eb53cc8032502845fab4ac177770d0508a7cbf2  QuadMiquel/Parabola.lean
ea33070625a616859d0ac8e145c1fe6224af0f2c9bbc28a84f1e4505f9d49e5f  QuadMiquel/Parallel.lean
69b49c142ec7435ebfbea2fb2851f66a20c96fbdb9e48be3e67ecc0fae2936ce  QuadMiquel/Simson.lean
5da507d51bdc4b18c7f4e11a3d25fd967b0fcb57bd972f9fcd3ca481bef32751  tests/tamper.sh
7241a353c784648d4845a08f094acb5899de8f9d92d8a53652db83ba4bcc1903  lakefile.toml
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
01cd99b1415c15f68b71234930a2ef89077b1a45f44f1c171b6347316fe291d2  lake-manifest.json
```
Changed, as permitted:
* QuadMiquel.lean `e57f46fc…` → `82456dcf3e1ee7a89611275d01ff97b41944a6bd7fa474b25669d1f85966cc96`
* gate.sh `e30b3651…` → `3a6ed8a281a0d89928456ac193dad377ff77ddcccdce0cd993575c400e9544f7`

New file:
* ParabolaPoints.lean `58a18c5a69370c72bbe93fd7031bd006bea10101801d29a55feda1ab91d4d7ff`

Original `~/lean/quadparabola`: rehashed after the work and identical to before.
