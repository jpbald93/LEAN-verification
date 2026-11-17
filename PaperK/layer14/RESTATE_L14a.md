# L14a — Paper K: Mathlib-vocabulary restatements (8 claims) + sign audit

Deliverable: `paperK_l14_2d.lean` (namespace `PaperKL14`, `import Mathlib` only, no Paper K import).
Compiled on john as `~/lean/x_paperi_circles/scratch/paperK_l14_2d.lean` (Lean v4.33.1, the project's
`.lake/packages/mathlib`). sha256 of the local copy and of john's copy (read from `sha256sum` on both):
`3c8de98db69271df984c06294e30316f734a97c1c8ce507c35fe8cabf257cf60`.

## Vocabulary used (all thin wrappers over Mathlib)

- `G : Matrix (Fin 5) (Fin 5) ℝ` (literal `!![…]`), `lieB X Y := Matrix.toLinearMap₂' ℝ G X Y`.
  `lieB_apply` proves `lieB X Y = X0Y0 − X1Y1 − X2Y2 − X3Y4 − X4Y3`, which is the body of `PaperK.B`
  character for character. (Because nothing imports Paper K, `lieB = PaperK.B` is not a Lean
  theorem in this file. It is the same polynomial, and the `PaperK.bridge_B_toLinearMap₂` bridge already
  proves `PaperK.B = toLinearMap₂' ℝ G`.)
- `G3`, `lieB3` are the same construction on `Fin 6` (`lieB3_apply` gives the body of `PaperK3.B`).
- `circ r c` (c : `EuclideanSpace ℝ (Fin 2)`) = `![r, c 0, c 1, 1, (r² − c0² − c1²)/2]`, which is `PaperK2.circ r (c 0) (c 1)`.
- `sph r c` (c : `EuclideanSpace ℝ (Fin 3)`) is the same as `PaperK3.sph`.
- `pX P := !₂[P 1 / P 3, P 2 / P 3] : EuclideanSpace ℝ (Fin 2)`. This is `PaperK.pt`, but landing in the Euclidean plane, not in `ℝ × ℝ` with its sup metric.
- Geometry uses Mathlib's `dist`, `EuclideanGeometry.Sphere`, `Sphere.power`, `Collinear`, `Affine.Simplex.circumcenter`, `Matrix.det`.

## The eight rows

Every row got a **full proof**. None of them rests on a witness only.

| # | Source | Restated as | Proof / witness | Verdict |
|---|---|---|---|---|
| 1 | `PaperK.B_self_eq_zero_iff` | `B_self_eq_zero_iff (X : EuclideanSpace ℝ (Fin 5)) : lieB X X = 0 ↔ X 0^2 − X 1^2 − X 2^2 = 2·X 3·X 4` | full proof | **E**. Same equation. `X` is a `EuclideanSpace` point coerced to coordinates. |
| 2 | `PaperK.prop31` | `prop31`: same hypotheses (`hspan`, `hP`, `A 3, A' 3, P 3 ≠ 0`, with `lieB`); conclusion `P ∈ span{A,A'} ∧ Collinear ℝ {pX P, pX A, pX A'}` in `EuclideanSpace ℝ (Fin 2)` | full proof | **W**. The original's middle conjunct (`∃ s t, s+t=1 ∧ pt P = s•pt A + t•pt A'`) is dropped, so the explicit affine coefficients are lost. The coefficient `β·A'3/(αA3+βA'3)` does appear inside the proof (as a `lineMap` parameter) but not in the statement. Collinearity moved from `ℝ × ℝ` to the Euclidean plane, which has the same affine structure. |
| 3 | `PaperK.explicit_power` | `explicit_power (r : Fin 4 → ℝ) (c : Fin 4 → ℝ × ℝ) (hD : det[r a b 1] ≠ 0) (i)`, with `a, b` the coordinates of `c`, `s = a²+b²−r²`, `p = (−det[r b s 1], det[r a s 1])/(2D)`, `ρ = −det[a b s 1]/(2D)`, conclusion `(p.1−a i)²+(p.2−b i)²−(ρ−r i)² = ‖p‖²−ρ²+det[r a b s]/D` (`det4` = `Matrix.det` of the column matrix) | full proof (row relation proved by Leibniz expansion `det4_eq` + `ring`, not via the cofactor library) | **E**. Same formula and same sign convention, in `ℝ × ℝ` coordinates as asked. |
| 4 | `PaperK.equal_power` | `equal_power`: same hypotheses with `lieB`; conclusion `Sphere.power ⟨!₂[X i 1, X i 2], ρ − X i 0⟩ (pX P) = Sphere.power ⟨…X j…⟩ (pX P)` with `ρ = P 0/P 3`. Companion `power_eq_const` gives the common value `−lieB P P / P 3²`. | full proof | **E**. The Laguerre power `‖p−c‖² − (ρ−r)²` is the `Sphere.power` of `p` for the sphere of centre `c` and radius `ρ−r`, and this unfolds definitionally inside the proof. Indexing is over an arbitrary `ι`, as in the original. |
| 5 | `PaperK2.PX_circumcentre` | `PX_circumcentre (P) (hP3) (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) (r₀) (h : ∀ i, lieB P (circ r₀ (s.points i)) = 0) : pX P = s.circumcenter` | full proof (via `Affine.Simplex.eq_circumcenter_of_dist_eq`) | **O**. The original takes `D3 a b ≠ 0` and concludes equality with the explicit Cramer formula `(ccx, ccy)`. The restatement takes affine independence (a `Simplex`) and concludes equality with Mathlib's `circumcenter`. Two equivalences are not proved in this file: `D3 ≠ 0 ↔ AffineIndependent` (the old bridge `bridge_D3_collinear` covers it in `ℝ × ℝ`), and `(ccx, ccy) = circumcenter`. The geometric content is the same. |
| 6 | `PaperK2.equilateral_PX` | `equilateral_PX (P) (hP3) (r) (c : EuclideanSpace ℝ (Fin 2))`, with `h1,h2,h3` orthogonality to the unit circles at `!₂[0,0]`, `!₂[2,0]`, `!₂[1,√3]` and `h4` orthogonality to an arbitrary `circ r c`; conclusion `pX P = !₂[1, √3/3]` | full proof | **E**. As in the original, the fourth-circle hypothesis is unused. |
| 7 | `PaperK2.square_PX` (+ `square_apollonius`) | `square_PX (P) (hP3) (h : ∀ i, lieB P (circ 1 (sqc i)) = 0) : pX P = 0`, with `sqc = !₂[±1,±1]` centres; `square_apollonius k x ρ : (∀ i ≠ k, dist x (sqc i)^2 = (ρ−1)^2) ↔ x = 0 ∧ (ρ = 1+√2 ∨ ρ = 1−√2)` | full proofs | **E**. The centre and the two Apollonius radii `1 ± √2` hold for every 3-subset. `hP3` is unused, as in the original. |
| 8 | `PaperK3.tetra_PX_origin` | `tetra_PX_origin (r) (c : EuclideanSpace ℝ (Fin 3)) (P : Fin 6 → ℝ) (h : ∀ i, lieB3 P (sph 1 (tv i)) = 0) (_h5 : lieB3 P (sph r c) = 0) (_hP4 : P 4 ≠ 0) : !₂[P1/P4, P2/P4, P3/P4] = 0` with `tv = !₂[1,1,1], !₂[1,−1,−1], !₂[−1,1,−1], !₂[−1,−1,1]` | full proof | **E**. The family `Fin 5` is split into four vertex spheres plus the fifth. The proof shows `P1 = P2 = P3 = 0` directly from the four vertex hypotheses, so neither `h5` nor `P4 ≠ 0` is actually needed. |

No row was dropped.

## Sign audit

All the theorems below are proved in `paperK_l14_2d.lean` against john's Mathlib.

- `audit_two_B_dist (X Y) (hX : lieB X X = 0) (hY : lieB Y Y = 0) (hX3 : X 3 = 1) (hY3 : Y 3 = 1) : 2 * lieB X Y = dist !₂[X 1, X 2] !₂[Y 1, Y 2] ^ 2 − (X 0 − Y 0) ^ 2`. This is the general statement about the form.
- `audit_two_B_dist_circ r r' c c' : 2 * lieB (circ r c) (circ r' c') = dist c c' ^ 2 − (r − r') ^ 2`. This needs no hypotheses.
- `audit_B_half_power x r c : lieB (circ 0 x) (circ r c) = (1/2) * Sphere.power ⟨c, r⟩ x`. This is the radius-0 cycle.
- `audit_power_const_rho0 (P) (hP3) (hP0 : P 0 = 0) r c (h : lieB P (circ r c) = 0) : Sphere.power ⟨c, r⟩ (pX P) = −lieB P P / P 3 ^ 2`. This is the equal-power constant.
- `audit_B_eq_source X Y : lieB X Y = sourceForm X Y`, where `sourceForm X Y := X0Y0 − (X1Y1 + X2Y2) − X3Y4 − X4Y3`. This is reading (ii)'s source form `(X|Y) = r r' − c·c' − v w' − w v'`, transcribed literally.
- `audit_reading_ii_false : ¬ ∀ X Y, lieB X Y = −sourceForm X Y`. At `X = Y = (1,1,1,1,1)` the two sides are `−3` and `3`.
- `audit_witness : 2 * lieB (circ 1 !₂[0,0]) (circ 2 !₂[3,4]) = 24 ∧ dist !₂[0,0] !₂[3,4] ^ 2 − (1 − 2) ^ 2 = 24`. This is a numeric check of the general identity.

**Verdict: reading (i) is supported.** For normalised cycles, `2·B = dist² − (r−r')²`. For a radius-0 cycle,
`B = +½·Sphere.power`, and the equal-power constant is `Sphere.power = −B(P,P)/P₃²`.

**Reading (ii) as written is false.** `B` is *equal* to the stated source form, so the factor is **+1, not −1**
(`audit_B_eq_source`, refuted alternative `audit_reading_ii_false`).

The two readings differ only by the overall normalisation of the "source form", and nowhere else. Reading (ii)
would be correct with factor `−1` only if its source form were the opposite-signature Lie product
`c·c' − r r' + v w' + w v'`. That convention is what the docstring of `Bridge_paperK.lean` calls "the usual Lie
product", which is why it says `B = −(·|·)`. Against the form actually written in (ii), the factor between `B`
and the source form is exactly `+1`.

Axiom lines for the audit theorems are pasted in the gate below.

## Gate output (pasted)

```
$ cd ~/lean/x_paperi_circles && PATH=$HOME/.elan/bin:$PATH lake env lean scratch/paperK_l14_2d.lean; echo rc=$?
rc=0
$ grep -nE 'sorry|admit|native_decide|axiom' scratch/paperK_l14_2d.lean; echo grep_rc=$?
grep_rc=1
$ git status --short
?? scratch/
$ ls scratch
paperK_l14_2d.lean
probe.lean
```

The deliverable must not contain the substring `axiom`, so the `#print axioms` lines are kept out of it. They
were run on a temporary concatenation (deliverable + 18 `#print axioms` lines) at
`scratch/l14a_axcheck.lean`. That run gave `rc=0`, and the temporary file was deleted afterwards (the re-run
`ls scratch` showed only the two files above):

```
'PaperKL14.B_self_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.prop31' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.explicit_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.power_eq_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.equal_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.circ_pw' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.PX_circumcentre' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.equilateral_PX' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.square_PX' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.square_apollonius' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.tetra_PX_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.audit_two_B_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.audit_two_B_dist_circ' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.audit_B_half_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.audit_power_const_rho0' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.audit_B_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.audit_reading_ii_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14.audit_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
rc=0
```

Every command ran in under 20 s wall time. No `lake build`, update or cache fetch was run, and no tracked file
was touched.

## Standing negative results (unchanged, not re-examined here)

- The completion map does not fix `P_X`.
- The briefed general-`n` equal-power statement is false without `hnorm`. `PaperKn.brief_E_false` is present in `paperK_general_n.lean`.
- `PaperK3.tetra_thm36` is **not** Płatek's Theorem 3.6, and its name overclaims. It is the regular-tetrahedron special case: `P_X = 0` plus the radii `√3 ∓ 1`.
