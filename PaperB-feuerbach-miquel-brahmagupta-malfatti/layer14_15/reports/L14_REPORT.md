# PAPER B — LAYER 14 REPORT (Mathlib-only restatement + witnesses)
Started 2026-10-21 21:24 EDT on jack (jack). All work inline, no subagents.

## Sources
| repo | pinned commit (paper) | clone HEAD | toolchain | Mathlib rev | packages |
|---|---|---|---|---|---|
| feuerbach | 2bf41901548aed8b0e43d2f1bd10bb1a1d54ebf8 | same | v4.33.1 | 0df444a360eaa60ab8c11dca51a86af692955474 | symlink ~/barbier/.lake/packages |
| brahmagupta | c5c3ce014dc450ca212df76fade8948aa45421e0 | same | v4.33.1 | 0df444a3… | symlink |
| miquel | 401de13c0c4e51f67f87f7252f147048084c4a01 | same | v4.33.1 | 0df444a3… | symlink |
| malfatti | d39519346e71c9af8c349490a4dac5388de4d8f2 | same | v4.33.1 | 0df444a3… | symlink |

## Gate before (fresh clones)
- feuerbach: PASS (46 declarations, standard axioms only)
- brahmagupta: PASS (30 declarations, standard axioms only)
- miquel: PASS (84 declarations, standard axioms only)
- malfatti: PASS (77 declarations, standard axioms only)

(per-repo sections follow)

## Repo 1: feuerbach  (DONE 21:38)
New file `Feuerbach/L14.lean`; `import Feuerbach.L14` appended to `Feuerbach.lean`; REQUIRED line extended.

| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Feuerbach.feuerbach (Thm 1) | `l14_feuerbach` | YES | `l14w_feuerbach` (3-4-5 triangle 0,4,3i; circle centre 1+¾i, r=5/4) | incircle ≠ S; each excircle ≠ S; excircle ≠ incircle; excircles pairwise ≠; S.radius>0 | NPC is given by its DEFINING property: any `Sphere` through the 3 side midpoints; needs `finrank V = 2` (as in the paper's statement; in dim ≥3 three points don't determine a sphere) |

l14 statement (type, pp.fullNames):
```
@Feuerbach.l14_feuerbach : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (t : Affine.Triangle ℝ P) (S : EuclideanGeometry.Sphere P),
  (∀ (i j : Fin 3), i ≠ j → midpoint ℝ (t.points i) (t.points j) ∈ S) →
    (Affine.Simplex.insphere t).IsIntTangent S ∧ ∀ (i : Fin 3), (Affine.Simplex.exsphere t {i}).IsExtTangent S
```
grep "Feuerbach" over the type: empty → NAMESPACE-FREE. Axioms of l14_feuerbach, l14w_feuerbach: [propext, Classical.choice, Quot.sound].

Bridges: `l14_faceOppositeCentroid_eq_midpoint` (Mathlib faceOppositeCentroid = midpoint of the other two vertices); `l14_eq_ninePointCircle` (any circle through the 3 midpoints in a plane = `ninePointCircle`, via `ninePointCircle_eq_circumsphere_medial` + `circumsphere_unique_dist_eq`); `l14_circumcenter_345` (O = 2+(3/2)i).
Witness note: the incircle ≠ S part is proved non-trivially (if equal, r=R/2, so Euler's OI²=R(R-2r)=0, but I=1+¾i ≠ O=2+3/2 i).
Gate after: PASS (54 declarations, standard axioms only)  [before: 46]. Tamper: ALL TAMPERING TESTS REJECTED (6/6).
REQUIRED added: Feuerbach.l14_faceOppositeCentroid_eq_midpoint Feuerbach.l14_eq_ninePointCircle Feuerbach.l14_feuerbach Feuerbach.l14_S345 Feuerbach.l14_fact_plane Feuerbach.l14_S345_mid Feuerbach.l14_circumcenter_345 Feuerbach.l14w_feuerbach

## Repo 2: brahmagupta  (DONE 21:42)
New file `Brahmagupta/L14.lean`; `import Brahmagupta.L14` appended to `Brahmagupta.lean`; REQUIRED line extended.

| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Brahmagupta.brahmagupta (Thm 3) | `l14_brahmagupta` | YES | `l14w_brahmagupta`: A=(1,0), B=(0,1), C=(-1,0), D=(3/5,-4/5) on the unit circle, P=(1/3,0) | the 4 vertices pairwise ≠ (6 facts); BC ≠ CD (so it is not a square, unlike the repo's own witness); area = 9/5 > 0 | area expressed as `½·AC·BD·sin θ` with `InnerProductGeometry.angle (C-A) (D-B)` (the repo's `area` removed through its bridge `area_eq_half_mul_sin_angle`). Not expressed as Lebesgue measure of the convex hull (that identification is not in either library; the paper itself flags it as unproved — Sec. limits) |

l14 type (pp.fullNames):
```
Brahmagupta.l14_brahmagupta : ∀ (A B C D P : EuclideanSpace ℝ (Fin 2)),
  EuclideanGeometry.Cospherical {A, B, C, D} → Sbtw ℝ A P C → Sbtw ℝ B P D →
    Dist.dist A C * Dist.dist B D * Real.sin (InnerProductGeometry.angle (C - A) (D - B)) / 2 =
      √(((Dist.dist A B + Dist.dist B C + Dist.dist C D + Dist.dist D A) / 2 - Dist.dist A B) *
        ((…) / 2 - Dist.dist B C) * ((…) / 2 - Dist.dist C D) * ((…) / 2 - Dist.dist D A))
```
grep "Brahmagupta" over the type: empty → NAMESPACE-FREE. Axioms of both: [propext, Classical.choice, Quot.sound].
(The witness statement uses the repo's helper `pt x y := !₂[x,y]`, but that is the witness, not the restatement.)
Gate after: PASS (35 declarations, standard axioms only)  [before: 30]. Tamper: ALL TAMPERING TESTS REJECTED (6/6).
REQUIRED added: Brahmagupta.l14_brahmagupta Brahmagupta.l14_cospherical Brahmagupta.l14_sbtw_AC Brahmagupta.l14_sbtw_BD Brahmagupta.l14w_brahmagupta

## Repo 3: miquel  (DONE 22:03)
New file `Miquel/L14.lean`; `import Miquel.L14` appended to `Miquel.lean`; REQUIRED line extended.

| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Miquel.miquel (Thm 2) | `l14_miquel` | YES | `l14w_miquel`: A=0, B=2, C=2i, F=-2 (n=-1, extended side), E=-2i (t=-1, extended), D=1+i (u=½) | every M satisfying the conclusion is forced to be -2-2i, and that point ≠ A,B,C,D,E,F (6 facts); circle centres -1-i, -i, -1 pairwise ≠; circles distinct (B off circle 1, C off circle 2, A off circle 3) | `Dp ≠ 0` replaced by `¬ Collinear ℝ {A,B,C}` (bridge `Dp_eq_zero_iff_collinear`); the parametrisations `F = A + n(B-A)`, `n ∉ {0,1}` replaced by `F ∈ line[ℝ,A,B]`, `F ≠ A`, `F ≠ B` (bridge `l14_eq_of_mem_line`). Same strength: these are equivalent to the original hypotheses |
| Miquel.miquel_concyclic | `l14_miquel_cospherical` | YES | same configuration (applied inside `l14w_miquel`) | as above | the circles are expressed with Mathlib's `Cospherical` |

Types (pp.fullNames): see the type-check output section below; grep "Miquel" over both types: empty → NAMESPACE-FREE. Axioms of all three: [propext, Classical.choice, Quot.sound].
Gate after: PASS (91 declarations, standard axioms only)  [before: 84]. Tamper: ALL TAMPERING TESTS REJECTED (6/6).
REQUIRED added: Miquel.l14_eq_of_mem_line Miquel.l14_miquel Miquel.l14_miquel_cospherical Miquel.l14_dist_eq Miquel.l14_dist_sq Miquel.l14_ABC Miquel.l14w_miquel

## Repo 4: malfatti  (DONE 21:48)
New file `Malfatti/L14.lean`; `import Malfatti.L14` appended to `Malfatti.lean`; REQUIRED line extended.

| theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Malfatti.malfatti_circles_exist (Thm 4) | `l14_malfatti_circles_exist` | YES | `l14w_malfatti`: scalene Heronian triangle (0,0),(154,0),(35,120); side lengths 154,169,125 proved | for EVERY family c meeting the conclusion: pairwise distinct centres and pairwise distinct circles (`l14_center_ne_of_isExtTangent`: ext. tangent + positive radii ⇒ distinct centres); radii > 0 | the published statement was already Mathlib-only; l14 is a namespace-free re-export. Witness is a scalene triangle, unlike the repo's isosceles right triangle `triW` |
| Malfatti.malfatti_circles_formula (Thm 4, formula) | `l14_malfatti_circles_formula` | YES | same triangle; the formula family is exhibited and shown pairwise distinct | as above | the only repo definition in the original type, `Malfatti.semi`, is written out as `(d01+d12+d20)/2` (definitional) |

Types: see the type-check output section; grep "Malfatti" over both types (excluding the name line): 0 hits → NAMESPACE-FREE. Axioms of all three: [propext, Classical.choice, Quot.sound].
Limitation (honest): the witness does not compute the three radii in closed form (they involve √ of the incentre distances); non-vacuity is via positivity + distinctness, not explicit values.
Gate after: PASS (84 declarations, standard axioms only)  [before: 77]. Tamper: ALL TAMPERING TESTS REJECTED (6/6).
REQUIRED added: Malfatti.l14_malfatti_circles_exist Malfatti.l14_malfatti_circles_formula Malfatti.l14_center_ne_of_isExtTangent Malfatti.l14_tri_affineIndependent Malfatti.l14_tri Malfatti.l14_tri_sides Malfatti.l14w_malfatti

## FINDINGS
**No Mathlib-only restatement turned out FALSE, and none needed an extra hypothesis compared with the published theorem.** Details:
1. Feuerbach: the nine-point circle characterised by its defining property ("a circle through the 3 side midpoints") needs `finrank V = 2`. The repo's `feuerbach` already carries this hypothesis (unused there). It is genuinely needed for the defining-property form: in dimension ≥ 3 a large sphere through the three midpoints is not tangent to the incircle. No weakening.
2. Brahmagupta: the area is restated as `½·AC·BD·sin∠(AC,BD)` (Mathlib angle). It is NOT restated as the Lebesgue measure of the convex hull. That identification is proved neither in the repo nor here, so this is partial coverage of the notion "area", consistent with the paper's own limitation. The degenerate configurations the paper admits (e.g. A=B, C=D) still satisfy the hypotheses; the L14 witness uses 4 distinct vertices, a non-square, and area 9/5.
3. Miquel: `Dp ≠ 0` and the parametrisations n,t,u ∉ {0,1} are replaced by `¬Collinear`, `∈ line[ℝ,·,·]` and "≠ vertex". These are equivalent hypotheses, not stronger ones. The witness uses two points on extended sides (n = t = -1) and proves the Miquel point is unique (= -2-2i) and distinct from all six points.
4. Malfatti: the published statement was already Mathlib-only apart from the `semi` abbreviation, so nothing new mathematically.

## Type-check output (scratch files ~/l14B_scratch/*_types.lean, set_option pp.fullNames true; outputs in *_types.out)
```
@Feuerbach.l14_feuerbach : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (t : Affine.Triangle ℝ P) (S : EuclideanGeometry.Sphere P),
  (∀ (i j : Fin 3), i ≠ j → midpoint ℝ (t.points i) (t.points j) ∈ S) →
    (Affine.Simplex.insphere t).IsIntTangent S ∧ ∀ (i : Fin 3), (Affine.Simplex.exsphere t {i}).IsExtTangent S
grep Feuerbach over type → TYPE NAMESPACE-FREE

Brahmagupta.l14_brahmagupta : ∀ (A B C D P : EuclideanSpace ℝ (Fin 2)),
  EuclideanGeometry.Cospherical {A, B, C, D} → Sbtw ℝ A P C → Sbtw ℝ B P D →
    Dist.dist A C * Dist.dist B D * Real.sin (InnerProductGeometry.angle (C - A) (D - B)) / 2 =
      √(((Dist.dist A B + Dist.dist B C + Dist.dist C D + Dist.dist D A) / 2 - Dist.dist A B) * … )
grep Brahmagupta over type → TYPE NAMESPACE-FREE

@Miquel.l14_miquel : ∀ {A B C D E F : ℂ}, ¬Collinear ℝ {A, B, C} → F ∈ line[ℝ, A, B] → E ∈ line[ℝ, A, C] →
  D ∈ line[ℝ, B, C] → F ≠ A → F ≠ B → E ≠ A → E ≠ C → D ≠ B → D ≠ C →
  ∃ M, (∀ (O : ℂ) (r : ℝ), Dist.dist A O = r → Dist.dist E O = r → Dist.dist F O = r → Dist.dist M O = r) ∧
       (∀ (O : ℂ) (r : ℝ), Dist.dist B O = r → Dist.dist F O = r → Dist.dist D O = r → Dist.dist M O = r) ∧
        ∀ (O : ℂ) (r : ℝ), Dist.dist C O = r → Dist.dist D O = r → Dist.dist E O = r → Dist.dist M O = r
@Miquel.l14_miquel_cospherical : (same hypotheses) → ∃ M, EuclideanGeometry.Cospherical {A, E, F, M} ∧
  EuclideanGeometry.Cospherical {B, F, D, M} ∧ EuclideanGeometry.Cospherical {C, D, E, M}
grep Miquel over types → TYPES NAMESPACE-FREE

Malfatti.l14_malfatti_circles_exist : ∀ (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), ∃ c,
  (∀ (i : Fin 3), 0 < (c i).radius) ∧ (∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k →
     (c i).IsTangent line[ℝ, t.points i, t.points j] ∧ line[ℝ, t.points i, t.points j].SSameSide (c i).center (t.points k)) ∧
  ∀ (i j : Fin 3), i ≠ j → (c i).IsExtTangent (c j)
Malfatti.l14_malfatti_circles_formula : ∀ t, ∃ c, (∀ i, (c i).radius = Affine.Simplex.inradius t / (2 * ((Dist.dist (t.points 0) (t.points 1) + … ) / 2 - Dist.dist (t.points (i+1)) (t.points (i+2)))) * ( … - Affine.Simplex.inradius t - (Dist.dist (Affine.Simplex.incenter t) (t.points (i + 1)) + … ))) ∧ (same as exist)
grep Malfatti over types (excluding the decl-name line) → 0 hits, NAMESPACE-FREE
```
All l14_/l14w_ headline declarations: `depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Gate before → after
| repo | before | after | tamper |
|---|---|---|---|
| feuerbach | PASS (46) | PASS (54) | ALL TAMPERING TESTS REJECTED (sorry, ax2line, evalfake, macro, falsehyp, wrap) |
| brahmagupta | PASS (30) | PASS (35) | ALL REJECTED (6/6) |
| miquel | PASS (84) | PASS (91) | ALL REJECTED (6/6) |
| malfatti | PASS (77) | PASS (84) | ALL REJECTED (6/6) |

## Hashes (sha256, fresh clone vs after; pre/post lists in ~/l14B_hashes_<repo>.{pre,post})
Every pre-existing library file under `<Lib>/` and tests/tamper.sh is UNCHANGED. The only changed files are the permitted ones: the root file (one import line appended) and gate.sh (only the REQUIRED line changed, as `git diff` confirms). Unchanged-file hashes:
```
feuerbach:  Algebra 015176ce… Bridge a42d8d13… Geometry 3e408628… Main 2338aa8f… Witness 8b19f930… tamper afb25736…
brahmagupta: Basic 7c5a02a5… Bridge ee898182… Cyclic 3214326b… Examples e7736aae… tamper 287acae0…
miquel:     Basic 8c317d7e… Bridge ab22a572… Coeffs 67524042… Frame 1697ebaf… Main 58b4bb10… Witness 71dd8ea7… tamper aaef202b…
malfatti:   Algebra 4e3b8617… Bridge d8cbe706… Geometry c4a714e9… Main ae27e5a2… Witness 0eef9934… tamper 389c8943…
```
Root before→after: Feuerbach.lean 7c343c98→f51ca534; Brahmagupta.lean d9d01280→46b90b40; Miquel.lean 001636c0→60048551; Malfatti.lean 73677293→03e349e2. New files: Feuerbach/L14.lean bdc9d756…, Brahmagupta/L14.lean 1a0e09bd…, Miquel/L14.lean badaf583…, Malfatti/L14.lean 38d872a6….
No set_option/sorry/axiom/etc. in library files (gate token filter passes). The set_option lines are only in ~/l14B_scratch. Nothing committed or pushed. No lake update or cache get was run. Only ~/l14B_* directories were touched.

## Wall time
21:24 → 21:50 EDT (≈26 min).
