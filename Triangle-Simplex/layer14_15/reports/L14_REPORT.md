# Paper TriSimplex — Layer 14 report (Mathlib-only restatements + witnesses)

Paper: `AFM/TriangleSimplex/trisimplex.tex`. Machine: john (arm64 macOS). Work dirs `~/lean/l14TriSimplex_<repo>`.
Started 2026-10-21 22:20 EDT, finished 23:12 EDT (**wall time ≈ 52 min**). All work inline, no subagents.
Nothing committed or pushed. The only changes per repo: new `<Lib>/L14.lean`, one appended `import <Lib>.L14` line at
the end of the root file, and new names appended to the `REQUIRED=` line of `gate.sh`.

## Sources (fresh `git clone` + `git checkout` of the pinned commit)
| repo | commit (HEAD verified) | toolchain | Mathlib rev | packages |
|---|---|---|---|---|
| carnot | 98e5614812f2fc2491a729adf9677bfce9b55217 | v4.33.1 | 0df444a360eaa60ab8c11dca51a86af692955474 | symlink → ~/lean/clifford/.lake/packages |
| viviani | 029aa3d464db2ac8b3eb2e8f57e79e80f5585803 | v4.33.1 | 0df444a3… | same |
| degua | d46e6b20717012a9ca49fa3bffb08a5db0bdd2e7 | v4.33.1 | 0df444a3… | same |
| japanese-theorem | 34fd0a9c71c6efdca2f154043820f2a6aef7fb3a | v4.33.1 | 0df444a3… | same |
| poncelet-triangles | 9affe6203bbf0ec0f42eeb8c8ce567159de19b40 | v4.33.1 | 0df444a3… | same |

Baseline `jl build`: all five succeed (73 s, 47 s, 79 s, 94 s, 98 s).

## FINDINGS
**No Mathlib-only restatement was false or needed an extra hypothesis.** Every main theorem I restated goes
through from the library theorem plus definitional bridges, with the same hypotheses.

- **F0 (tooling, all 5 repos):** the published `gate.sh` calls `mktemp --suffix=.lean -p .`, which is GNU-only.
  Under `jl gate` (default BSD tools on macOS) every gate prints `FAIL: axiom report` before checking anything
  (`mktemp: unrecognized option '--suffix=.lean'`). With `jl -g gate` (GNU coreutils) all gates PASS. **All gate
  results below use `jl -g gate` / `jl -g tamper`.** On Linux, which the README presumably assumes, this doesn't show up.
- **F1 (gate heuristic, minor):** the token filter's `\bIO\b` also matches the plain word "IO" in a doc comment. My first
  Poncelet L14 docstring wrote `|IO| < R`; the gate rejected it with `FAIL: forbidden token`, and tamper then reported
  `NOT OK` for falsehyp/wrap because the gate stopped at the token stage. Changing the comment to `|OI|` fixed it.
  The heuristic is conservative, not unsound, but authors should know that "IO" is banned even in prose.
- **Note (Japanese, not a weakening):** a Mathlib `Affine.Triangle` needs an affine-independence proof, so
  `l14_triInradius_eq` / `l14_japanese_quadrilateral` take `AffineIndependent ℝ ![a,b,c]` arguments. They follow
  from the stated positive-orientation hypotheses (that's the repo's `affineIndependent_of_areaForm_ne_zero`),
  and the conclusion doesn't depend on which proof is supplied (proof irrelevance), so this adds no real assumption.
  The polygon form uses `if h : AffineIndependent … then inradius else 0`, matching the repo's `triInradius`.

## Per-repo tables
"namespace-free" = the `#check` output under `pp.fullNames` contains no repo namespace (see the type-check section;
the grep strips only the declaration's own name at the start of the line).

### carnot (`Carnot/L14.lean`, 124 lines)
| paper theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Thm 3.1 Carnot (`Carnot.carnot`, `carnot_sum`) | `l14_carnot`: `∑ i, t.signedInfDist i t.circumcenter = t.circumradius + t.inradius`; `l14_carnot_of_dist_eq`: the circumcentre given by its defining property (in the plane, equidistant `R` from the vertices) | yes | `l14w_carnot`: obtuse scalene `0, 21, 6+8i` (sides 21, 10, 17) | the three signed distances are `3R/5 > 0`, `15R/17 > 0`, `−13R/85 < 0`; proved: `d₂ < 0 < d₀, d₁` and `d₀ ≠ d₁` | shows the signs matter; the repo's `signedSideDist` is replaced by Mathlib `signedInfDist` via the repo lemma `signedSideDist_eq_signedInfDist` |
| Thm 3.2 cosine form | `l14_signedInfDist_circumcenter_eq` (`d_i(O) = R cos α_i`, `EuclideanGeometry.angle`), `l14_cos_add_cos_add_cos` | yes | same witness (cosines computed exactly: 3/5, 15/17, −13/85) | as above | |

### viviani (`Viviani/L14.lean`, 165 lines)
Height and distance to a facet are written as `Metric.infDist x (affineSpan ℝ (s.points '' {i}ᶜ))`, not as
`Affine.Simplex.height` / `orthogonalProjectionSpan`. Both are Mathlib, but the infDist form is the defining property.
| paper theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Thm 4.1 (weights) | `l14_sum_signedInfDist_div_height` | yes | `l14w_viviani` | — | |
| Thm 4.2 (equal heights, signed / unsigned, converse) | `l14_sum_signedInfDist_eq_height`, `l14_sum_infDist_eq_height`, `l14_exists_forall_sum_signedInfDist_eq_iff` | yes | `l14w_viviani` | | |
| Prop 4.3 (equilateral ⇒ equal heights) | `l14_equilateral_height_eq` | yes | `l14w_viviani` (triangle proved `Equilateral`, side √2) | | |
| Cor 4.4 Viviani | `l14_regular_sum_infDist`; classical form `l14_viviani_triangle`: equilateral `a,b,c` (affinely independent, pairwise equal distances), `p ∈ convexHull ℝ {a,b,c}` ⇒ `infDist p line[b,c] + infDist p line[a,c] + infDist p line[a,b] = infDist a line[b,c]` | yes | `l14w_viviani`: `e₀,e₁,e₂ ∈ ℝ³`, `p` with weights (1/2,1/4,1/4) | the distances are `h/2, h/4, h/4`: proved `d₀ = 2d₁`, `d₁ = d₂`, `d₁ > 0` (not all equal, all positive), sum = height | |

### degua (`DeGua/L14.lean`, 140 lines)
| paper theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Thm 5.1 (3-D, cross product) | `l14_de_gua_three` (`triAreaSq` unfolded to Mathlib `crossProduct`/`⬝ᵥ`) | yes | `l14w_de_gua_three`: O=0, A=e₀, B=2e₁, C=3e₂ | hypotheses proved; squared face areas 49/4, 1, 9, 9/4 (pairwise distinct, > 0) | |
| Thm 5.2 general | `l14_de_gua` (`simplexVolSq` unfolded to `det (Matrix.gram …) / (m!)²`) | yes | `l14w_de_gua` (same tetrahedron, m = 2) | pairwise orthogonality proved; values 49/4, 9, 9/4, 1 | |
| Lemma 5.3 | `l14_det_diagonal_add_const` | yes | no hypotheses → no witness needed | | |
| Thm 5.4 Cauchy–Binet | `l14_cauchy_binet` | yes | `l14w_cauchy_binet`: 2×3 / 3×2 over ℤ, `det(AB) = 7 ≠ 0` | nonzero value, so the sum is not trivially 0 | |
| Cor 5.5 projection form | `l14_det_gram_eq_sum_sq_minors` | yes | no hypotheses → no witness needed | | |

### japanese-theorem (`Japanese/L14.lean`, 279 lines)
| paper theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Lemma 6.3 Carnot chord form | `l14_triInradius_eq` (`chordDist` unfolded to `o.areaForm (q -ᵥ p) (O -ᵥ p) / dist p q`, inradius = Mathlib's) | yes | used inside the quadrilateral witness | | |
| Thm 6.4 quadrilateral | `l14_japanese_quadrilateral` | yes | `l14w_japanese_quadrilateral`: `1, (3+4i)/5, −1, −i` on the unit circle | 6 pairwise distinctness facts, 4 positive orientations, 4 inradii > 0 | |
| Thm 6.8 Japanese (geometric triangulations) | `l14_japanese_polygon`: `IsGeomTriangulation` written out (chords `a<b≤n−1`, no two distinct chords whose open segments share a point via `Sbtw`, maximal); triangles = triples in `range n³` whose 3 sides are in `E` | yes | `l14w_japanese_polygon`: same quadrilateral as `p : ℕ → ℂ` (an explicit `let`), `E = sides ∪ {(0,2)}`, `E' = sides ∪ {(1,3)}` | `E ≠ E'` proved; both proved to satisfy the written-out triangulation conditions; hconv and concyclicity proved | bridges `l14b_isGeomTriangulation_iff`, `l14b_triangleInradiusSum_eq` |
| Thm 6.5 (tree form), Props 6.6/6.7, combinatorial variant | **not restated** | — | — | — | they're about the repo's inductive `Triangulation` / `IsTriangulation`; Thm 6.8 covers the geometric statement. Time-boxed. |

### poncelet-triangles (`Poncelet3/L14.lean`, 245 lines)
| paper theorem | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| Thm 7.1 Euler | `l14_euler`, `l14_euler_excenter` | yes | `l14w_euler`: triangle `0, 4, 3i`; circumcentre `2 + 3i/2`, R = 5/2 proved | `O ≠ I` proved (O lies on the hypotenuse, I is at signed distance r > 0 from it); `R(R−2r) > 0` | |
| Thm 7.2 porism | `l14_exists_poncelet_triangle` (repo statement already Mathlib-only) | yes | `l14w_poncelet`: Γ = (2+3i/2, 5/2), ω = (1+i, 1) | hypotheses proved (`0<r<R`, `d² = 5/4 = R(R−2r)`, `\|OI\| < R`); explicit Poncelet triangle `0,4,3i` with pairwise distinct vertices and the 3 tangencies at `1`, `i`, `8/5+9i/5` proved by hand | |
| Thm 7.3 converse + iff | `l14_euler_of_isTangent`, `l14_poncelet_triangle_iff` | yes | `l14w_poncelet` (the explicit triangle meets every hypothesis of the converse) | as above | |
| Thm 7.5 construction | `l14_poncelet_construction`, `l14_poncelet_construction_iff`, `l14_poncelet_all_or_nothing` (`ConstructionCloses` unfolded into `Sphere.tangentsFrom` / `IsTangent`) | yes | `l14w_poncelet` gives the unfolded closure property at every `A ∈ Γ`, including its non-vacuity part (i) | | |
| Lemma 8.4 correctness lemmas (`radius_lt_dist_center_of_mem`, `tangentsFrom_eq_pair`, `secondInter_spec`) | **not restated** | — | — | — | auxiliary; time-boxed |

Also not restated (auxiliary or definition-correctness lemmas): Carnot `carnot_poly`, `signedSideDist_*`; De Gua
`triAreaSq_eq_simplexVolSq` (in effect used inside `l14w_de_gua`). Every theorem environment in §§3–7 of the paper
that is a main result has an l14 form, except the Japanese tree/combinatorial forms listed above.

## Bridges (new, all in REQUIRED)
- carnot: `l14b_affineIndependent` (nonzero cross term ⇒ affinely independent, ℂ), `l14b_norm`, `l14b_cos_angle` (exact cosine in ℂ).
- viviani: `l14b_dist_eq_infDist`, `l14b_height_eq_infDist` (projection distance / height = `Metric.infDist` to the facet span), `l14b_witness_indep`.
- degua: `l14b_corner_areas`, `l14b_corner_orth`.
- japanese: `l14b_triInradius_eq`, `l14b_isGeomTriangulation_iff`, `l14b_triangleInradiusSum_eq`, `l14b_norm`, `l14b_mem_unit`, `l14b_indep`, `l14b_quad_pos`, `l14b_quad`, `l14b_quad_conv`, `l14b_quad_tri`, `l14b_isTri_iff`.
- poncelet: `l14b_norm`, `l14b_dist`, `l14b_isTangent` (tangency in ℂ from two perpendicularity checks), `l14b_config`.

## REQUIRED added (only the `REQUIRED=` line of gate.sh changed; `git diff --stat`: root file +1, gate.sh 1 line)
- carnot: Carnot.l14_carnot Carnot.l14_carnot_of_dist_eq Carnot.l14_signedInfDist_circumcenter_eq Carnot.l14_cos_add_cos_add_cos Carnot.l14b_affineIndependent Carnot.l14b_norm Carnot.l14b_cos_angle Carnot.l14w_carnot
- viviani: Viviani.l14_sum_signedInfDist_div_height Viviani.l14_sum_signedInfDist_eq_height Viviani.l14_exists_forall_sum_signedInfDist_eq_iff Viviani.l14_sum_infDist_eq_height Viviani.l14_equilateral_height_eq Viviani.l14_regular_sum_infDist Viviani.l14_viviani_triangle Viviani.l14w_viviani Viviani.l14b_dist_eq_infDist Viviani.l14b_height_eq_infDist Viviani.l14b_witness_indep
- degua: DeGua.l14_de_gua_three DeGua.l14_de_gua DeGua.l14_det_diagonal_add_const DeGua.l14_cauchy_binet DeGua.l14_det_gram_eq_sum_sq_minors DeGua.l14w_de_gua_three DeGua.l14w_de_gua DeGua.l14w_cauchy_binet DeGua.l14b_corner_areas DeGua.l14b_corner_orth
- japanese-theorem: Japanese.l14b_triInradius_eq Japanese.l14_triInradius_eq Japanese.l14_japanese_quadrilateral Japanese.l14b_isGeomTriangulation_iff Japanese.l14b_triangleInradiusSum_eq Japanese.l14_japanese_polygon Japanese.l14b_norm Japanese.l14b_mem_unit Japanese.l14b_indep Japanese.l14b_quad_pos Japanese.l14w_japanese_quadrilateral Japanese.l14b_quad Japanese.l14b_quad_conv Japanese.l14b_quad_tri Japanese.l14b_isTri_iff Japanese.l14w_japanese_polygon
- poncelet-triangles: Poncelet3.l14_euler Poncelet3.l14_euler_excenter Poncelet3.l14_exists_poncelet_triangle Poncelet3.l14_euler_of_isTangent Poncelet3.l14_poncelet_triangle_iff Poncelet3.l14_poncelet_construction Poncelet3.l14_poncelet_construction_iff Poncelet3.l14_poncelet_all_or_nothing Poncelet3.l14b_norm Poncelet3.l14b_dist Poncelet3.l14b_isTangent Poncelet3.l14b_config Poncelet3.l14w_poncelet Poncelet3.l14w_euler

## Gate before → after (`jl -g gate`; see F0)
| repo | before | after |
|---|---|---|
| carnot | `PASS (12 declarations, standard axioms only)` | `PASS (20 declarations, standard axioms only)` |
| viviani | `PASS (10 declarations, standard axioms only)` | `PASS (21 declarations, standard axioms only)` |
| degua | `PASS (10 declarations, standard axioms only)` | `PASS (20 declarations, standard axioms only)` |
| japanese-theorem | `PASS (51 declarations, standard axioms only)` | `PASS (67 declarations, standard axioms only)` |
| poncelet-triangles | `PASS (22 declarations, standard axioms only)` | `PASS (36 declarations, standard axioms only)` |

## Tamper (`jl -g tamper`, after)
| repo | tests rejected | result |
|---|---|---|
| carnot | sorry, ax2line, evalfake, macro, falsehyp, wrap | `ALL TAMPERING TESTS REJECTED` |
| viviani | sorry, ax2line, evalfake, macro, falsehyp, wrap | `ALL TAMPERING TESTS REJECTED` |
| degua | sorry, ax2line, evalfake, macro, falsehyp, wrap | `ALL TAMPERING TESTS REJECTED` |
| japanese-theorem | sorry, ax2line, evalfake, macro, falsehyp, wrap | `ALL TAMPERING TESTS REJECTED` |
| poncelet-triangles | sorry, ax2line, evalfake, macro, falsehyp, wrap | `ALL TAMPERING TESTS REJECTED` |

## Hashes
For every tracked `.lean` file I compared the working-tree sha256 with the blob at the pinned commit (`git show HEAD:<f>`):
- carnot: 5 tracked .lean, 4 identical; only `Carnot.lean` changed (+`import Carnot.L14`)
- viviani: 5 tracked, 4 identical; only `Viviani.lean` changed (+1 import line)
- degua: 6 tracked, 5 identical; only `DeGua.lean` changed (+1 import line)
- japanese-theorem: 9 tracked, 8 identical; only `Japanese.lean` changed (+1 import line)
- poncelet-triangles: 10 tracked, 9 identical; only `Poncelet3.lean` changed (+1 import line)
`git diff -U0` of each root file is exactly one added `import <Lib>.L14` line at the end. `tests/tamper.sh` is
unchanged in all five repos (sha before = after). Untracked: only `<Lib>/L14.lean` (plus `.lake` symlink/build).
Full working-tree hash lists:

carnot (working tree, all tracked .lean files):
```
9fa51f7eb34e67b08cdad38cdb6a2480f50192790f84e4991d49a531219dd442  Carnot.lean
1a18e5333c100219aada8b4ece33e744c05be8f8b4356421767c3aecb5981bad  Carnot/Algebra.lean
87a9c1988963bd6c783e1024d825705dedf17118fd99a21b2faf71c495df0ae3  Carnot/Geometry.lean
1fb6ed3429304a9a0373f17c29c39af207fc835e4728f0757883761d93394745  Carnot/Main.lean
6d3629bedb459b7fb28fef3266451838cda2c6393fd41e027c82725232039262  scratch/Axioms.lean
```

viviani (working tree, all tracked .lean files):
```
d9e149d8b9ff2e8c5216c00f68ac2738464d11cca6101c8560fa7369c1e24d88  Viviani.lean
0e158e6bb275ef7aca5754fd7edc349d6d386fb82e2271821ac70991d620c0ca  Viviani/Basic.lean
20f61763238cec1f046cf1df890aae038cf1c3824b39c47ac16470a9ec36ae90  Viviani/Equilateral.lean
c325e7bf8d9dca4dcdb316f3f71eb020d5e20e61ef355cf7bea83b9d3efe56d1  Viviani/Heights.lean
c2a07f516ca7e9296ca2f27e5fa1b909fe488e99f4f310e87cb2970025d16909  scratch/Axioms.lean
```

degua (working tree, all tracked .lean files):
```
41e8d193e756ade8071dadd47fc830fa2ec5775ab0f9898879735b285a91601b  DeGua.lean
084667537392c949fc8acd42991e86883a72b1938c3866ce76e310b6b5e76acf  DeGua/Bridge.lean
affbcf74306be0f3aae934df82694245310fab0fb575bae781a99e08f6a17a35  DeGua/CauchyBinet.lean
14946c809e0ab9e9c49adae9ff132005646972c2d7a87a8ffc50cecc68b711a2  DeGua/General.lean
847942fd3b06ede5832fb02276c690906068ab299361365959047f25f971875d  DeGua/Three.lean
87c226880cfcc62e98222199140aba1eb7b5d2c97daf864ef3146351392a313e  scratch/Axioms.lean
```

japanese-theorem (working tree, all tracked .lean files):
```
0a8200647660cbb3cb56c305e4c115fc69ec191d6ed6b5ae4d5b411562d3d26d  Japanese.lean
263971b7e9e8b78af4959b48f91e1abffc218a47bb6149a67c0bb5e69f2f57d2  Japanese/Basic.lean
1a18e5333c100219aada8b4ece33e744c05be8f8b4356421767c3aecb5981bad  Japanese/Carnot/Algebra.lean
72d0326f6ef7bb2fda5cc3fcda8d280464098f0ce10631ae0d8e2340aff078f4  Japanese/Carnot/Geometry.lean
7d27ca0f91c77fb86de2fe45848a1445c75913df0c9362498bd39872ecad957c  Japanese/Carnot/Main.lean
89bd618e607a92a17b9c107ef1898d2332e846cd5ada0bf800627526c210d7b7  Japanese/Combinatorial.lean
7b107f1405233abae1f35c439343c5b53bdc6dbbaf0f311208ed8664d82eb5d8  Japanese/Geometric.lean
4ac37743441eb5aeffcc2851ec4cf999e7df8ff50c319f7515d02701ec078418  Japanese/Polygon.lean
b1b5e47d062f8d04a38f781a274b3a9486394c75ac1ace20f52d7d5f300cace2  scratch/Axioms.lean
```

poncelet-triangles (working tree, all tracked .lean files):
```
190bc20d6072aa8a7c589a42a1ed53161a751b24d671ddfe11cf48c7f8eaa4df  Poncelet3.lean
29aa4e3107b22d15503bbaa01b069661a506530323ffd3ab375c54876e80a395  Poncelet3/Algebra.lean
4c84dbb67595cbc2d674dc5e6d16c48cb6e172345e4266ad4d33a595b9285aa9  Poncelet3/Closure.lean
75095e3125f473ac068e038a96d8a5c409f1bec1ee4977a6621bd20a06ff354f  Poncelet3/Construction.lean
015176ce7796f94bd69fe5756eed4cfa499e4241462ff3f51acd3468bee34c29  Poncelet3/Euler/Algebra.lean
ea4c126619c6dbaac72dade046203e397dceafd4cc1c54299ac5362fa2ba4c10  Poncelet3/Euler/Geometry.lean
060600eb0a41af5f7bd07ee8b5e714187daf67946c8550fa5f4365f7c7f6110c  Poncelet3/Euler/Main.lean
8bd1430c23d0dd61f13f65758abc985d2238292b8355d694e055075095fdb8ce  Poncelet3/Package.lean
66928c79f0bcb398b604aa082ecbf95ec61ad975a9f0c7b4b1bb8ba6ba670a69  Poncelet3/Porism.lean
f79e31cbdf5b5c8a3737e79bd8e9f0a226901c68d37099b5e35cba7490e2070d  scratch/Ax.lean
```

## Type-check output (scratch `~/lean/l14TriSimplex_scratch/<repo>_types.lean`, `set_option pp.fullNames true`)
For each repo the grep for the repo namespace(s) (`Carnot\.`; `Viviani\.|Affine\.Simplex\.(repo lemma names)`; `DeGua\.`; `Japanese\.|Carnot\.`; `Poncelet3\.|Feuerbach\.`) after stripping the leading declaration name **returned empty for all five**.

### carnot
```
@Carnot.l14_carnot : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
  [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (t : Affine.Triangle ℝ P),
  ∑ i, (Affine.Simplex.signedInfDist t i) (Affine.Simplex.circumcenter t) =
    Affine.Simplex.circumradius t + Affine.Simplex.inradius t
@Carnot.l14_carnot_of_dist_eq : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (t : Affine.Triangle ℝ P)
  {O : P},
  O ∈ affineSpan ℝ (Set.range t.points) →
    ∀ {R : ℝ},
      (∀ (i : Fin (2 + 1)), Dist.dist (t.points i) O = R) →
        ∑ i, (Affine.Simplex.signedInfDist t i) O = R + Affine.Simplex.inradius t
@Carnot.l14_signedInfDist_circumcenter_eq : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (t : Affine.Triangle ℝ P),
  (Affine.Simplex.signedInfDist t 0) (Affine.Simplex.circumcenter t) =
      Affine.Simplex.circumradius t * Real.cos (EuclideanGeometry.angle (t.points 1) (t.points 0) (t.points 2)) ∧
    (Affine.Simplex.signedInfDist t 1) (Affine.Simplex.circumcenter t) =
        Affine.Simplex.circumradius t * Real.cos (EuclideanGeometry.angle (t.points 0) (t.points 1) (t.points 2)) ∧
      (Affine.Simplex.signedInfDist t 2) (Affine.Simplex.circumcenter t) =
        Affine.Simplex.circumradius t * Real.cos (EuclideanGeometry.angle (t.points 0) (t.points 2) (t.points 1))
@Carnot.l14_cos_add_cos_add_cos : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (t : Affine.Triangle ℝ P),
  Real.cos (EuclideanGeometry.angle (t.points 1) (t.points 0) (t.points 2)) +
        Real.cos (EuclideanGeometry.angle (t.points 0) (t.points 1) (t.points 2)) +
      Real.cos (EuclideanGeometry.angle (t.points 0) (t.points 2) (t.points 1)) =
    1 + Affine.Simplex.inradius t / Affine.Simplex.circumradius t
Carnot.l14w_carnot : ∃ t,
  t.points = ![0, 21, 6 + 8 * Complex.I] ∧
    (Affine.Simplex.signedInfDist t 2) (Affine.Simplex.circumcenter t) < 0 ∧
      0 < (Affine.Simplex.signedInfDist t 0) (Affine.Simplex.circumcenter t) ∧
        0 < (Affine.Simplex.signedInfDist t 1) (Affine.Simplex.circumcenter t) ∧
          (Affine.Simplex.signedInfDist t 0) (Affine.Simplex.circumcenter t) ≠
              (Affine.Simplex.signedInfDist t 1) (Affine.Simplex.circumcenter t) ∧
            ∑ i, (Affine.Simplex.signedInfDist t i) (Affine.Simplex.circumcenter t) =
              Affine.Simplex.circumradius t + Affine.Simplex.inradius t
```

### viviani
```
@Viviani.l14_sum_signedInfDist_div_height : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {n : ℕ} [inst_4 : NeZero n]
  (s : Affine.Simplex ℝ P n) {p : P},
  p ∈ affineSpan ℝ (Set.range s.points) →
    ∑ i, (s.signedInfDist i) p / Metric.infDist (s.points i) ↑(affineSpan ℝ (s.points '' {i}ᶜ)) = 1
@Viviani.l14_sum_signedInfDist_eq_height : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {n : ℕ} [inst_4 : NeZero n]
  (s : Affine.Simplex ℝ P n),
  (∀ (i j : Fin (n + 1)),
      Metric.infDist (s.points i) ↑(affineSpan ℝ (s.points '' {i}ᶜ)) =
        Metric.infDist (s.points j) ↑(affineSpan ℝ (s.points '' {j}ᶜ))) →
    ∀ {p : P},
      p ∈ affineSpan ℝ (Set.range s.points) →
        ∀ (k : Fin (n + 1)), ∑ i, (s.signedInfDist i) p = Metric.infDist (s.points k) ↑(affineSpan ℝ (s.points '' {k}ᶜ))
@Viviani.l14_exists_forall_sum_signedInfDist_eq_iff : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {n : ℕ} [inst_4 : NeZero n]
  (s : Affine.Simplex ℝ P n),
  (∃ c, ∀ p ∈ affineSpan ℝ (Set.range s.points), ∑ i, (s.signedInfDist i) p = c) ↔
    ∀ (i j : Fin (n + 1)),
      Metric.infDist (s.points i) ↑(affineSpan ℝ (s.points '' {i}ᶜ)) =
        Metric.infDist (s.points j) ↑(affineSpan ℝ (s.points '' {j}ᶜ))
@Viviani.l14_sum_infDist_eq_height : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {n : ℕ} [NeZero n]
  (s : Affine.Simplex ℝ P n),
  (∀ (i j : Fin (n + 1)),
      Metric.infDist (s.points i) ↑(affineSpan ℝ (s.points '' {i}ᶜ)) =
        Metric.infDist (s.points j) ↑(affineSpan ℝ (s.points '' {j}ᶜ))) →
    ∀ {p : P},
      p ∈ s.closedInterior →
        ∀ (k : Fin (n + 1)),
          ∑ i, Metric.infDist p ↑(affineSpan ℝ (s.points '' {i}ᶜ)) =
            Metric.infDist (s.points k) ↑(affineSpan ℝ (s.points '' {k}ᶜ))
@Viviani.l14_equilateral_height_eq : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {n : ℕ} [NeZero n]
  {s : Affine.Simplex ℝ P n},
  s.Equilateral →
    ∀ (i j : Fin (n + 1)),
      Metric.infDist (s.points i) ↑(affineSpan ℝ (s.points '' {i}ᶜ)) =
        Metric.infDist (s.points j) ↑(affineSpan ℝ (s.points '' {j}ᶜ))
@Viviani.l14_regular_sum_infDist : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {n : ℕ} [NeZero n]
  {s : Affine.Simplex ℝ P n},
  s.Regular →
    ∀ {p : P},
      p ∈ s.closedInterior →
        ∀ (k : Fin (n + 1)),
          ∑ i, Metric.infDist p ↑(affineSpan ℝ (s.points '' {i}ᶜ)) =
            Metric.infDist (s.points k) ↑(affineSpan ℝ (s.points '' {k}ᶜ))
@Viviani.l14_viviani_triangle : ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
  {a b c : V},
  AffineIndependent ℝ ![a, b, c] →
    Dist.dist a b = Dist.dist b c →
      Dist.dist b c = Dist.dist c a →
        ∀ {p : V},
          p ∈ (convexHull ℝ) {a, b, c} →
            Metric.infDist p ↑line[ℝ, b, c] + Metric.infDist p ↑line[ℝ, a, c] + Metric.infDist p ↑line[ℝ, a, b] =
              Metric.infDist a ↑line[ℝ, b, c]
Viviani.l14w_viviani : ∃ t,
  (t.points = fun i => EuclideanSpace.single i 1) ∧
    Affine.Simplex.Equilateral t ∧
      ∃ p ∈ Affine.Simplex.closedInterior t,
        p = (Finset.affineCombination ℝ Finset.univ t.points) ![1 / 2, 1 / 4, 1 / 4] ∧
          Metric.infDist p ↑(affineSpan ℝ (t.points '' {0}ᶜ)) =
              2 * Metric.infDist p ↑(affineSpan ℝ (t.points '' {1}ᶜ)) ∧
            Metric.infDist p ↑(affineSpan ℝ (t.points '' {1}ᶜ)) = Metric.infDist p ↑(affineSpan ℝ (t.points '' {2}ᶜ)) ∧
              0 < Metric.infDist p ↑(affineSpan ℝ (t.points '' {1}ᶜ)) ∧
                ∑ i, Metric.infDist p ↑(affineSpan ℝ (t.points '' {i}ᶜ)) =
                  Metric.infDist (t.points 0) ↑(affineSpan ℝ (t.points '' {0}ᶜ))
```

### degua
```
DeGua.l14_de_gua_three : ∀ (O A B C : EuclideanSpace ℝ (Fin 3)),
  Inner.inner ℝ (A - O) (B - O) = 0 →
    Inner.inner ℝ (B - O) (C - O) = 0 →
      Inner.inner ℝ (C - O) (A - O) = 0 →
        (crossProduct (B - A).ofLp) (C - A).ofLp ⬝ᵥ (crossProduct (B - A).ofLp) (C - A).ofLp / 4 =
          (crossProduct (A - O).ofLp) (B - O).ofLp ⬝ᵥ (crossProduct (A - O).ofLp) (B - O).ofLp / 4 +
              (crossProduct (B - O).ofLp) (C - O).ofLp ⬝ᵥ (crossProduct (B - O).ofLp) (C - O).ofLp / 4 +
            (crossProduct (C - O).ofLp) (A - O).ofLp ⬝ᵥ (crossProduct (C - O).ofLp) (A - O).ofLp / 4
@DeGua.l14_de_gua : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] (O : E) {m : ℕ}
  (P : Fin (m + 1) → E),
  (Pairwise fun i j => Inner.inner ℝ (P i - O) (P j - O) = 0) →
    (Matrix.gram ℝ fun j => P j.succ - P 0).det / ↑m.factorial ^ 2 =
      ∑ i,
        (Matrix.gram ℝ fun j => Fin.cons O (P ∘ i.succAbove) j.succ - Fin.cons O (P ∘ i.succAbove) 0).det /
          ↑m.factorial ^ 2
@DeGua.l14_det_diagonal_add_const : ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (b : ι → ℝ) (c : ℝ),
  (Matrix.diagonal b + Matrix.of fun x x_1 => c).det = ∏ i, b i + c * ∑ i, ∏ j ∈ Finset.univ.erase i, b j
@DeGua.l14_cauchy_binet : ∀ {R : Type u_1} [inst : CommRing R] {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
  (B : Matrix (Fin n) (Fin k) R), (A * B).det = ∑ s with StrictMono s, (A.submatrix id s).det * (B.submatrix s id).det
@DeGua.l14_det_gram_eq_sum_sq_minors : ∀ {k n : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)),
  (Matrix.gram ℝ v).det = ∑ s with StrictMono s, (Matrix.of fun i j => (v i).ofLp (s j)).det ^ 2
DeGua.l14w_de_gua_three : have O := !₂[0, 0, 0];
have A := !₂[1, 0, 0];
have B := !₂[0, 2, 0];
have C := !₂[0, 0, 3];
(Inner.inner ℝ (A - O) (B - O) = 0 ∧ Inner.inner ℝ (B - O) (C - O) = 0 ∧ Inner.inner ℝ (C - O) (A - O) = 0) ∧
  (crossProduct (B - A).ofLp) (C - A).ofLp ⬝ᵥ (crossProduct (B - A).ofLp) (C - A).ofLp / 4 = 49 / 4 ∧
    (crossProduct (A - O).ofLp) (B - O).ofLp ⬝ᵥ (crossProduct (A - O).ofLp) (B - O).ofLp / 4 = 1 ∧
      (crossProduct (B - O).ofLp) (C - O).ofLp ⬝ᵥ (crossProduct (B - O).ofLp) (C - O).ofLp / 4 = 9 ∧
        (crossProduct (C - O).ofLp) (A - O).ofLp ⬝ᵥ (crossProduct (C - O).ofLp) (A - O).ofLp / 4 = 9 / 4
DeGua.l14w_de_gua : have O := !₂[0, 0, 0];
have P := ![!₂[1, 0, 0], !₂[0, 2, 0], !₂[0, 0, 3]];
(Pairwise fun i j => Inner.inner ℝ (P i - O) (P j - O) = 0) ∧
  (Matrix.gram ℝ fun j => P j.succ - P 0).det / ↑(Nat.factorial 2) ^ 2 = 49 / 4 ∧
    (Matrix.gram ℝ fun j => ![O, P 1, P 2] j.succ - ![O, P 1, P 2] 0).det / ↑(Nat.factorial 2) ^ 2 = 9 ∧
      (Matrix.gram ℝ fun j => ![O, P 0, P 2] j.succ - ![O, P 0, P 2] 0).det / ↑(Nat.factorial 2) ^ 2 = 9 / 4 ∧
        (Matrix.gram ℝ fun j => ![O, P 0, P 1] j.succ - ![O, P 0, P 1] 0).det / ↑(Nat.factorial 2) ^ 2 = 1
DeGua.l14w_cauchy_binet : have A := !![1, 2, 0; 0, 1, 1];
have B := !![1, 0; 1, 1; 0, 2];
(A * B).det = 7 ∧ (A * B).det ≠ 0 ∧ ∑ s with StrictMono s, (A.submatrix id s).det * (B.submatrix s id).det = (A * B).det
```

### japanese-theorem
```
@Japanese.l14_triInradius_eq : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [inst_4 : Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) (s : EuclideanGeometry.Sphere P) {a b c : P},
  a ∈ s →
    b ∈ s →
      c ∈ s →
        0 < (o.areaForm (b -ᵥ a)) (c -ᵥ a) →
          ∀ (h : AffineIndependent ℝ ![a, b, c]),
            { points := ![a, b, c], independent := h }.inradius =
              (o.areaForm (b -ᵥ a)) (s.center -ᵥ a) / Dist.dist a b +
                    (o.areaForm (c -ᵥ b)) (s.center -ᵥ b) / Dist.dist b c +
                  (o.areaForm (a -ᵥ c)) (s.center -ᵥ c) / Dist.dist c a -
                s.radius
@Japanese.l14_japanese_quadrilateral : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [inst_4 : Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) (s : EuclideanGeometry.Sphere P) {A B C D : P},
  A ∈ s →
    B ∈ s →
      C ∈ s →
        D ∈ s →
          0 < (o.areaForm (B -ᵥ A)) (C -ᵥ A) →
            0 < (o.areaForm (C -ᵥ A)) (D -ᵥ A) →
              0 < (o.areaForm (B -ᵥ A)) (D -ᵥ A) →
                0 < (o.areaForm (C -ᵥ B)) (D -ᵥ B) →
                  ∀ (i₁ : AffineIndependent ℝ ![A, B, C]) (i₂ : AffineIndependent ℝ ![A, C, D])
                    (i₃ : AffineIndependent ℝ ![A, B, D]) (i₄ : AffineIndependent ℝ ![B, C, D]),
                    { points := ![A, B, C], independent := i₁ }.inradius +
                        { points := ![A, C, D], independent := i₂ }.inradius =
                      { points := ![A, B, D], independent := i₃ }.inradius +
                        { points := ![B, C, D], independent := i₄ }.inradius
@Japanese.l14_japanese_polygon : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [inst_4 : Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) (s : EuclideanGeometry.Sphere P) (p : ℕ → P)
  (n : ℕ),
  2 ≤ n →
    (∀ l < n, p l ∈ s) →
      (∀ (a b c : ℕ), a < b → b < c → c < n → 0 < (o.areaForm (p b -ᵥ p a)) (p c -ᵥ p a)) →
        ∀ {E E' : Finset (ℕ × ℕ)},
          ((∀ e ∈ E, e.1 < e.2 ∧ e.2 ≤ n - 1) ∧
              (∀ e ∈ E, ∀ f ∈ E, e ≠ f → ¬∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) ∧
                ∀ (e : ℕ × ℕ),
                  e.1 < e.2 →
                    e.2 ≤ n - 1 →
                      (∀ f ∈ E, e ≠ f → ¬∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) → e ∈ E) →
            ((∀ e ∈ E', e.1 < e.2 ∧ e.2 ≤ n - 1) ∧
                (∀ e ∈ E', ∀ f ∈ E', e ≠ f → ¬∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) ∧
                  ∀ (e : ℕ × ℕ),
                    e.1 < e.2 →
                      e.2 ≤ n - 1 →
                        (∀ f ∈ E', e ≠ f → ¬∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) → e ∈ E') →
              (∑ t ∈ Finset.range n ×ˢ Finset.range n ×ˢ Finset.range n with
                  (t.1, t.2.1) ∈ E ∧ (t.2.1, t.2.2) ∈ E ∧ (t.1, t.2.2) ∈ E,
                  if h : AffineIndependent ℝ ![p t.1, p t.2.1, p t.2.2] then
                    { points := ![p t.1, p t.2.1, p t.2.2], independent := h }.inradius
                  else 0) =
                ∑ t ∈ Finset.range n ×ˢ Finset.range n ×ˢ Finset.range n with
                  (t.1, t.2.1) ∈ E' ∧ (t.2.1, t.2.2) ∈ E' ∧ (t.1, t.2.2) ∈ E',
                  if h : AffineIndependent ℝ ![p t.1, p t.2.1, p t.2.2] then
                    { points := ![p t.1, p t.2.1, p t.2.2], independent := h }.inradius
                  else 0
Japanese.l14w_japanese_quadrilateral : have A := 1;
have B := (3 + 4 * Complex.I) / 5;
have C := -1;
have D := -Complex.I;
∃ (i₁ : AffineIndependent ℝ ![A, B, C]) (i₂ : AffineIndependent ℝ ![A, C, D]) (i₃ : AffineIndependent ℝ ![A, B, D]) (i₄
  : AffineIndependent ℝ ![B, C, D]),
  (A ∈ { center := 0, radius := 1 } ∧
      B ∈ { center := 0, radius := 1 } ∧ C ∈ { center := 0, radius := 1 } ∧ D ∈ { center := 0, radius := 1 }) ∧
    (A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D) ∧
      (0 < (Complex.orientation.areaForm (B -ᵥ A)) (C -ᵥ A) ∧
          0 < (Complex.orientation.areaForm (C -ᵥ A)) (D -ᵥ A) ∧
            0 < (Complex.orientation.areaForm (B -ᵥ A)) (D -ᵥ A) ∧
              0 < (Complex.orientation.areaForm (C -ᵥ B)) (D -ᵥ B)) ∧
        (0 < { points := ![A, B, C], independent := i₁ }.inradius ∧
            0 < { points := ![A, C, D], independent := i₂ }.inradius ∧
              0 < { points := ![A, B, D], independent := i₃ }.inradius ∧
                0 < { points := ![B, C, D], independent := i₄ }.inradius) ∧
          { points := ![A, B, C], independent := i₁ }.inradius + { points := ![A, C, D], independent := i₂ }.inradius =
            { points := ![A, B, D], independent := i₃ }.inradius + { points := ![B, C, D], independent := i₄ }.inradius
Japanese.l14w_japanese_polygon : have p := fun k => [1, (3 + 4 * Complex.I) / 5, -1, -Complex.I].getD k 0;
have E := {(0, 1), (1, 2), (2, 3), (0, 3), (0, 2)};
have E' := {(0, 1), (1, 2), (2, 3), (0, 3), (1, 3)};
E ≠ E' ∧
  (∀ l < 4, p l ∈ { center := 0, radius := 1 }) ∧
    (∀ (a b c : ℕ), a < b → b < c → c < 4 → 0 < (Complex.orientation.areaForm (p b -ᵥ p a)) (p c -ᵥ p a)) ∧
      ((∀ e ∈ E, e.1 < e.2 ∧ e.2 ≤ 4 - 1) ∧
          (∀ e ∈ E, ∀ f ∈ E, e ≠ f → ¬∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) ∧
            ∀ (e : ℕ × ℕ),
              e.1 < e.2 →
                e.2 ≤ 4 - 1 → (∀ f ∈ E, e ≠ f → ¬∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) → e ∈ E) ∧
        ((∀ e ∈ E', e.1 < e.2 ∧ e.2 ≤ 4 - 1) ∧
            (∀ e ∈ E', ∀ f ∈ E', e ≠ f → ¬∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) ∧
              ∀ (e : ℕ × ℕ),
                e.1 < e.2 →
                  e.2 ≤ 4 - 1 →
                    (∀ f ∈ E', e ≠ f → ¬∃ q, Sbtw ℝ (p e.1) q (p e.2) ∧ Sbtw ℝ (p f.1) q (p f.2)) → e ∈ E') ∧
          (∑ t ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4 with
              (t.1, t.2.1) ∈ E ∧ (t.2.1, t.2.2) ∈ E ∧ (t.1, t.2.2) ∈ E,
              if h : AffineIndependent ℝ ![p t.1, p t.2.1, p t.2.2] then
                { points := ![p t.1, p t.2.1, p t.2.2], independent := h }.inradius
              else 0) =
            ∑ t ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4 with
              (t.1, t.2.1) ∈ E' ∧ (t.2.1, t.2.2) ∈ E' ∧ (t.1, t.2.2) ∈ E',
              if h : AffineIndependent ℝ ![p t.1, p t.2.1, p t.2.2] then
                { points := ![p t.1, p t.2.1, p t.2.2], independent := h }.inradius
              else 0
```

### poncelet-triangles
```
@Poncelet3.l14_euler : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
  [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (t : Affine.Triangle ℝ P),
  Dist.dist (Affine.Simplex.circumcenter t) (Affine.Simplex.incenter t) ^ 2 =
    Affine.Simplex.circumradius t * (Affine.Simplex.circumradius t - 2 * Affine.Simplex.inradius t)
@Poncelet3.l14_euler_excenter : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (t : Affine.Triangle ℝ P)
  (i : Fin 3),
  Dist.dist (Affine.Simplex.circumcenter t) (Affine.Simplex.excenter t {i}) ^ 2 =
    Affine.Simplex.circumradius t * (Affine.Simplex.circumradius t + 2 * Affine.Simplex.exradius t {i})
@Poncelet3.l14_exists_poncelet_triangle : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    ω.radius < Γ.radius →
      Dist.dist Γ.center ω.center ^ 2 = Γ.radius * (Γ.radius - 2 * ω.radius) →
        ∀ {A : P},
          A ∈ Γ →
            ∃ B C,
              B ∈ Γ ∧
                C ∈ Γ ∧
                  A ≠ B ∧
                    A ≠ C ∧ B ≠ C ∧ ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, A, C] ∧ ω.IsTangent line[ℝ, B, C]
@Poncelet3.l14_euler_of_isTangent : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P) {A B C : P},
  A ∈ Γ →
    B ∈ Γ →
      C ∈ Γ →
        A ≠ B →
          A ≠ C →
            B ≠ C →
              ω.IsTangent line[ℝ, A, B] →
                ω.IsTangent line[ℝ, A, C] →
                  ω.IsTangent line[ℝ, B, C] →
                    Dist.dist ω.center Γ.center < Γ.radius →
                      Dist.dist Γ.center ω.center ^ 2 = Γ.radius * (Γ.radius - 2 * ω.radius)
@Poncelet3.l14_poncelet_triangle_iff : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    ω.radius < Γ.radius →
      Dist.dist ω.center Γ.center < Γ.radius →
        ((∀ A ∈ Γ,
            ∃ B C,
              B ∈ Γ ∧
                C ∈ Γ ∧
                  A ≠ B ∧
                    A ≠ C ∧ B ≠ C ∧ ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, A, C] ∧ ω.IsTangent line[ℝ, B, C]) ↔
          Dist.dist Γ.center ω.center ^ 2 = Γ.radius * (Γ.radius - 2 * ω.radius))
@Poncelet3.l14_poncelet_construction : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    ω.radius < Γ.radius →
      Dist.dist Γ.center ω.center ^ 2 = Γ.radius * (Γ.radius - 2 * ω.radius) →
        ∀ {A : P},
          A ∈ Γ →
            ∀ {ℓ₁ ℓ₂ : AffineSubspace ℝ P},
              ℓ₁ ∈ ω.tangentsFrom A →
                ℓ₂ ∈ ω.tangentsFrom A →
                  ℓ₁ ≠ ℓ₂ → ∀ {B C : P}, B ∈ Γ → B ∈ ℓ₁ → B ≠ A → C ∈ Γ → C ∈ ℓ₂ → C ≠ A → ω.IsTangent line[ℝ, B, C]
@Poncelet3.l14_poncelet_construction_iff : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    ω.radius < Γ.radius →
      Dist.dist ω.center Γ.center < Γ.radius →
        ∀ {A : P},
          A ∈ Γ →
            (((∃ ℓ₁ ∈ ω.tangentsFrom A,
                  ∃ ℓ₂ ∈ ω.tangentsFrom A, ℓ₁ ≠ ℓ₂ ∧ ∃ B C, B ∈ Γ ∧ B ∈ ℓ₁ ∧ B ≠ A ∧ C ∈ Γ ∧ C ∈ ℓ₂ ∧ C ≠ A) ∧
                ∀ ℓ₁ ∈ ω.tangentsFrom A,
                  ∀ ℓ₂ ∈ ω.tangentsFrom A,
                    ℓ₁ ≠ ℓ₂ →
                      ∀ (B C : P), B ∈ Γ → B ∈ ℓ₁ → B ≠ A → C ∈ Γ → C ∈ ℓ₂ → C ≠ A → ω.IsTangent line[ℝ, B, C]) ↔
              Dist.dist Γ.center ω.center ^ 2 = Γ.radius * (Γ.radius - 2 * ω.radius))
@Poncelet3.l14_poncelet_all_or_nothing : ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V]
  [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P]
  [Fact (Module.finrank ℝ V = 2)] (Γ ω : EuclideanGeometry.Sphere P),
  0 < ω.radius →
    ω.radius < Γ.radius →
      Dist.dist ω.center Γ.center < Γ.radius →
        ∀ {A : P},
          A ∈ Γ →
            (((∃ ℓ₁ ∈ ω.tangentsFrom A,
                  ∃ ℓ₂ ∈ ω.tangentsFrom A, ℓ₁ ≠ ℓ₂ ∧ ∃ B C, B ∈ Γ ∧ B ∈ ℓ₁ ∧ B ≠ A ∧ C ∈ Γ ∧ C ∈ ℓ₂ ∧ C ≠ A) ∧
                ∀ ℓ₁ ∈ ω.tangentsFrom A,
                  ∀ ℓ₂ ∈ ω.tangentsFrom A,
                    ℓ₁ ≠ ℓ₂ →
                      ∀ (B C : P), B ∈ Γ → B ∈ ℓ₁ → B ≠ A → C ∈ Γ → C ∈ ℓ₂ → C ≠ A → ω.IsTangent line[ℝ, B, C]) ↔
              ∀ A' ∈ Γ,
                (∃ ℓ₁ ∈ ω.tangentsFrom A',
                    ∃ ℓ₂ ∈ ω.tangentsFrom A', ℓ₁ ≠ ℓ₂ ∧ ∃ B C, B ∈ Γ ∧ B ∈ ℓ₁ ∧ B ≠ A' ∧ C ∈ Γ ∧ C ∈ ℓ₂ ∧ C ≠ A') ∧
                  ∀ ℓ₁ ∈ ω.tangentsFrom A',
                    ∀ ℓ₂ ∈ ω.tangentsFrom A',
                      ℓ₁ ≠ ℓ₂ →
                        ∀ (B C : P), B ∈ Γ → B ∈ ℓ₁ → B ≠ A' → C ∈ Γ → C ∈ ℓ₂ → C ≠ A' → ω.IsTangent line[ℝ, B, C])
Poncelet3.l14w_poncelet : have Γ := { center := 2 + 3 / 2 * Complex.I, radius := 5 / 2 };
have ω := { center := 1 + Complex.I, radius := 1 };
(0 < ω.radius ∧
    ω.radius < Γ.radius ∧
      Dist.dist Γ.center ω.center ^ 2 = Γ.radius * (Γ.radius - 2 * ω.radius) ∧ Dist.dist ω.center Γ.center < Γ.radius) ∧
  (0 ∈ Γ ∧
      4 ∈ Γ ∧
        3 * Complex.I ∈ Γ ∧
          0 ≠ 4 ∧
            0 ≠ 3 * Complex.I ∧
              4 ≠ 3 * Complex.I ∧
                ω.IsTangent line[ℝ, 0, 4] ∧
                  ω.IsTangent line[ℝ, 0, 3 * Complex.I] ∧ ω.IsTangent line[ℝ, 4, 3 * Complex.I]) ∧
    (∀ A ∈ Γ,
        ∃ B C,
          B ∈ Γ ∧
            C ∈ Γ ∧
              A ≠ B ∧
                A ≠ C ∧ B ≠ C ∧ ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, A, C] ∧ ω.IsTangent line[ℝ, B, C]) ∧
      ∀ A ∈ Γ,
        (∃ ℓ₁ ∈ ω.tangentsFrom A,
            ∃ ℓ₂ ∈ ω.tangentsFrom A, ℓ₁ ≠ ℓ₂ ∧ ∃ B C, B ∈ Γ ∧ B ∈ ℓ₁ ∧ B ≠ A ∧ C ∈ Γ ∧ C ∈ ℓ₂ ∧ C ≠ A) ∧
          ∀ ℓ₁ ∈ ω.tangentsFrom A,
            ∀ ℓ₂ ∈ ω.tangentsFrom A,
              ℓ₁ ≠ ℓ₂ → ∀ (B C : ℂ), B ∈ Γ → B ∈ ℓ₁ → B ≠ A → C ∈ Γ → C ∈ ℓ₂ → C ≠ A → ω.IsTangent line[ℝ, B, C]
Poncelet3.l14w_euler : ∃ t,
  t.points = ![0, 4, 3 * Complex.I] ∧
    Affine.Simplex.circumcenter t = 2 + 3 / 2 * Complex.I ∧
      Affine.Simplex.circumradius t = 5 / 2 ∧
        Affine.Simplex.circumcenter t ≠ Affine.Simplex.incenter t ∧
          0 < Affine.Simplex.circumradius t * (Affine.Simplex.circumradius t - 2 * Affine.Simplex.inradius t) ∧
            Dist.dist (Affine.Simplex.circumcenter t) (Affine.Simplex.incenter t) ^ 2 =
              Affine.Simplex.circumradius t * (Affine.Simplex.circumradius t - 2 * Affine.Simplex.inradius t)
```
