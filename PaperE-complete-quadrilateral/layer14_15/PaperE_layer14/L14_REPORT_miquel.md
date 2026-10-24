# Layer 14 (Paper E pilot) — Mathlib-only restatement + witnesses

Repos (fresh clones of the published commits, on john): `~/lean/l14E_newton` @ 48e94cf9, `~/lean/l14E_miquel` @ 011c9ecd.
New files: `QuadNewton/L14Newton.lean` (832 lines), `QuadMiquel/L14Miquel.lean` (861 lines).
Other changes: one import line appended at the end of each root file; the REQUIRED line in each `gate.sh` was extended. Nothing else edited, nothing committed or pushed.
The same report is in both repo roots.

Baseline (fresh clone, before any change): newton `jl build` rc 0, gate `PASS (35 declarations, standard axioms only)`;
miquel `jl build` rc 0, gate `PASS (62 declarations, standard axioms only)`.

## Summary table

| theorem (library) | l14 done | namespace-free verified | witness (A generic / P with L1⟂L2) | distinctness proved | notes |
|---|---|---|---|---|---|
| QuadNewton.newton_gauss | `l14_newton_gauss` | yes | `l14w_newton_gauss`, `_perp` | 3 pairwise-distinct midpoints, given explicitly | `midpoint ℝ` of the diagonals |
| QuadNewton.diag_midpoints_ne | `l14_diag_midpoints_ne` | yes | `l14w_diag_midpoints_ne`, `_perp` | (the conclusion is itself a distinctness statement) | covers all **3** pairs; the library theorem covers 1 pair (taken from `bodenmiller_coaxal`) |
| QuadNewton.orthocentres_collinear | `l14_orthocentres_collinear` | yes | `l14w_orthocentres_collinear`, `_perp` | A: 4 pairwise distinct H; P: 3 distinct, H3 = H4 | `Affine.Triangle.orthocenter` |
| QuadNewton.orthocentres_not_all_eq | `l14_orthocentres_not_all_eq` | yes | `l14w_orthocentres_not_all_eq`, `_perp` | proves the disjunct H2 ≠ H4 | same shape as the library: H3≠H4 ∨ H2≠H4 |
| QuadNewton.bodenmiller | `l14_bodenmiller` | yes | `l14w_bodenmiller`, `_perp` | explicit common powers (A: −5/2, 10, 2, −1/2); the 3 circle centres are distinct; H's distinct | uses `EuclideanGeometry.Sphere.power` (present at the pinned revision) on `⟨midpoint ℝ P Q, dist P Q / 2⟩` |
| QuadNewton.orthocentre_line_perp | `l14_orthocentre_line_perp` | yes | `l14w_orthocentre_line_perp`, `_perp` | both direction vectors nonzero (genuine lines) | `inner ℝ` on ℂ, ∀ H₁ H₂ in the set of orthocentres |
| QuadMiquel.miquel | `l14_miquel` (∃!) | yes | `l14w_miquel`, `_perp` | M ≠ each of the 6 vertices; the 4 circumcentres pairwise distinct | M stated via `Affine.Simplex.circumsphere` |
| QuadMiquel.steiner_circle | `l14_steiner_circle` | yes | `l14w_steiner_circle`, `_perp` | 5 pairwise distinct points (O1..O4, M) | holds for **any** M on the four circumspheres; `EuclideanGeometry.Cospherical` |
| QuadMiquel.simson | `l14_simson` | yes | `l14w_simson`, `_perp` | 4 pairwise distinct feet | `EuclideanGeometry.orthogonalProjection line[ℝ,pᵢ,qᵢ] M`, any M on the four circumspheres |
| QuadMiquel.steiner_parallel_line | `l14_steiner_parallel_line` | yes | `l14w_steiner_parallel_line`, `_perp` | feet on L1, L2 distinct (genuine Simson line); H's: A 4 distinct, P 3 distinct with H3 = H4 | parallel to `affineSpan` of the 4 orthocentres; **no extra hypothesis needed**, and the P witness covers the L1⟂L2 case |

Also added: `l14_triangles_exist` in each repo. It shows that the four Mathlib triangles with the given vertices exist, so the `e₁…e₄` hypotheses can be satisfied.

**Coverage: 10/10 main theorems restated, and each has 2 witnesses (20 in total).**

## The Mathlib-only setting
- Data: p₁ q₁ … p₄ q₄ : ℂ with pᵢ ≠ qᵢ, and lines `line[ℝ, pᵢ, qᵢ]`.
- General position: `¬ line[ℝ,pᵢ,qᵢ].Parallel line[ℝ,pⱼ,qⱼ]` for all six pairs, and `¬ ∃ z, z ∈ Lᵢ ∧ z ∈ Lⱼ ∧ z ∈ Lₖ` for all four triples.
- Vertices: arbitrary points `aᵢⱼ` with `aᵢⱼ ∈ Lᵢ ∧ aᵢⱼ ∈ Lⱼ`.
- Triangles: arbitrary `Tₖ : Affine.Triangle ℝ ℂ` with `Tₖ.points = ![…]`.
- Miquel point: any M with M ∈ Tₖ.circumsphere for k = 1..4.

## Bridges (new, `l14b_*`)
**Newton:**
- `l14b_mem`, `l14b_mem_iff` (carrier ↔ line[ℝ,p,q], and its `cr` form)
- `l14b_genPos` (Mathlib hypotheses → `GenPos`, via `genPos_iff`)
- `l14b_meet`, `l14b_setup` (any common point = `meet`)
- `l14b_tri`, `l14b_orthocenter`, `l14b_setupT` (arbitrary triangle with the given points = library triangle; via `ortho_eq_orthocenter`)
- `l14b_midpoint` (midpoint ℝ x y = (x+y)/2)
- `l14b_sphere` (Mathlib sphere = `diamCircle`)
- `l14b_parallel_iff`, `l14b_noconc` (used for the witnesses)

**Miquel:** the same set (`l14b_carrier, mem, mem_iff, genPos, meet, setup, tri, orthocenter, parallel_iff, noconc`), plus:
- `l14b_circumcenter`, `l14b_mem_circumsphere`, `l14b_setupT`
- `l14b_miquel` (any point on the 4 circumspheres = `miquelPt`, via `miquelPt_unique`)
- `l14b_miquel_mem`
- `l14b_foot` (orthogonalProjection = `foot`)

The library theorems used are `newton_gauss`, `bodenmiller_coaxal`, `orthocentres_collinear`, `orthocentres_not_all_eq`, `orthocentre_line_perp_inner`, `miquel`, `miquelPt_unique`, `steiner_circle`, `simson` and `steiner_parallel_line`, together with the existing Bridge lemmas (`genPos_iff`, `meet_eq_iff`, `carrier_eq_line`, `circ_eq_circumcenter`, `ortho_eq_orthocenter`, `foot_eq_orthogonalProjection`, `genPos_triangles`, `pw_eq_power`, `parallel_iff_cr`).
Several Miquel-side bridges follow the Paper F L14Parabola template almost verbatim, since both repos share the same model. The Newton-side bridges were adapted to that repo's names: `cr_comm` and `Line.toAffine`.

## FINDINGS
**No Mathlib-only statement turned out false, and none needed an extra hypothesis.** Points worth noting:
1. Steiner's parallel holds in Mathlib-only form with no perpendicularity hypothesis, because the target is the affine span of all four orthocentres. This includes the L1 ⟂ L2 case, where H3 = H4. The P witness exhibits exactly that case: H3 = H4 = 0, H1 = 1+i, H2 = 2+2i, and the span is still a line.
2. In `orthocentres_not_all_eq` the library's disjunction H3≠H4 ∨ H2≠H4 is the honest form, since two orthocentres can coincide (P: H3 = H4). In both witnesses the disjunct H2 ≠ H4 is proved.
3. `diag_midpoints_ne` (library: one pair) is restated in a stronger form covering all three pairs. This is legitimate because `bodenmiller_coaxal` already proves the other two.
4. In config P the orthocentre H3 = H4 = A12 has power 0 with respect to all three diagonal circles. This is consistent: it lies on the circle with diameter A12A34.

## Type-check (namespace-freeness)
Method: a scratch file (`set_option` only there, not in the library) containing `import Q.L14X`, `set_option pp.fullNames true`, `set_option pp.notation false`, and `#check @Q.<name>` for every `l14_*`/`l14w_*` theorem. In the output I stripped the declaration-name header and grepped for `QuadNewton.` / `QuadMiquel.`.
- Newton: rc 0, 2878 lines, 19 declarations checked, 0 errors, **0 occurrences**.
- Miquel: rc 0, 2166 lines, 13 declarations checked, 0 errors, **0 occurrences**.

The 32 declarations checked are the 6+4 main restatements, `l14_triangles_exist` in each repo, and all 20 witnesses. The `l14b_*`/`l14wb*` helpers mention local definitions by design and are not part of this check.
Excerpt (Newton):
```
@QuadNewton.l14_triangles_exist : ∀ {p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : Complex},
  Ne p₁ q₁ → … Not ((affineSpan Real (Insert.insert p₁ (Singleton.singleton q₁))).Parallel
                (affineSpan Real (Insert.insert p₂ (Singleton.singleton q₂)))) → …
```

## Gate / tamper (after the change)
- newton: `jl build` rc 0; `jl gate` → `PASS (70 declarations, standard axioms only)`; `jl tamper` → sorry, ax2line, evalfake, macro, wrap, falsehyp all rejected, `ALL TAMPERING TESTS REJECTED`.
- miquel: `jl build` rc 0; `jl gate` → `PASS (95 declarations, standard axioms only)`; `jl tamper` → `ALL TAMPERING TESTS REJECTED` (6/6).
- Forbidden-token scan of the new files: no matches. There is no sorry, admit, axiom, native_decide, #eval, set_option, macro, notation or run_cmd.

## Hashes (shasum -a 256)
All pre-existing library files are identical to the fresh clone. The only modified file in each repo is the root file, which had one import appended (see `git diff`):

**Newton (unchanged):**
- Basic 7514740705648ce85f70f0ad0c991a963baaa4b2ac8e5ae6c2b503e03d7040c3
- Bridge 902c885b3fe53ae1ccccf11e3d9e2a436945257f0d8b2269937f27f379bc1974
- Core b005e0198ac9477785862cf89ea5e1768cf66df900f9d4e5808cb6720c9f86fb
- Lines 55d37f730c57fddb76b9744ece554b1dfa73a16b422453c1bcaa6274d5aba9d7
- Quad 06783cf3344b232b4d3e321821e978a03500862c8593fbb1ceb0b202f3736aaa

**Newton (changed):**
- QuadNewton.lean 5cb4e2e8… → 082829ec… (one import appended)
- new L14Newton.lean 7554fe86600450803b3229f775bccab1b97a5187fdbada57f822fb46ede1b877
- gate.sh bb5e5c7b…

**Miquel (unchanged):**
- Algebra 95b548bc2ee7b7c87bbaa7ff03c74cf3722ce41ad2a26d634d9cf97101b47938
- Basic f7b4da7d2abf6c1f66b987defd25bf99be4bf10a6cf081c97af51dd1f52dcf12
- Bridge fb6f3e39230d5279dee671a62c70748ed1969d32df77815ba49f3145b68b29fa
- Frame 1e7cbfc90348e6884806654ff0c60085c6b3d807a6c2dec15aa7d3e126703fc8
- Miquel 5ce67f6891f4ec1c36c4ff6f1a789f076bef4fa567a579f63c03d7efa9f785a5
- Parallel ea33070625a616859d0ac8e145c1fe6224af0f2c9bbc28a84f1e4505f9d49e5f
- Simson 69b49c142ec7435ebfbea2fb2851f66a20c96fbdb9e48be3e67ecc0fae2936ce

**Miquel (changed):**
- QuadMiquel.lean 40e264fd… → ee73b0e0… (one import appended)
- new L14Miquel.lean 060f567bb1178563c35298095ace5332c48fb2fd899c4b000ada50a3ac6649a9
- gate.sh 675ee66b…

## REQUIRED names added
- **Newton (35):** QuadNewton.l14b_mem QuadNewton.l14b_mem_iff QuadNewton.l14b_genPos QuadNewton.l14b_meet QuadNewton.l14b_setup QuadNewton.l14b_tri QuadNewton.l14b_orthocenter QuadNewton.l14b_midpoint QuadNewton.l14b_sphere QuadNewton.l14b_setupT QuadNewton.l14b_parallel_iff QuadNewton.l14b_noconc QuadNewton.l14_triangles_exist QuadNewton.l14_newton_gauss QuadNewton.l14_diag_midpoints_ne QuadNewton.l14_orthocentres_collinear QuadNewton.l14_orthocentres_not_all_eq QuadNewton.l14_bodenmiller QuadNewton.l14_orthocentre_line_perp QuadNewton.l14wbA_base QuadNewton.l14wbA_master QuadNewton.l14w_newton_gauss QuadNewton.l14w_diag_midpoints_ne QuadNewton.l14w_orthocentres_collinear QuadNewton.l14w_orthocentres_not_all_eq QuadNewton.l14w_bodenmiller QuadNewton.l14w_orthocentre_line_perp QuadNewton.l14wbP_base QuadNewton.l14wbP_master QuadNewton.l14w_newton_gauss_perp QuadNewton.l14w_diag_midpoints_ne_perp QuadNewton.l14w_orthocentres_collinear_perp QuadNewton.l14w_orthocentres_not_all_eq_perp QuadNewton.l14w_bodenmiller_perp QuadNewton.l14w_orthocentre_line_perp_perp 
- **Miquel (33):** QuadMiquel.l14b_carrier QuadMiquel.l14b_mem QuadMiquel.l14b_mem_iff QuadMiquel.l14b_genPos QuadMiquel.l14b_meet QuadMiquel.l14b_setup QuadMiquel.l14b_tri QuadMiquel.l14b_orthocenter QuadMiquel.l14b_circumcenter QuadMiquel.l14b_mem_circumsphere QuadMiquel.l14b_setupT QuadMiquel.l14b_miquel QuadMiquel.l14b_miquel_mem QuadMiquel.l14b_parallel_iff QuadMiquel.l14b_noconc QuadMiquel.l14b_foot QuadMiquel.l14_triangles_exist QuadMiquel.l14_miquel QuadMiquel.l14_steiner_circle QuadMiquel.l14_simson QuadMiquel.l14_steiner_parallel_line QuadMiquel.l14wbA_base QuadMiquel.l14wbA_master QuadMiquel.l14w_miquel QuadMiquel.l14w_steiner_circle QuadMiquel.l14w_simson QuadMiquel.l14w_steiner_parallel_line QuadMiquel.l14wbP_base QuadMiquel.l14wbP_master QuadMiquel.l14w_miquel_perp QuadMiquel.l14w_steiner_circle_perp QuadMiquel.l14w_simson_perp QuadMiquel.l14w_steiner_parallel_line_perp 

## Configurations (picked and checked in Python first with exact Fractions: `py/cfg.py`, `py/chk.py`)

* **A (generic)**: L1 = line[0,1], L2 = line[1−i, −2+2i], L3 = line[−1+3i, −2], L4 = line[−1−2i, 3].
  Vertices A12=0, A13=−2, A14=3, A23=−3/2+3/2 i, A24=1−i, A34=−3−3i.
  Circumcentres O1..O4 = −3/2−i, 1/2−5/2 i, 3/2+1/2 i, −1+1/2 i. Orthocentres H1..H4 = −1/2−1/2 i, −3+2i, 1−2i, −3/2+1/2 i (pairwise distinct).
  Miquel point M = i. Feet of M on L1..L4 = 0, −1/2+1/2 i, −3/2+3/2 i, 1−i. Diagonal midpoints = −3/2−3/2 i, −1/2−1/2 i, 3/4+3/4 i.
  Common powers of H1..H4 w.r.t. the diagonal circles: −5/2, 10, 2, −1/2. Steiner circle: centre 1/4−3/4 i, r² = 25/8.
* **P (L1 ⟂ L2)**: L1 = line[0,1], L2 = line[0,i], L3 = line[−i, −1−2i], L4 = line[−2+3i, 2+i].
  A12=0, A13=1, A14=4, A23=−i, A24=2i, A34=2+i; H1=1+i, H2=2+2i, H3=H4=0; M=1−i;
  feet 1, −i, 1/2−1/2 i, 2+i; O1..O4 = 1/2+1/2 i, 5/2−1/2 i, 2+i, 1/2−1/2 i; powers −1, 2, 0, 0.

Every witness `l14w_*` (and `*_perp` for P) states: **all hypotheses** of the `l14_*` theorem for the concrete
configuration (p_i ≠ q_i, six `¬ Parallel`, four `¬ ∃ common point`, six vertex memberships), the existence of the
Mathlib triangles with the stated `points`, and the distinctness facts. Hypotheses are proved by
`norm_num [Complex.ext_iff, …]` after rewriting through `l14b_mem_iff` / `l14b_parallel_iff` / `l14b_noconc`;
Mathlib objects (orthocenter, circumcenter, orthogonalProjection, circumsphere membership) are evaluated through
the bridges and then `norm_num`. No `decide` needed.

## Wall time
About **20 minutes** wall-clock for both repos (18:37 → 18:57 EDT), including clone, both baseline builds and gates, Python checks, writing both files, gates and tamper.
The main speed-up came from the sibling Paper F template (bridges reused), plus a small Python generator that writes the long witness statements. Each witness file compiled after 2–4 iterations, about 7 s per check. For the rollout: expect roughly 20–40 min per paper when a template with the same model exists, and more if the model differs.
