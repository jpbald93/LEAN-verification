# L15 — Classical comparer, Paper A (Desargues / Monge / Simson / Napoleon / Lami)

Inputs: paper `AFM/CoordCertificates/paper.tex`; blind writer file `/tmp/blindA/Classical.lean` (namespace `PaperAClassical`, 14 sorried declarations) and its `CLASSICAL_REPORT.md`; textbook statements `/tmp/blindA/classical_statements.txt`.
Machine: john (`~/lean/jl`). Wall time: 03:21 → 04:17 EDT (about 56 min).

## Fresh clones (published pinned commits)

| repo | clone | commit | `jl build` | gate |
|---|---|---|---|---|
| desargues | `~/lean/l15A_desargues` | b6409255c844abb6e1cad80b23f8182fc3934116 | rc 0 | `PASS (24 declarations, standard axioms only)` |
| monge | `~/lean/l15A_monge` | a01f7504d12fd492dd30c66f880905b21cca3895 | rc 0 | `PASS (7 declarations, standard axioms only)` |
| simson | `~/lean/l15A_simson` | 7c239b31600575db241b45dda4930cf9486e7d17 | rc 0 | `PASS (12 declarations, standard axioms only)` |
| napoleon | `~/lean/l15A_napoleon` | e16592ae04be8e5516a2caef52418c6c60df5165 | rc 0 | `PASS (21 declarations, standard axioms only)` |
| lami | `~/lean/l15A_lami` | ea6b038b1a3eebd9b02465650901f4b5d4ddaf19 | rc 0 | `PASS (17 declarations, standard axioms only)` |

All five use toolchain v4.33.1 and Mathlib 0df444a3, so `.lake/packages` is a symlink to `~/lean/clifford/.lake/packages`. No l14 library was used.

**Gate note:** at the pinned commits, `gate.sh` needs GNU `mktemp --suffix`. Under `jl gate` (BSD system tools) all five fail with `FAIL: axiom report` (rc 1). Under `jl -g gate` (GNU tools) all five PASS, as above. This matches the paper's statement that the BSD portability fix came in a later commit that does not touch any Lean source. Logs: `~/lean/l15A_<repo>.gate.log` and `.build.log`.

## Classification

Each writer statement is copied verbatim and packaged as `def classical_X : Prop`. All proofs are in `namespace L15Compare`.

| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| `classical_A1_a` (Desargues ⇒) | **E** | `cov_A1_a` | — | From `Desargues.desargues_det`. Glue: `pline y z` is the projectivisation of `span{y.rep, z.rep}`; membership is `x·(y×z)=0`; a common point of two distinct lines is `mk((y×z)×(y'×z'))`; `PCollinear` (Mathlib `Dependent`) is `br = 0`. Uses only the writer's hypotheses: `PTriangle` gives the vertex inequalities; `A≠A'` etc. are unused. |
| `classical_A1_b` (Desargues ⇐) | **E** | `cov_A1_b` | — | From `Desargues.desargues_converse_det` and `exists_dotProduct_eq_zero_of_br_eq_zero`. The concurrency point is built explicitly; `A≠A'` etc. make `AA'` a genuine line. |
| `classical_A1_obligation` | **O** → proved | `cov_A1_obligation` | — | NEW PROOF (the paper does not state it): two distinct lines meet in exactly one point. |
| `classical_A2_a` (Monge) | **E** | `cov_A2_a` | — | From `Monge.monge` and `Monge.det3_eq_zero_iff_collinear`, transported along the linear map ℝ×ℝ → `EuclideanSpace ℝ (Fin 2)`. NEW glue lemma `ext_eq_of_isExt`: the writer's defining property ("homothety with ratio r_t/r_s maps circle s onto circle t") forces `(r_s−r_t)E = r_s O_t − r_t O_s`, i.e. `E = Monge.ext`; proved by testing two antipodal points. The centre-distinctness hypotheses are unused. |
| `classical_A2_b` (E₁₂, I₂₃, I₁₃) | **E** (via instantiation) | `cov_A2_b` | — | The paper only *remarks* this instantiation (replace r₃ by −r₃); it is not a library declaration. Proved here as `Monge.monge … s₁.radius s₂.radius (-s₃.radius)`, with glue `int_eq_of_isInt` (Wbtw + ratio gives `(r_s+r_t)I = r_t O_s + r_s O_t`). Uses `O₂≠O₃` and `O₁≠O₃`; `hr₂₃` and `hr₁₃` are unused, as the writer flagged. |
| `classical_A2_obligation_ext` | **O** → proved | `cov_A2_obligation_ext` | — | NEW PROOF: existence (explicit E, image of the sphere computed in both directions) and uniqueness (via `ext_eq_of_isExt`). |
| `classical_A2_obligation_int` | **O** → proved | `cov_A2_obligation_int` | — | NEW PROOF: `I = lineMap O_s O_t (r_s/(r_s+r_t))`; uniqueness via `int_eq_of_isInt`. |
| `classical_A3_a` (Simson ⇒) | **E** | `cov_A3_a` | — | From `Simson.simson` and the bridge `perpFoot_eq_orthogonalProjection`, transported along the isometry `Complex.orthonormalBasisOneI.repr : ℂ ≃ₗᵢ ℝ²` (`orthogonalProjection_map`, `AffineSubspace.map_span`). Membership in the circumsphere gives `Cospherical {a,b,c,p}`. |
| `classical_A3_b` (Simson converse) | **O** (paper explicitly does not prove it) → **proved** | `cov_A3_b` | — | NEW PROOF. The paper says the missing piece is the bridge "Collinear ⇒ area2 = 0". I proved it (`area2_eq_zero_of_collinear`, 8 lines) and chained it: `area2_perpFoot_eq_zero_iff` → `concyc = 0` → `concyc_eq_zero_iff_cospherical` → membership in `Affine.Simplex.circumsphere` (`eq_circumcenter_of_dist_eq` / `eq_circumradius_of_dist_eq`; in the plane the centre lies in the affine span). So the geometric converse follows from repository theorems plus a short bridge. |
| `classical_A4_a` (outer Napoleon, **non-degenerate**) | **E** | `cov_A4_a` | — | From `Napoleon.napoleon_outer` / `napoleon_inner` and the bridges `Ga/Gb/Gc_eq_centroid`. NEW glue: (i) strict sides `SOppSide`/`SSameSide` of `line[u,v]` are characterised by the sign of the cross product; (ii) an equilateral apex is `apex ωo` or `apex ωi` according to that sign. For a clockwise triangle the outward apexes are `apex ωi`, so the library's "inner" theorem gives the outer triangle. Hence the library's ω choice matches "outer" only for counter-clockwise triangles; this is not a gap, because `napoleon_general` covers both rotations. Non-degeneracy (the writer's extra `AffineIndependent` conjunct) is a NEW PROOF: an explicit identity for the doubled signed area of the Napoleon triangle, `S/2 ± √3·Σ|side|²/12`, which is nonzero for the outer triangle. |
| `classical_A4_b` (inner Napoleon, distances only) | **E** | `cov_A4_b` | — | Same glue, with the orientation swap. |
| `classical_A4_obligation` | **D** — false as written | `A4_obligation_false : ¬ classical_A4_obligation`; corrected: `cov_A4_obligation_corrected` | the hypothesis `U ≠ V` | Writer error: `U ≠ V` is omitted. Counterexample: U = V = 0, W = e₀. Then `line[ℝ,0,0] = {0}`, W is off it, the only apex is X = 0, which lies on the line, so no X is strictly on either side. With `U ≠ V` added, the obligation is proved (NEW PROOF). The textbook statement presupposes a non-degenerate segment, so this mis-states the textbook; the paper is not at fault. |
| `classical_A5` (Lami) | **E** | `cov_A5` | — | From `Lami.lami`. The writer's non-collinearity hypothesis gives F₁, F₂, F₃ ≠ 0 (`ne_zero_of_nc`). |
| `classical_A5_obligation` | **E** | `cov_A5_obligation`; with A5: `cov_A5_nondegenerate` | — | From `Lami.lami_sin_ne_zero`. Non-collinearity rules out ∠(F₁,F₂) ∈ {0, π} (`angle_ne_of_nc`). Together with `cov_A5` this is the paper's Thm `lami_nondegenerate`. |

**Summary:**
- E: 9 (A1a, A1b, A2a, A2b, A3a, A4a, A4b, A5, A5-obligation).
- O, proved anyway: 4 (A1-obligation, A2-obligation-ext, A2-obligation-int, and A3b, the Simson converse the paper disclaims).
- D: 1 (A4-obligation is false as written because the writer omitted `U ≠ V`; the corrected form is proved).
- N: none.

Nothing stays open.

## NEW PROOFS (not in any repository)
- `cov_A3_b`: geometric converse of Wallace–Simson, including the missing bridge `area2_eq_zero_of_collinear`. The paper (§Simson, limits) lists this as not formalised.
- `cov_A4_a`, non-degeneracy part: the outer Napoleon triangle is affinely independent, via the signed-area identities `cr_napoleon_o` / `cr_napoleon_i`.
- `cov_A2_b` as a declaration: the paper only describes the instantiation `r₃ ↦ −r₃` in prose.
- Synthetic ↔ coordinate glue:
  - Monge: the homothety-image definition ⇒ the `Monge.ext` formula; the Wbtw/ratio definition ⇒ the internal-centre formula.
  - Napoleon: `SOppSide`/`SSameSide` ⇔ cross-product sign; equilateral apex classification.
  - Desargues: `Subspace.span` lines ⇔ dot-product equations; distinct lines meet in the cross of their normals.
- Obligations proved: `cov_A1_obligation`, `cov_A2_obligation_ext`, `cov_A2_obligation_int`, `cov_A5_obligation`, `cov_A4_obligation_corrected`.

## Construction obligations
Every writer obligation is either proved or refuted, with no extra hypotheses carried. The one exception is A4: the statement as written is refuted (`A4_obligation_false`), and the corrected version adds `U ≠ V` (`cov_A4_obligation_corrected`).

## Compile results (`~/lean/jl lake env lean scratch/L15_compare.lean`, in each fresh clone)
| repo | rc | errors | warnings |
|---|---|---|---|
| desargues | 0 | 0 | 0 |
| monge | 0 | 0 | 5 (unused-simp-arg / unused-variable linters only) |
| simson | 0 | 0 | 0 |
| napoleon | 0 | 0 | 0 |
| lami | 0 | 0 | 0 |

Logs: `~/lean/l15A_<repo>.compare.log`.

## Forbidden-token grep
`grep -nE "sorry|admit|native_decide|axiom" <all 5 scratch files> | grep -v "#print axioms"` returns no matches (rc 1). The only hits for `axiom` are the `#print axioms` lines.

## #print axioms
Every theorem listed below prints exactly `[propext, Classical.choice, Quot.sound]`:
- `cov_A1_obligation`, `cov_A1_a`, `cov_A1_b`
- `cov_A2_a`, `cov_A2_b`, `cov_A2_obligation_ext`, `cov_A2_obligation_int`
- `cov_A3_a`, `cov_A3_b`
- `cov_A4_a`, `cov_A4_b`, `A4_obligation_false`, `cov_A4_obligation_corrected`
- `cov_A5`, `cov_A5_obligation`, `cov_A5_nondegenerate`

## Library hashes
Computed with `find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`. Before and after are identical for every repo:

| repo | before = after |
|---|---|
| desargues | ccf54d817ae516e3d1219f43ee212430ed2ff237c5a7605f348d45e9c0fe4f58 |
| monge | a8997a2030a394cbc8a881e03eba4cf7c906513d935747923b9ccbd78c8d0c64 |
| simson | c89b614176c6cdf4bb671cdad0342c311696a33ef97d9fbf3c769e4eaacc8422 |
| napoleon | da6e7351dde2f3d0b0d058d87b3ea8e8094144c161cafe752a8e5115f9a78221 |
| lami | 156e036cb8900f42f518519b1e04e09634f72049700f9fb1e38ba76ec1b5a4fa |

`git status --porcelain` shows only the untracked `scratch/` in each clone. Hash files: `~/lean/l15A_<repo>.sha_before` and `.sha_after`.

## Scratch paths
- On john: `~/lean/l15A_{desargues,monge,simson,napoleon,lami}/scratch/L15_compare.lean`.
- Local copies: `AFM/L14L15/A/L15_scratch/L15_compare_<repo>.lean`; working copies in `/tmp/l15A/`.
- Sizes: desargues 249, monge 256, simson 159, napoleon 497, lami 93 lines.

## Comments for the paper
1. Every textbook statement in A1–A5 now follows from repository theorems plus short glue, including the Simson converse the paper calls unformalised. The missing bridge (Collinear ⇒ area2 = 0) is 8 lines. The paper could cite or add it.
2. Napoleon: the library's `ωo` is "outer" only for counter-clockwise triangles (as `apex_outward` documents). With an orientation-free outward hypothesis (`SOppSide`), clockwise triangles need `napoleon_inner`. Both are in the library, so coverage is complete, but the naming is orientation-dependent.
3. Monge's companion form (one external, two internal centres) is true under the writer's hypotheses and follows from `Monge.monge` exactly as the paper's prose describes.
