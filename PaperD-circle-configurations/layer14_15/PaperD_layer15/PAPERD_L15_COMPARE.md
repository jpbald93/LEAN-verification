# Paper D — Layer 15 classical comparison

## Result and limits

**Seven main classical statements and three construction obligations are proved with their exact writer signatures.** Five further main statements have certified partial/scope comparisons. Three existence obligations remain open. All eight finished scratch files compile with exit **0**. All **48** `cov_` declarations (counting repeated transport lemmas in different repositories) have dependency output exactly `[propext, Classical.choice, Quot.sound]`. All library hashes are unchanged.

This is a **partial coverage audit, not an all-statements equivalence certificate**. In particular, full D1(c), full all-n D1(d), the omitted global-collision cases of D2, and identification of the writer's Fermat definitions in D3 are not proved here. No discrepancy is presented as a counterexample to a classical statement without a configuration meeting that statement's hypotheses.

Comparer: `genspark-llm-proxy/gpt-6-astra`. Writer source checked on jack:
`~/reformal/PaperDClassical.lean`, SHA256
`611b172409ce3579cc3fac0b6ce5fba308045c9657cf81bb6abad23540ad50cd`.
Read the writer report and classical source brief. Work used published repositories and Mathlib on jack through BatchMode SSH. No subagents, dependency updates, cache downloads, library edits, or unrelated-node jobs were used.

### Statement-copy convention

Every final scratch contains all the writer's own definitions and all 18 statement signatures, with bodies packaged as `def classical_* ... : Prop := ...` rather than imported unproved theorems. Parameter lists, hypotheses and conclusions are preserved; only theorem-to-proposition packaging removes the unproved bodies. Exact-coverage declarations `cov_D1_a`, `cov_D1_b`, `cov_D4`, `cov_D5`, `cov_D6_lower`, `cov_D6_upper`, `cov_D7`, `cov_D5_obligation`, `cov_D6_obligation`, `cov_D7_obligation` use the writer's signatures (the final obligation is textually restated equivalently). No writer theorem containing an unproved body is imported. A local script checked that the complete packaged statement block occurs verbatim in every final file.

## Comparison table

**E** = exact writer statement proved. **N** = certified coverage only under listed extra premises. **N / open bridge** is explicitly a limitation of this comparison, NOT evidence that the published result is mathematically narrower. **O** = the requested all-n positive theorem is not a theorem claimed by these published declarations. No **D** classification against a writer statement was justified.

All names below are in namespace `PaperDClassical`.

| Writer statement | E/N/D/O | Lean theorem(s) | What is missing | Note |
|---|---|---|---|---|
| D1_a | **E** | `cov_D1_a` | Nothing | Arbitrary common M, all supplied second points, and every ordered triple handled. Uses `Clifford.clifford_one`. |
| D1_b | **E** | `cov_D1_b` | Nothing relative to writer | Uses `clifford_two`; writer uniqueness identifies all five supplied X; writer noncollinearity removes line branch. |
| D1_c | **N / open bridge** | `cov_D1_c_part` | Six chosen canonical triples must be noncollinear; each normalized supplied C must equal the corresponding repository canonical circumcircle | This is not established as a genuine narrowing. `clifford_three` is used, but deriving canonical identification from hX/hXu/hC/hCnc remains open. |
| D1_d_even | **O** for unrestricted positive chain; finite repository part certified | `cov_D1_d_even_repository_part`, `cov_D1_d_repository_classification`, `cov_D1_d_large_repository_failure` | Writer's coherent lower-level sphere data are not converted to an arbitrary-n induction; no all-n proof | Published `CliffordChain` is a different predicate. Its n≥6 failure does not refute writer's theorem. Detailed certificate below. |
| D1_d_odd | **O** for unrestricted positive chain; partial | `cov_D1_d_odd_three_part`, `cov_D1_d_odd_repository_part`, classification/failure theorems | Exact writer n=3 proved; repository n=5 theorem recorded, but no full writer all-n proof | n=3 follows from noncollinearity of three points. |
| D2 | **N** | `cov_D2_part` | Injective V, T, Q; all V/T, V/Q, T/Q cross-family inequalities | Full incidence/circle and coordinate transports proved. Some added distinctness follows from line general position, but the redundant premises were not eliminated; Q collisions beyond local Q i ≠ V i are not treated. |
| D2_obligation | **N / open obligation** | No coverage theorem | Existence of V,T and outer-triangle noncollinearity | Main partial theorem takes the writer's supplied V,T,ω data; this obligation is not assumed as an axiom. |
| D3 | **N / open bridge** | `cov_D3_part` | Transformed F₁,F₂ must satisfy `Lester.IsFermatOuter/Inner` | All simplex, metric, circumcentre, and nine-point-circle transport proved. Identifying existential equilateral apices by their side conditions with the explicit complex apices remains open. No demonstrated mathematical mismatch. |
| D3_obligation | **N / open obligation** | No coverage theorem | Existence of both Fermat points | Supplied F₁,F₂ remain explicit input data. |
| D4 | **E** | `cov_D4` | Nothing relative to writer | New side-assignment argument handles either ordering of ω₁,ω₂. Uses `sawayama_thebault`. |
| D4_obligation | **N / open obligation** | No coverage theorem | Existence of the two tangent circles with all required side conditions | Main theorem proves the conditional collinearity; no existence axiom is used. |
| D5 | **E**, using a new extension from repository certificates | `cov_D5`, `cov_Kosnita_zero_locus`, `cov_D5_nonparallel_part` | Nothing relative to writer | Published top-level `kosnita` excludes S=5R², but its polynomial `cert_den` proves parallelism on that locus. Auxiliary noncollinearity discharged. |
| D5_obligation | **E** | `cov_D5_obligation` | Nothing | Mathlib circumcentre of the noncollinear triple OBC. |
| D6_lower | **E** | `cov_D6_lower` | Nothing | Direct specialization of `Blundon.blundon`. |
| D6_upper | **E** | `cov_D6_upper` | Nothing | Direct specialization of `Blundon.blundon`. |
| D6_obligation | **E** | `cov_D6_obligation`, `cov_radicand_core`, `cov_triangle_radicand` | Nothing | Euler/radicand argument extracted from repository certificate and triangle bridges. |
| D7 | **E** | `cov_D7` | Nothing | Direct specialization of `SteinerLehmus.steiner_lehmus`. |
| D7_obligation | **E** | `cov_D7_obligation` | Nothing | New intermediate-value construction of an angle-bisector foot. |

## D1(d): the essential general-position distinction

### What the repository actually defines

`Clifford.GenPosN c` controls **initial pairs and triples only**:
- every pair is transversal (`conj cᵢ * cⱼ ≠ cᵢ * conj cⱼ`);
- every increasing triple satisfies `GenTriple`: two nonzero centre/conjugate determinants, ensuring the relevant initial configuration is nondegenerate.

`Clifford.Chain n c X` recursively quantifies over subfamily objects. Odd levels are **generalized circles**: an actual metric sphere OR an affine line. Even levels are finite points represented by singleton sets. It does not include a point at infinity. It does not impose writer-style uniqueness of every lower even-level common point or noncollinearity of every lower odd-level point set. Recursive existence choices are made within this predicate, rather than being one globally supplied subset-indexed coherent family.

The published classification is exactly:
`Clifford.CliffordChain n ↔ n ≤ 5`.
The scratch records n=4 and n=5 positive results, n≥6 failure, and the concrete six-centre failure. These are results about this precise predicate, not about every textbook meaning of “Clifford chain.”

### What the writer instead assumes

`PaperDClassical.CliffordChain n c M pt circ` supplies objects indexed by subsets of `Fin n`:
- initial spheres are positive-radius, distinct, through M;
- level-two points are non-M second intersections;
- **every lower odd level ≥3** has an actual `Sphere Pt`, containing all predecessor points, with those points **not collinear** (`odd_mem`, `odd_gp`);
- **every lower even level ≥4** supplies a common point and asserts its **uniqueness** (`even_mem`, `even_gp`);
- the odd top-step theorem additionally assumes noncollinearity of all top-level points.

These conditions are substantially stronger than initial-pair/triple general position. Some configurations for which the repository's generalized-circle chain fails do not even satisfy the writer's premises.

### Concrete obstruction certified in Lean

The repository counterexample has common point 0 and six circle centres

```
(3,-6), (6,-3), (1,2), (-2,-1), (0,-4), (4,0).
```

`cov_D1_d_repository_counterexample` proves both `GenPosN` and absence of a level-six repository object.

**New proof:** `cov_D1_d_no_spherical_level_five` shows that ANY repository level-five object for the subfamily omitting the last centre is **not cospherical**. Repository uniqueness lemmas force it to contain

```
(2/3,-4), (-8/3,-4), (-6,-4).
```

These are distinct and collinear. If they belonged to a sphere, Mathlib's `Cospherical.affineIndependent_of_mem_of_ne` would make them affinely independent, a contradiction. This is a kernel-checked obstruction, not a diagram or numerical guess.

`cov_D1_d_counterexample_not_writer_data` transports this obstruction to the writer's Euclidean plane: a set whose complex image is that repository level-five object cannot be contained in ANY writer sphere. The theorem explicitly states the object-identification premise; a full recursive translation between the two chain structures is not claimed.

Thus the published six-centre witness cannot directly instantiate the writer's lower level-five sphere data. For n=6 it is excluded already by lower-level sphere existence, not merely by top-step noncollinearity. The repository's broader generalized-circle setup can produce lines whose common intersection would need an infinity point, which its even-level predicate does not represent.

**Verdict:** do not label writer D1(d) false from `not_cliffordChain_of_six_le`. Conversely, this comparison does not prove the writer's all-n theorem. That theorem remains outside the positive published coverage checked here. The writer report's assertion that it holds for every n was not used as evidence.

## New proofs and reusable bridges

1. **Complex/Euclidean transport**: `complexIso := Complex.orthonormalBasisOneI.repr.symm`; `cov_cospherical_transport`, `cov_collinear_transport`. For arbitrary M, `normalizeAt` composes translation by −M with that isometry; `cov_cospherical_affine`, `cov_collinear_affine` cover affine transport.
2. **Second-intersection identification**: `cov_second_unique` derives the nonzero second intersection formula from the two distance equations and distinct centres. `cov_gp_normalize` transports writer general position and supplied P into repository coordinates. No “coordinate identification” axiom.
3. **Clifford n=4/n=5**: finite ordered-triple bookkeeping, circle membership-to-cosphericity, and writer uniqueness all formally discharged.
4. **Chain separation**: explicit noncospherical level-five obstruction above; this is stronger than merely observing differing definitions.
5. **Pentagram bridge**: derives repository collinear four-point line incidences from writer affine lines, derives five-point cyclicity from supplied spheres, and transports the result back. Extra distinctness is visible in the theorem signature.
6. **Lester transport**: constructs the mapped Mathlib triangle; maps circumcentre and nine-point-circle centre; identifies `Lester.ninePointCenter` with Mathlib's centre. The only main geometry bridge still hypothesized is the explicit Fermat-apex characterization.
7. **Thébault side assignment**: new signed-cross-product lemmas prove strict same-side from positive cross-product product and opposite-side negativity. Since B,C lie on opposite sides of AD, the two centres have one of the two assignments needed by the published theorem. Both branches prove the exact writer conclusion.
8. **Kosnita completion**: from the repository's `cert_den`, S=5R² forces zero cross product of two cevian directions. A new lemma converts this to `AffineSubspace.Parallel`; cyclic repetition yields both required parallelisms. On S≠5R², use `kosnita`. Equidistant OBC/OCA/OAB triples are automatically noncollinear because their three points are distinct and cospherical.
9. **Blundon radicand**: extracts the proof that the polynomial certificate forces R−2r≥0, and reuses/copies the published triangle-to-algebra derivation in scratch. This is proof reuse, not an independent proof of Blundon.
10. **Steiner–Lehmus construction**: the continuous function `t ↦ angle a b (lineMap a c t) − angle (lineMap a c t) b c` changes sign on [0,1]. Noncollinearity keeps the moving point away from b. The intermediate-value theorem supplies the foot with exactly the writer's Wbtw/angle property.

## Construction obligations and hypothesis accounting

**Proved:** D5_obligation, D6_obligation, D7_obligation.

**Not proved:** D2_obligation, D3_obligation, D4_obligation. They are not imported or invoked as axioms. Main results take the original explicitly supplied construction data. Consequently the report certifies conditional conclusions, not unproved global construction existence.

**Additional comparison premises still present:**
- D1(c): six canonical three-point noncollinearities and six circle-identification equalities. These are listed explicitly as `hcanonical_nc0`…`5` and `hcanonical_circle0`…`5`.
- D2: six global distinctness/injectivity families, as in the table.
- D3: two repository Fermat-incidence predicates after coordinate transport. These are not mere construction-existence obligations; they are the unclosed definition bridge and are not counted as E.

No final proof assumes its own conclusion. No existence obligation is hidden behind an unproved theorem.

## Build and integrity receipts

Before starting a repo's scratch compilation, its build log was checked for `Build completed successfully` and running lake process cwd was checked. Initial builds were allowed to finish serially. Final serial audit repeated the check for all eight. Compiles use:

```
cd ~/l15D_<repo>
PATH=$HOME/.elan/bin:$PATH lake env lean scratch/L15_compare.lean
```

All final compile rc files contain `0`. Logs have only axiom-print messages and occasional unused/unreachable-tactic linter warnings. Earlier failed drafts are not proof evidence; some expensive Clifford bookkeeping drafts were terminated by their own recorded PIDs and replaced with finite-index proofs. No unrelated process was killed. The failed probe is renamed `.failed.txt`, not a finished Lean scratch file.

Forbidden-token audit of each final file:

```
grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide|axiom)([^[:alnum:]_]|$)' scratch/L15_compare.lean
```

Every invocation returned **1 (no matches)**. This intentionally permits the plural command `#print axioms`, while forbidding an `axiom` declaration. Every `cov_` theorem has a matching print command; the names were cross-checked programmatically.

Library hash command, exactly as requested:

```
find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs sha256sum | sha256sum
```

| Repo | Commit | Compile rc | Forbidden matches | Library hash before = after |
|---|---|---:|---:|---|
| clifford | `209abaa5e638f37aee8ec374e29b74341297cc46` | 0 | 0 | `bb53ed5aa005078a6d9c3f24379c427f850b96e39f05e5268e7911601f29472a` |
| cliffordchain | `ba083b2158e1b96e2360b6e7d8fe04bd278ff5e2` | 0 | 0 | `d7464f13579e39d7a2696e19e2dbe409fd1e75703ddfd69a82e1f64c7964015e` |
| fivecircles | `f1fd9b7b2bd9f6b1e881425019f86fc49adba927` | 0 | 0 | `1cddd210ca590ece1325206106d79b455e05b61de8fa10e8d6f71da22a474cbf` |
| lester | `9f94754987cbb9ddb8bf14bef295f2bfedb077df` | 0 | 0 | `6e768745d69ddd3276f02f51e6d62e6bd4d1075c7907b64f8ecb6c47063f36c0` |
| thebault | `c37f92e53c9ed790a2c90afdef95a7a35e6a7842` | 0 | 0 | `06432c5a80ad20e9bf1289902c9aae64c3e9310d300600be83da0e0672b897c7` |
| kosnita | `702f0263a70136830aee7a9fd38ec7f4fc7d304d` | 0 | 0 | `e98f36b540e0288412b4d5e2ebbf80a7671d1256f95e52bcf4ab71eeb3a606c6` |
| blundon | `118b4c9f3afd6d4120ea2c2d2e60c1e70d7dc8b8` | 0 | 0 | `89ec32d88994fac7ac8afb5802ca2d200c7bcf8d77f8f7e3008fda9bfe5e0729` |
| steinerlehmus | `a3a3d26bee6c68eae6d564228355524c46fe546d` | 0 | 0 | `feaf54dcf171b4eb7086aa4800c0f8e24b3ad4402acfa91a0664f0dfbf358813` |

## Scratch and evidence paths

**On jack:** for every repo in the table:
- `~/l15D_<repo>/scratch/L15_compare.lean`
- `~/l15D_<repo>/scratch/L15_compile.log`
- `~/l15D_<repo>/scratch/L15_compile.rc`
- `~/l15D_<repo>/scratch/L15_forbidden.log` (empty)

**Local copies:** `<ws>/AFM/PaperD/layer15/comparer/l15D_<repo>/scratch/`.

Combined audit: `<ws>/AFM/PaperD/layer15/comparer/final_audit.txt`.

Report: `jack:~/reformal/PAPERD_L15_COMPARE.md` and
`<ws>/AFM/PaperD/layer15/PAPERD_L15_COMPARE.md`.

## Complete final #print axioms output

All outputs below come from the final successful compilation, not failed drafts.

```text
REPO=clifford
'PaperDClassical.cov_cospherical_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_collinear_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_cospherical_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_second_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_gp_normalize' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_collinear_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_gam_cospherical' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_gamma_of_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_mem_normalizeSphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_c_part' depends on axioms: [propext, Classical.choice, Quot.sound]
REPO=cliffordchain
'PaperDClassical.cov_cospherical_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_collinear_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_d_repository_classification' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_d_repository_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_d_no_spherical_level_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_d_counterexample_not_writer_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_d_odd_three_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_d_even_repository_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_d_odd_repository_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D1_d_large_repository_failure' depends on axioms: [propext, Classical.choice, Quot.sound]
REPO=fivecircles
'PaperDClassical.cov_cospherical_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_collinear_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D2_part' depends on axioms: [propext, Classical.choice, Quot.sound]
REPO=lester
'PaperDClassical.cov_cospherical_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_collinear_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D3_part' depends on axioms: [propext, Classical.choice, Quot.sound]
REPO=thebault
'PaperDClassical.cov_D4_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D4_swapped_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_cross_zero_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_sameSide_of_cross_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_opp_cross_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D4' depends on axioms: [propext, Classical.choice, Quot.sound]
REPO=kosnita
'PaperDClassical.cov_D5_obligation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D5_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_auxiliary_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D5_nonparallel_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_parallel_of_cross_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_Kosnita_zero_locus' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D5' depends on axioms: [propext, Classical.choice, Quot.sound]
REPO=blundon
'PaperDClassical.cov_D6_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D6_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_radicand_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_triangle_radicand' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D6_obligation' depends on axioms: [propext, Classical.choice, Quot.sound]
REPO=steinerlehmus
'PaperDClassical.cov_D7' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperDClassical.cov_D7_obligation' depends on axioms: [propext, Classical.choice, Quot.sound]
```
