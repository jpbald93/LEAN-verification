# L15 — Classical comparer, Paper G, Group N (NagelLine)

- Classical file: `the arm64 machine:~/lean/reformalG/PaperGClassical.lean`, sha256 `2bb545d76d505fe0db1a848362e9414fdd285239321dea37980b365755ae1b74` (prefix matches `2bb545d76d505fe0`).
- Repository copy: `the arm64 machine:~/lean/l15_nagel` (copied from `~/lean/paperg_nagel`, `.lake/packages` symlinked, `~/lean/jl build` finished with "Build completed successfully (8711 jobs)").
- Scratch file: `the arm64 machine:~/lean/l15_nagel/scratch/L15_compare.lean` (sha256 `21d65f9724b9d53b9a638bafd54cbc169134e01b69fcce05c4ae159036dc6d10`), `import NagelLine`, namespace `PaperGClassicalL15`. Compile log: `scratch/compare.log`.
- All work was done inline. No sub-agent were used.

## Summary table

All 10 assigned statements are **E (covered)**. Each `cov_<name>` has the classical statement as its type, proved from repository theorems plus bridge lemmas in the scratch file.

| classical | verdict | Lean theorem(s) | what is missing from the repository | note |
|---|---|---|---|---|
| N1 (Gergonne concurrency) | **E** | `cov_N1` | nothing | `ClassicalInContactX` = Mathlib `touchpoint ∅ i` (bridges `inA_eq`/`inB_eq`/`inC_eq`: same projection, the lines are equal via `range_face0/1/2`). Then `l14_gergonne`. |
| N2a (Nagel concurrency) | **E** | `cov_N2a` | nothing | Classical excentre `-a:b:c` = Mathlib `excenter {i}` (`exA0/1/2`, from the repository's `excenter_singleton_eq_affineCombination`). Classical ex-contact = `touchpoint {i} i` (`exC0/1/2`). Then `l14_nagel`. |
| N2b (BD = s−c, CD = s−b) | **E** | `cov_N2b` | No distance statement as such. The repository proves `touchpoint {0} 0 = lineMap B C ((s−c)/a)` (`touchpoint_singleton_zero`). | Distances derived in the scratch file (`dist_lineMap_left/right`, 0 ≤ (s−c)/a ≤ 1). Small **NEW PROOF**. |
| N3 (I, G, Na collinear; Wbtw I G Na; GNa = 2·IG) | **E** | `cov_N3` | **Uniqueness of the Nagel point.** The classical `Na` is *any* common point of the cevians. The repository only shows that its weight-defined `nagelPoint` lies on them. | **NEW PROOF** `nagel_unique` (two cevians from A and B meet in at most one point, because the A-cevian meets BC strictly inside, by `sbtw_touchpoint_singleton_zero`). So `Na = nagelPoint`. Then `G = lineMap I Na (1/3)` from `nagelPoint_vsub_centroid` gives Wbtw (parameter 1/3 ∈ [0,1]) and the distance identity. Collinearity: `collinear_incenter_centroid_nagelPoint`. |
| N4 (Spieker = midpoint(I, Na); I, G, Na, Sp collinear) | **E** | `cov_N4` | Same uniqueness gap as N3 (closed by `nagel_unique`). The 4-point collinearity is not stated (repository has {Sp, I, N} and {I, G, N} separately). | Classical medial triangle = `t.medial` (`medial_eq`). Midpoint: `medial_incenter_eq_midpoint`. 4-point collinearity: all four points are `lineMap I N r` (r = 0, 1/3, 1, 1/2). |
| N5 (isotomic contacts, side BC) | **E** | `cov_N5`, plus `cov_N5_all` (all 3 sides) | nothing | `midpoint_touchpoint_zero`; all three sides via `l14_isotomic`. |
| N6a (Nagel point of medial triangle = I) | **E** | `cov_N6a` | Uniqueness (the classical X is any common point of the medial Nagel cevians). Non-degeneracy of the medial triangle in the classical `![midpoints]` form. | `nagel_unique` applied to the medial triangle, with **NEW PROOF** `medial_indep` (from `t.medial.independent` + `medial_points_eq`). Then `medial_nagelPoint`. |
| N6b (Na = incentre of anticomplementary triangle) | **E** | `cov_N6b` | Uniqueness (closed by `nagel_unique`). | Classical `ClassicalAnticompl` triangle = `t.anticomplementary` (`anti_eq`, via `anticomplementary_points_zero/one/two`). Then `nagelPoint_eq_anticomplementary_incenter`. |
| N7 (O, G, H, L collinear; L = orthocentre of anticomplementary) | **E** | `cov_N7` | The 4-point collinearity is not stated (repository has {G,O,L} and {L,O,H}). | Combined with no case split: `G = lineMap O H (1/3)` (from `orthocenter_vsub_circumcenter`) and `L = pointReflection O H = lineMap O H (−1)`, so all four lie on `line[O, H]`. In the equilateral case O = H, the line is the point {O} and the set is a singleton, still collinear, so no separate argument is needed. Classical `pointReflection O H` = repository `deLongchampsPoint` (`deLongchamps_eq`). Second conjunct: `anticomplementary_orthocenter`. |
| N8 (Spieker centre has equal power w.r.t. the 3 excircles) | **E** | `cov_N8` | nothing | `ClassicalExradiusA` (distance from excentre to foot) = Mathlib `exradius {i}` by `ExcenterExists.dist_excenter` + bridges. Then `l14_spieker_radical t 0 1`, `… 1 2`. |

## NEW PROOFS (scratch only; library untouched)

- `cevian_unique`: two cevians from vertices A ≠ B, where the A-cevian meets line BC at D ≠ B, meet in at most one point (non-collinear A, B, C).
- `nagel_unique`: any common point of the first two classical Nagel cevians equals the repository's `nagelPoint`. This closes the gap between the classical cevian-based "Nagel point" and the repository's weight definition. Used in N3, N4, N6a, N6b.
- `medial_indep`: the classical extra hypothesis `hM` (medial triangle non-degenerate) follows from `h`.
- `anti_indep`: the classical extra hypothesis `hT` (anticomplementary triangle non-degenerate) follows from `h`.
- Distance form of the ex-contact point (inside `cov_N2b`).
- 4-point collinearities in N4 and N7 (combinations of repository facts via `lineMap`).
- Bridge lemmas: `exA0/1/2` (textbook excentre `−a:b:c` = Mathlib excentre), `exC0/1/2`, `inA/B/C_eq`, `medial_points_eq`/`medial_eq`, `anti_points_eq`/`anti_eq`, `centroid_eq_lineMap`, `O_H_lineMap`, `deLongchamps_eq`.

Remark: `hM` and `hT` are extra hypotheses in the classical statements, and the `cov_` theorems keep them because they are copied verbatim. `medial_indep` and `anti_indep` show these hypotheses are redundant.

## Verbatim check

A script compared the scratch file with the original.
- The definitions block (`Basic definitions`, from `ClassicalTri` to `ClassicalAnticompl`) is byte-identical.
- N1, N2a, N2b, N3, N5 and N6a are byte-identical to the classical statements.
- N4, N6b, N7 and N8 are identical after removing whitespace and `--` comments. Only the classical `-- EXTRA HYPOTHESIS` / `-- AMBIGUOUS` comment lines were dropped; the Lean terms are the same.

## Compile / gates

- `cd ~/lean/l15_nagel && ~/lean/jl lake env lean scratch/L15_compare.lean` → **exit 0**, 0 errors. The only warnings are linter ones ("this tactic is never executed" from the `first | …` combinator in `exA1/exA2`, plus unused simp args).
- Forbidden-token grep (`sorry|admit|native_decide|axiom`) on the scratch file: **no matches** (grep rc 1).
- `#print axioms`: every one of `cov_N1, cov_N2a, cov_N2b, cov_N3, cov_N4, cov_N5, cov_N5_all, cov_N6a, cov_N6b, cov_N7, cov_N8, medial_indep, anti_indep, nagel_unique` → `[propext, Classical.choice, Quot.sound]`.

## Library hash

`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`
- before (paperg_nagel and fresh l15_nagel copy): `3b06625b902845677b99ac2eee1fc88b1f7bfeabb763ce7b026cd26f1c952124`
- after (l15_nagel): `3b06625b902845677b99ac2eee1fc88b1f7bfeabb763ce7b026cd26f1c952124`
- after (paperg_nagel, untouched): `3b06625b902845677b99ac2eee1fc88b1f7bfeabb763ce7b026cd26f1c952124`

## Not reached / caveats

- Everything assigned was reached. Group S was ignored as instructed.
- Interpretation: "E" here means the classical statement follows from the repository's proven content plus short new proofs. For N3, N4, N6a and N6b the new uniqueness lemma is essential. The repository itself does not prove that the Nagel point is the *unique* common point of the cevians.
