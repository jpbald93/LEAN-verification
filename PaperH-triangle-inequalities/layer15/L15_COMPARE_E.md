# Layer 15 — Classical comparer, Paper H, library EulerIneq (assignment E)

Classical file: `PaperHClassical.lean`, sha256 `0ac73f94ec9efdb8e9d6337980d6e2ec8cc2521083c2026968373dd7d85eceb7` (prefix matches `0ac73f94ec9efdb8`; x86-64 machine's copy `~/PaperHClassical.lean` has the same hash).
Machine: x86-64 machine, work copy `~/l14h_euler` (HEAD `545a974df2663e30d735d9de43d62dd3a7c79c6b`, "Layer 14: …").
Scratch: `x86-64 machine:~/l14h_euler/scratch/L15_compare.lean` (sha256 `df31c68071d92491fb02776218aa3e624d3e00fbc04e5006716010bd57f38ef5`), `import EulerIneq`; local copy `<paper-dir>/L15_compare_E.lean`. `scratch/` added to `.git/info/exclude`.

Method: the classical definitions (variable line through `ClassicalInOrderOnCircleOrLine`) were copied verbatim, with namespace `PaperHClassical` renamed to `L15CompareE`. Each assigned statement is restated with its verbatim type as `cov_<name>`. A script compared every `cov_` signature with the matching `classical_` signature after whitespace normalisation: definitions and all 22 signatures match exactly (for P1 the matching theorem is `cov_P1_part`; see below). Proofs use the Layer-14 bridge `EulerIneq/L14.lean` (`l14_*`) only.

## Table

| classical | E/N/D/O | cov_ theorem(s) | what is missing / NEW PROOF | note |
|---|---|---|---|---|
| E1 | E | cov_E1 | — | `l14_euler` + `dist_comm` |
| E2a | E | cov_E2a | — | `l14_euler_inequality` |
| E2b | E | cov_E2b | — | `l14_euler_inequality_eq_iff`; the equilateral conjuncts are permuted (linarith) |
| E3 | E | cov_E3 | — | `l14_euler_excenter` + `dist_comm`, all `i : Fin 3` |
| E4a | E | cov_E4a | — | `l14_dist_circumcenter_centroid_sq` (`ClassicalCentroid` = `Simplex.centroid` by defeq) |
| E4b | E | cov_E4b | — | `l14_dist_circumcenter_orthocenter_sq` |
| E4c | E | cov_E4c | — | `l14_dist_incenter_centroid_sq` |
| E5 | E | cov_E5 | — | `l14_fundamental_quartic` |
| E6a | E | cov_E6a | — | `(l14_gerretsen t).1` |
| E6b | E | cov_E6b | — | `(l14_gerretsen t).2` |
| E7 | E | cov_E7 | — | `l14_kooi`, no extra hypothesis |
| E8a | E | cov_E8a | — | `l14_weitzenboeck` (same area definition ½·AB·AC·sin A) |
| E8b | E | cov_E8b | — | `l14_weitzenboeck_eq_iff` + symmetry / conjunct permutation |
| E9a | E | cov_E9a | — | `l14_hadwiger_finsler`; the order of the squared-difference terms matches up to defeq |
| E9b | E | cov_E9b | — | `l14_hadwiger_finsler_eq_iff` + permutation |
| E10a | E | cov_E10a | — | `l14_isoperimetric` |
| E10b | E | cov_E10b | — | `l14_isoperimetric_eq_iff` + `eq_comm` |
| E11a | E | cov_E11a | — | `l14_leibniz_relation` |
| E11b | E | cov_E11b | — | `l14_leibniz_min`, `l14_leibniz_min_eq_iff`, plus value at G = Σ/3 (from E11a) |
| E12a | E | cov_E12a | — | `l14_pedoe`, two triangles in possibly different spaces P, P′, as in the classical file |
| E12b | E | cov_E12b | — | `l14_pedoe_eq_iff` (same similarity condition ∃k>0) |
| P1 | D (Euclidean part covered) | cov_P1_part, cov_P1_counterexample, cov_P1_false | The verbatim `classical_P1 (A B C D : P)` does not mention `V`, so Lean auto-binding drops `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddTorsor V P]`. Its elaborated type is `∀ {P} [MetricSpace P] (A B C D : P), …`, i.e. Ptolemy in an **arbitrary metric space**, and that is false. NEW PROOF of the counterexample: in `Fin 2 → ℝ` (sup metric), A=(1,0), B=(0,1), C=(−1,0), D=(0,−1) give AC·BD = 4 > 2 ≥ AB·CD + BC·AD (`cov_P1_counterexample`, `cov_P1_false`) | The intended Euclidean statement is exactly what the repository proves: `cov_P1_part` has the same text with `include V in` (`l14_ptolemy_inequality`). So this is a formalisation slip in the classical file, not a mismatch with the paper. Verified: compiling the classical declaration alone and running `#check` shows `@classical_P1 : ∀ {P : Type u_3} [inst : MetricSpace P] …` |

Summary: 21 × E, 1 × D (P1: the verbatim Lean statement is false; its intended Euclidean meaning is covered exactly).

## Compile

`cd ~/l14h_euler && flock ~/ph.lock lake env lean scratch/L15_compare.lean` → **EXIT=0**. No errors and no warnings; the only output is the axiom lines below.

## Forbidden grep

`grep -nE "sorry|admit|native_decide|^axiom|[^_]axiom " scratch/L15_compare.lean | grep -v "#print axioms"` → no matches (grep exit 1).

## #print axioms (all 24)

```
'L15CompareE.cov_E1' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E2a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E2b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E3' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E4a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E4b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E4c' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E5' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E6a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E6b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E7' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E8a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E8b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E9a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E9b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E10a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E10b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E11a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E11b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E12a' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_E12b' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_P1_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_P1_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'L15CompareE.cov_P1_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Every theorem depends only on `propext, Classical.choice, Quot.sound`.

## Library hashes

Combined sha256 of `find EulerIneq EulerIneq.lean lakefile.toml lean-toolchain lake-manifest.json -type f | sort | xargs sha256sum | sha256sum`:
- before: `c445b2d2fd3e8f0e3d603d0036c4d410e1e39c83c68f14834ff34de919041b67`
- after:  `c445b2d2fd3e8f0e3d603d0036c4d410e1e39c83c68f14834ff34de919041b67` (unchanged)

`git status --short` was clean after the work (scratch is excluded). I did not edit any library file and did not run `lake update`, `cache get` or `lake build`. Every lean invocation ran under `flock ~/ph.lock`. No background processes were started.

## Scratch paths

- x86-64 machine: `~/l14h_euler/scratch/L15_compare.lean`
- local: `<paper-dir>/L15_compare_E.lean`, compile log `<work-dir>`

DONE
