# Paper CB (Cayley–Bacharach) — Layer 15: classical comparison

Wall time: 2026-10-22 05:22 → 07:06 EDT (about 1 h 45 min). All work was inline, with no sub-agents.

## Setup
- Repo `jpbald93/cayley-bacharach` @ `9a4f11e82c291bc9428ad9b66bfaba388acf63de` (the paper's `\commit`). Fresh clone at `john:~/lean/l15CB_cayley-bacharach`, HEAD verified.
- Toolchain v4.33.1, Mathlib `0df444a3…`. `.lake/packages` is symlinked to `~/lean/clifford/.lake/packages`. No update or cache fetch was run.
- `jl build`: rc=0 (8734 jobs).
- Gate:
  - `jl -g gate` (GNU): **PASS (100 declarations, standard axioms only)**, both before and after the scratch work.
  - `jl gate` (BSD tools): `FAIL: axiom report`. This is the known BSD `mktemp --suffix` portability problem in `gate.sh` (L14 finding 2). It is not a proof issue.
- Writer inputs: `/tmp/blindCB/Classical.lean` and `CLASSICAL_REPORT.md`. The writer's definitions are copied **verbatim**. Each `theorem classical_X … := by sorry` became `def classical_X : Prop := ∀ <same binders>, <same conclusion>` (a mechanical Python rewrite; no binder or type was changed).
- The Mathlib↔library bridges (`toP`, `cv`, `l14b_*`, `l14_*` restatements) are copied **into the scratch file** from the L14 file. They are not imported from the l14 clone, whose library is not used.

## Table

| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| `classical_CB1_a` | **E** | `cov_CB1_a` | — | Every field. Proved from `cayley_bacharach_of_no_common_factor_any`. `IsRelPrime` gives the repo's "no common line / conic factor" and linear independence, since non-constant homogeneous forms are non-units. Of the writer's AMBIGUOUS readings, the weaker one (nine distinct common points, no exactness) is the one proved. |
| `classical_CB1_a_linear` | **E** | `cov_CB1_a_linear` | — | Every field. Uses `general_position_of_no_common_factor` and `mem_span_of_eight`. For \|K\|≤2 the statement is vacuous (`card_le_seven_of_not_atLeastThree`). |
| `classical_CB1_b` (multiplicities, `IsAlgClosed`, simple points) | **N** (paper: O) | `cov_CB1_b_part`, plus the bridge `l15_intMult_ne_zero_iff` | the case where P₁…P₉ are **not distinct**, i.e. real intersection multiplicities | `cov_CB1_b_part` assumes `Function.Injective P` but drops `IsAlgClosed` and `hsimple`. In that case it proves `Q = P 8` from the writer's own `intMult` cycle hypotheses. NEW PROOF of the bridge `intMult F G P ≠ 0 ↔ F(P)=0 ∧ G(P)=0` for homogeneous F, G. The general case needs Bézout and local intersection theory. The paper says outright that this is not formalised ("Limitations: Multiplicities"). |
| `classical_CB1_b_irreducible` | **N** (paper: O) | `cov_CB1_b_irreducible_part` | same as above | Same partial result; `Irreducible F₁` is not used. |
| `classical_CB2_a` | **E** | `cov_CB2_a` | — | Every field. Uses `finrank_ker_evalMap_eq_two_iff` through the L14 bridge `l14_finrank_eq_two_iff`. The writer's "no 4 on a line" is stronger than the repo's "≤4 of 8 on a line", and "no 7 on a conic" is stronger than "not all 8 on a conic". |
| `classical_CB2_b` (`IsAlgClosed`, base cycle via `intMult`) | **O** | — | the whole statement (Bézout, intersection cycles, multiplicity 2 when P₉ = Pᵢ) | The paper does not claim it. I did not search for a counterexample, and I did not check the writer's claim that `intMult` equals Fulton's multiplicity. Only the support lemma `l15_intMult_ne_zero_iff` is proved. |
| `classical_CB2_b_distinct` | **N** | `cov_CB2_b_distinct_part` | the **uniqueness** half of `∃!` | Existence holds over every field: P₉ := Q, via `l15_cb` applied to `Fin.snoc P Q`. Uniqueness says two coprime cubics have at most 9 common rational points (Bézout over k). That bound is not in the repo, and I did not close it. |
| `classical_CB3_a` (Pascal) | **E** (NEW PROOF) | `cov_CB3_a`; also `cov_CB3_a_part` | — | **Every field.** The repo's `pascal_clean` needs `CardGT K 10`; `cov_CB3_a_part` is the version via the repo plus the L14 bridge, with `hK : ∃ s, 10 < s.card`. The new proof avoids that hypothesis. The explicit Braikenridge–Maclaurin conic `Q(p) = [X, BC∩Ep, CD∩pA]` passes through A…E (proved by `ring`) and is nonzero (`Q(A+B)` factors as a product of four 3×3 brackets). The repo's `conics_le_one` says the conics through 5 points in general position form a space of dimension ≤ 1, so `Q ∝ q` and Q(F) = 0, which is exactly collinearity of X, Y, Z. The paper's "Further work" item notes that Pascal over small fields is open in the repo. |
| `classical_CB3_a_obligation` | **E** | `cov_CB3_a_obligation` | — | Opposite sides meet uniquely. Uses `noncollinear_of_irreducible` and a new `l15_meet`. |
| `classical_CB3_b` (Braikenridge–Maclaurin) | **O** (NEW PROOF) | `cov_CB3_b` | — | The paper does not claim it. Proved over **every field** with the same explicit conic Q: X, Y, Z collinear ⇔ Q(F)=0. The F₄ check below shows it is vacuous there. |
| `classical_CB3_b_obligation` | **O**, proved | `cov_CB3_b_obligation` | — | |
| `classical_CB4_a` (Pappus) | **E** (NEW PROOF) | `cov_CB4_a`; also `cov_CB4_a_part` | — | **Every field.** The repo's `pappus_clean` needs `CardGT K 10` (`cov_CB4_a_part` is that route). New proof: write C = sA+tB and C' = s'A'+t'B'. Then `l15_papid` is a polynomial identity, proved by `ring` in about 26 s, saying the three Pappus points are collinear. The meeting points are tied to the cross products by `l14b_on_two`. |
| `classical_CB4_a_obligation` | **E** | `cov_CB4_a_obligation` | — | |
| `classical_CB4_b` (hexagon form) | **E** (NEW PROOF) | `cov_CB4_b`; also `cov_CB4_b_part` | — | Every field, by relabelling into `l15_pappus_core`. The writer's EXTRA HYPOTHESES (distinct lines, distinct vertices, no vertex at L∩M) are exactly the non-degeneracy the repo needs. `hlm` is not used. |
| `classical_CB4_b_obligation` | **E** | `cov_CB4_b_obligation` | — | |

**No classical statement was found false. No D classifications.**

## NEW PROOFS (all in the scratch file, standard axioms)
1. `cov_CB3_a`: Pascal over every field (the repo needs |K|>10).
2. `cov_CB3_b`: Braikenridge–Maclaurin over every field. The repo has no converse.
3. `cov_CB4_a`, `cov_CB4_b`: Pappus over every field (the repo needs |K|>10). The key lemma `l15_papid` is a single `ring` identity.
4. `l15_intMult_ne_zero_iff`: the writer's `intMult` (a length over the localisation at the homogeneous point ideal) is nonzero iff both forms vanish. Supporting lemmas: `l15_aeval_hom` and `l15_mem_pointIdeal` (for homogeneous F, F ∈ pointIdeal v ⇔ F(v)=0).
5. `cov_CB1_b_part`, `cov_CB2_b_distinct_part`: the distinct-points case of the multiplicity version, and the existence half of the distinct form of CB2(b).

Side check (Python, not Lean; `work/f4.py`): over 𝔽₄ there are 168 six-point sets with no three collinear. These are hyperovals, and none lies on a conic. For every one of them, in all 720 orderings, X, Y, Z are never collinear. So CB3(b) holds vacuously there, consistent with `cov_CB3_b`.

## Obligations
- The writer's four well-formedness obligations (`classical_CB3_a/CB3_b/CB4_a/CB4_b_obligation`) are all **proved**, with no extra hypotheses.
- Hypotheses carried explicitly: only `hK : ∃ s : Finset k, 10 < s.card`, in `cov_CB3_a_part`, `cov_CB4_a_part` and `cov_CB4_b_part` (the repo routes). The NEW PROOF versions supersede these.
- `cov_CB1_b_part` and `cov_CB1_b_irreducible_part` add `Function.Injective P`. That is the missing part; no `IsAlgClosed` or `hsimple` is used.
- Open: CB2(b) (alg. closed form), the general multiplicity case of CB1(b), and uniqueness in CB2(b)-distinct. No sorry or axiom stands in for them; they are simply not proved.

## Compile, grep and axioms
- `~/lean/jl lake env lean scratch/L15_compare.lean`: **rc=0, 0 errors**, 0 "declaration uses sorry". The 233 warnings are all linter warnings (unused simp args or variables). About 41 s wall.
- Forbidden grep `\bsorry\b|\badmit\b|native_decide|\baxiom\b|set_option|#eval|run_cmd|macro|elab|notation` on the scratch file: **no matches** (grep rc=1).
- `#print axioms`: every theorem below prints `[propext, Classical.choice, Quot.sound]`:
  - `cov_CB1_a`, `cov_CB1_a_linear`, `cov_CB1_b_part`, `cov_CB1_b_irreducible_part`
  - `cov_CB2_a`, `cov_CB2_b_distinct_part`
  - `cov_CB3_a`, `cov_CB3_a_part`, `cov_CB3_a_obligation`, `cov_CB3_b`, `cov_CB3_b_obligation`
  - `cov_CB4_a`, `cov_CB4_a_part`, `cov_CB4_a_obligation`, `cov_CB4_b`, `cov_CB4_b_part`, `cov_CB4_b_obligation`
  - `l15_intMult_ne_zero_iff`

## Hashes
- Library hash (`find … -not -path ./.lake/* -not -path ./scratch/* | sort | xargs shasum -a 256 | shasum -a 256`):
  - before: `75d7f04d8a50f2fa3c101906f716b37bc5cbe8da4dc3b09f19aa6e3ed1edd96b`
  - after: `75d7f04d8a50f2fa3c101906f716b37bc5cbe8da4dc3b09f19aa6e3ed1edd96b` (**unchanged**)
- `git status`: only `?? scratch/L15_compare.lean`. `scratch/PaperAxioms.lean` and `scratch/paper_axioms.out` are tracked files from the published repo; I did not touch them.
- `L15_compare.lean` sha256: `1162670f3b0d2e22487be9be3bc71a75405b13de1a0bb85364dde64c48ae7550` (1652 lines).

## Scratch paths
- `john:~/lean/l15CB_cayley-bacharach/scratch/L15_compare.lean` (compiled copy). Logs: `john:~/lean/l15CB_build.log`, `l15CB_gate.log`, `l15CB_cmp.log`, `l15CB_hash_before.txt`.
- Local copy: `<ws>/AFM/L14L15/CB/L15_compare.lean`.
- Work dir: `<oc>/tmp/overnight1022/l15c/CB/work/` (`conv.py` def-rewriter, `head.lean`/`tail.lean`, `f4.py`, `pas*.py`, `bm.py` sympy checks).
- File layout:
  - Section 1: L14 bridge copy (namespace `L15B`).
  - Section 2: writer's definitions and statements, verbatim, as `Prop` defs.
  - Section 3: `l15_*` bridges and `cov_*` theorems.
