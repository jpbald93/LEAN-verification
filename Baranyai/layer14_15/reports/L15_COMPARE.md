# L15 classical comparison — Paper Baranyai

**Repository:** https://github.com/jpbald93/baranyai at the paper's pinned commit `051ae8c4063be0bb70f1726e9f60d0319dd37d91`. Fresh clone at `jack:~/l15Baranyai_baranyai`. Mathlib is at `0df444a3…`, so `.lake/packages` is symlinked to `~/barbier/.lake/packages`.

**Gate:** `bash gate.sh`, run under `flock ~/l15jack.lock`, printed `PASS (32 declarations, standard axioms only)`. rc 0, 18 s. Log: `jack:~/l15Baranyai_gate.log`.

**Writer's file:** `/tmp/blindBaranyai/Classical.lean`, sha256 `c4f5f448…`, as stated in the writer's report. It has 8 `classical_*` statements.

## Table

| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| classical_Baranyai1_a | **E** | `cov_Baranyai1_a`, `classical_Baranyai1_a` | — | Uses `Baranyai.baranyai_of_card`, `block_disjoint` and `class_card` through the bridge `classesOf_spec`. The writer's `0 < n` is not needed. |
| classical_Baranyai1_b | **E** | `cov_Baranyai1_b` | — | `Baranyai.choose_mul` with `mul_comm`. |
| classical_Baranyai2_a | **E** | `cov_Baranyai2_a` | — | Covers `n = 0` too, which resolves the writer's AMBIGUOUS mark: both readings are covered. Each perfect matching is turned into a `Finpartition univ` by `toFinpartition`, using `supIndep_iff_pairwiseDisjoint` and `k > 0` for `⊥ ∉ parts`. |
| classical_Baranyai2_b | **E** | `cov_Baranyai2_b` | — | Same as 2_a. |
| classical_Baranyai3_main | **O** | `cov_Baranyai3_main_part` (the instance `k∣n`, `t = C(n-1,k-1)`, `a_i = n/k`) | Arbitrary `t` and `a_i`, and the case `k ∤ n` | The paper says this is not formalised: §Future work, "almost-regular colourings when k∤n … None is formalised" (baranyai.tex l.645). The statement as written is true (van Lint–Wilson Thm 38.1) and is not mis-stated. It is not cheap: it needs a generalised invariant/flow argument, which the paper itself says would be required. Not proved. |
| classical_Baranyai3_a | **E** | `cov_Baranyai3_a` | — | Almost-regularity holds because every degree is 1 = ⌊k·(n/k)/n⌋ (`pointDegree_eq_one`, `ratio_eq_one`). |
| classical_Baranyai3_a_implication | **O** (NEW PROOF) | `cov_Baranyai3_a_implication` | — | The repository has no such statement. It is elementary: degree ∈ {⌊1⌋, ⌈1⌉} = {1}, which gives disjointness and covering. Proved here. |
| classical_Baranyai3_b | **E** | `cov_Baranyai3_b` | — | Uses `complete_graph_one_factorisation`, transported by `factorisation_congr` along `Fintype.equivFinOfCardEq`. Each colour class becomes a spanning `(⊤ : SimpleGraph V).Subgraph` (NEW bridge proof to Mathlib's `IsPerfectMatching` and edge partition). Covers `n = 0`, so both of the writer's readings are covered. |

**Summary:** 6 E, 2 O (one of them proved in full as a NEW PROOF), 0 N, 0 D.

- No writer statement is false.
- No classical statement disagrees with the repository.
- The repository's statements are slightly stronger than the classical text in these places:
  - no `0 < n` is needed for 1_a;
  - `n = 0` is covered for 2_a, 2_b and 3_b;
  - `baranyai'` gives the `C(n,k)·k/n` count;
  - `dvd_card_of_factorisation` gives a converse that the classical text does not state.

## NEW PROOFS (scratch only, not in the library)

- Bridges from the repository's colouring form (`c : {S // S.card = k} → Fin M`) to the writer's forms: `classesOf`, `mem_classesOf`, `classesOf_spec`, `classes_exist`.
- The Finpartition bridge `toFinpartition`.
- The SimpleGraph perfect-matching bridge inside `cov_Baranyai3_b`.
- `pointDegree_eq_one` and `ratio_eq_one`.
- `cov_Baranyai3_a_implication`, which is out of scope for the paper and proved in full.

## Obligations

- The writer reported none.
- There are no construction obligations: every comparison is proved outright, with no hypotheses beyond the writer's own.
- Nothing is carried as an explicit extra hypothesis.
- `classical_Baranyai3_main` (general form) is left unproved. It is not used anywhere and is not assumed.

## Verbatim check

The scratch file copies the writer's four definitions verbatim. It also re-extracts the text of the 7 proved `classical_*` theorems mechanically from `Classical.lean` (Python regex) and replaces only `:= by sorry` with `apply cov_X <;> assumption`. All 7 check, so the `cov_` statements are exactly the writer's.

## Compile

```
flock ~/l15jack.lock lake env lean scratch/L15_compare.lean   → rc=0, 0 errors
```

The only warnings are two unused-section-variable linter warnings. Output is in `jack:~/l15Baranyai_compare.out`.

## Forbidden grep

`grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b" scratch/L15_compare.lean` → no matches (rc 1).

## #print axioms

| theorem(s) | axioms |
|---|---|
| cov_Baranyai1_a, cov_Baranyai2_a, cov_Baranyai2_b, cov_Baranyai3_a, cov_Baranyai3_a_implication, cov_Baranyai3_b, cov_Baranyai3_main_part | [propext, Classical.choice, Quot.sound] |
| cov_Baranyai1_b | [propext, Quot.sound] |
| the 7 re-extracted classical_* theorems | same axioms as their cov_ counterparts |

No `sorryAx` and no other axioms appear.

## Hashes

- **Library, before:** `dc355427211e73fda5fa1fcb1a34fcdaa859440021b7454aa16959f9e43c7548`
- **Library, after:** `dc355427211e73fda5fa1fcb1a34fcdaa859440021b7454aa16959f9e43c7548` (unchanged)
- **Git status:** only `?? scratch/L15_compare.lean`
- **Scratch file:** sha256 `c10526c4f9a9cc4cd980a1c7693ce99e34162b19bb891443d2933cf263deb3eb`

## Scratch paths

- `jack:~/l15Baranyai_baranyai/scratch/L15_compare.lean`
- Local copies: `/tmp/l15Bar/L15_compare.lean` and `<ws>/AFM/L14L15/Baranyai/L15_compare.lean`

## Wall time

About 10 min (06:20–06:30 EDT, 2026-10-22).
