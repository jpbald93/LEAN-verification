# Layer 14 — Baranyai (Mathlib-only restatement + witnesses)
Started 2026-10-21 22:42 EDT, finished 22:58 EDT (wall time ≈ 16 min). Status: **DONE**. All work was done inline; no subagents were used.

Paper: AFM/Baranyai/baranyai.tex. Main theorems are `thm:formal` (`baranyai`) and `thm:partition` (`Baranyai.baranyai_partition`), plus the main-theorem rows of Table 1 (`baranyai'`, `complete_graph_one_factorisation`, `baranyai_four_two`) and the transport/converse theorems (`baranyai_of_card`, `baranyai_finset`, `dvd_card_of_factorisation`). The rest of Table 1 (Inv, dem, arithmetic lemmas, step, ...) are proof internals and were not restated.

## Repo: baranyai
- Source: https://github.com/jpbald93/baranyai at 051ae8c4063be0bb70f1726e9f60d0319dd37d91 (fresh clone, checked out) → jack:~/l14Baranyai_baranyai
- lean-toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474`. This is the expected pair, so `.lake/packages` → `~/barbier/.lake/packages` (symlink).
- New file `Baranyai/L14.lean` (409 lines, sha256 ade44d32b8b7bceb3b4911aee8fdcb53afd92769203986701dbe059100c9d760). One line `import Baranyai.L14` was appended to the end of `Baranyai.lean`. The only change to `gate.sh` is the REQUIRED line. Nothing was committed or pushed.

| theorem (paper) | l14 | namespace-free | witness | distinctness | notes |
|---|---|---|---|---|---|
| `baranyai` (Thm formal) | `l14_baranyai` | yes | `l14w_baranyai` (n=6,k=3) + `l14w_baranyai_explicit` (explicit K₄ factorisation, decide) | 10 pairwise distinct `Finpartition`s of Fin 6, each with 2 triples; explicit witness: 3 classes, each a perfect matching, every 2-set in exactly one | Colour map replaced by `P : Fin C(n-1,k-1) → Finpartition univ`, injective, blocks of size k, every k-set in exactly one `P i`, `#parts·k = n` |
| `baranyai'` | `l14_baranyai'` | yes | `l14w_baranyai'` (n=6,k=2, C(6,2)·2/6=5) | 5 distinct partitions, 3 pairs each | |
| `complete_graph_one_factorisation` | `l14_complete_graph_one_factorisation` | yes | `l14w_complete_graph_one_factorisation` (K₆) | 5 distinct `(⊤:SimpleGraph (Fin 6)).Subgraph`s, each `IsPerfectMatching` and spanning, each edge in exactly one | Uses Mathlib `SimpleGraph.Subgraph.IsPerfectMatching` |
| `baranyai_four_two` | `l14_baranyai_four_two` | yes | `l14w_baranyai_four_two` | G0≠G1, G0≠G2, G1≠G2; edge 01 in exactly one | |
| `Baranyai.baranyai_of_card` | `l14_baranyai_of_card` | yes | `l14w_baranyai_of_card` (α = Fin 2 × Fin 3, k=3) | 10 distinct partitions, 2 triples each | Needs `[DecidableEq α]` (instance only; Mathlib's `Finpartition` on Finset needs it) |
| `Baranyai.baranyai_finset` | `l14_baranyai_finset` | yes | `l14w_baranyai_finset` (s={0,2,4,6}⊆ℕ, k=2) | 3 distinct partitions, 2 pairs each | Needs `[DecidableEq γ]` (instance only) |
| `Baranyai.baranyai_partition` (Thm partition) | `l14_baranyai_partition` | yes | `l14w_baranyai_partition` (Fin 6, k=3) | `Finpartition (powersetCard 3 univ)` with 10 parts (of 20 triples); every class has 2 *distinct, disjoint* triples | One `Finpartition` of the set of k-subsets, `#parts = C(n-1,k-1)`, each class: k-blocks, every vertex in exactly one block, `#C = n/k` |
| `Baranyai.dvd_card_of_factorisation` (converse) | `l14_dvd_card_of_factorisation` | yes | `l14w_dvd_card_of_factorisation` | the hypothesis holds for an explicit 2-block partition {012,345} of Fin 6; the conclusion is used to show that Fin 5 has **no** partition into pairs | Stated as "a `Finpartition univ` into k-blocks ⇒ k ∣ card α". This is equivalent to "some colour class is a 1-factor"; the bridge builds a 2-colouring from the partition |

### Bridges (private, in L14.lean)
- `l14_classes`: a factorising colouring gives an injective family of `Finpartition univ` into k-blocks, each k-set in exactly one family member, with `#parts·k = n` (via `Finpartition.ofExistsUnique` and `Baranyai.class_card_mul`). Injectivity uses a vertex; with no vertex it uses M ≤ 1.
- `l14_choose_le`: when n = 0, (n-1).choose(k-1) ≤ 1 (needed for injectivity in the vacuous n=0 case).
- `l14_matchings`: a factorising colouring of the 2-subsets gives injective perfect matchings of ⊤ that partition the edges.
- `l14_eu`: bounded ∃ in a finset ⇒ ∃! (so `decide` can be used in the witnesses).

## FINDINGS
- **No false Mathlib-only statement was found, and no hypothesis was weakened or added.** The only additions are `[DecidableEq]` instances, which are typeclass instances and not mathematical hypotheses.
- Observation (it confirms the paper's n=0 discussion; it is not a defect): the Finpartition form genuinely **needs `0 < n`**. For n = 0, k = 1 (α empty), `powersetCard 1 ∅ = ∅`, so any `Finpartition` of it has 0 parts, but `(0-1).choose 0 = 1`. So "`Q.parts.card = (n-1).choose (k-1)`" is false without `hn`. The library's `baranyai_partition` already assumes `hn`, and the paper says that `baranyai` at n = 0 is only the vacuous colouring statement. In contrast, the family-of-partitions form `l14_baranyai` stays true at n = 0: the family is injective because there is at most 1 colour. So that form needs no `hn`, matching the library.
- The witnesses for the existence theorems take P/Q/G from the theorem. Their hypotheses are explicit numbers, and the non-degeneracy facts (distinct classes, block counts, disjoint distinct blocks) are proved. A fully explicit hand-written factorisation is given separately for K₄ (`l14w_baranyai_explicit`, checked with `decide`).

## Mechanical namespace check (scratch ~/l14Baranyai_scratch/TypeCheck.lean, set_option pp.fullNames true)
`grep -E "Baranyai\.|baranyai|complete_graph_one_factorisation|dvd_card_of_factorisation"` on the printed types, with the leading theorem name removed, gives **empty** (grep exit 1).
An extra check (ConstCheck.lean) lists every constant used in each l14 type that is defined in a module under the `Baranyai` root:
```
l14_baranyai: repo-constants in type = []
l14_baranyai': repo-constants in type = []
l14_baranyai_of_card: repo-constants in type = []
l14_baranyai_partition: repo-constants in type = []
l14_complete_graph_one_factorisation: repo-constants in type = []
l14_baranyai_four_two: repo-constants in type = []
l14_baranyai_finset: repo-constants in type = []
l14_dvd_card_of_factorisation: repo-constants in type = []
l14w_baranyai_explicit: repo-constants in type = []
l14w_baranyai: repo-constants in type = []
l14w_baranyai': repo-constants in type = []
l14w_baranyai_of_card: repo-constants in type = []
l14w_baranyai_finset: repo-constants in type = []
l14w_baranyai_partition: repo-constants in type = []
l14w_complete_graph_one_factorisation: repo-constants in type = []
l14w_baranyai_four_two: repo-constants in type = []
l14w_dvd_card_of_factorisation: repo-constants in type = []
```
Printed types:
```
l14_baranyai : ∀ (n k : ℕ),
  0 < k →
    k ∣ n →
      ∃ P,
        Function.Injective P ∧
          (∀ (i : Fin ((n - 1).choose (k - 1))), ∀ t ∈ (P i).parts, t.card = k) ∧
            (∀ (t : Finset (Fin n)), t.card = k → ∃! i, t ∈ (P i).parts) ∧
              ∀ (i : Fin ((n - 1).choose (k - 1))), (P i).parts.card * k = n
l14_baranyai' : ∀ (n k : ℕ),
  0 < k →
    0 < n →
      k ∣ n →
        ∃ P,
          Function.Injective P ∧
            (∀ (i : Fin (n.choose k * k / n)), ∀ t ∈ (P i).parts, t.card = k) ∧
              (∀ (t : Finset (Fin n)), t.card = k → ∃! i, t ∈ (P i).parts) ∧
                ∀ (i : Fin (n.choose k * k / n)), (P i).parts.card * k = n
@l14_baranyai_of_card : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] (n k : ℕ),
  0 < k →
    k ∣ n →
      Fintype.card α = n →
        ∃ P,
          Function.Injective P ∧
            (∀ (i : Fin ((n - 1).choose (k - 1))), ∀ t ∈ (P i).parts, t.card = k) ∧
              (∀ (t : Finset α), t.card = k → ∃! i, t ∈ (P i).parts) ∧
                ∀ (i : Fin ((n - 1).choose (k - 1))), (P i).parts.card * k = n
@l14_baranyai_partition : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] (n k : ℕ),
  0 < k →
    0 < n →
      k ∣ n →
        Fintype.card α = n →
          ∃ Q,
            Q.parts.card = (n - 1).choose (k - 1) ∧
              ∀ C ∈ Q.parts, (∀ t ∈ C, t.card = k) ∧ (∀ (a : α), ∃! t, t ∈ C ∧ a ∈ t) ∧ C.card = n / k
l14_complete_graph_one_factorisation : ∀ (n : ℕ),
  Even n →
    ∃ G,
      Function.Injective G ∧
        (∀ (i : Fin (n - 1)), (G i).IsPerfectMatching) ∧ ∀ (v w : Fin n), v ≠ w → ∃! i, (G i).Adj v w
l14_baranyai_four_two : ∃ G,
  Function.Injective G ∧ (∀ (i : Fin 3), (G i).IsPerfectMatching) ∧ ∀ (v w : Fin 4), v ≠ w → ∃! i, (G i).Adj v w
@l14_baranyai_finset : ∀ {γ : Type u_1} [inst : DecidableEq γ] (s : Finset γ) (k : ℕ),
  0 < k →
    k ∣ s.card →
      ∃ P,
        Function.Injective P ∧
          (∀ (i : Fin ((s.card - 1).choose (k - 1))), ∀ t ∈ (P i).parts, t.card = k) ∧
            (∀ (t : Finset ↥s), t.card = k → ∃! i, t ∈ (P i).parts) ∧
              ∀ (i : Fin ((s.card - 1).choose (k - 1))), (P i).parts.card * k = s.card
@l14_dvd_card_of_factorisation : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {k : ℕ}
  (P : Finpartition Finset.univ), (∀ t ∈ P.parts, t.card = k) → k ∣ Fintype.card α
l14w_baranyai_explicit : ∃ K,
  K = {{{0, 1}, {2, 3}}, {{0, 2}, {1, 3}}, {{0, 3}, {1, 2}}} ∧
    K.card = (4 - 1).choose (2 - 1) ∧
      (∀ C ∈ K, (∀ t ∈ C, t.card = 2) ∧ ∀ (a : Fin 4), ∃! t, t ∈ C ∧ a ∈ t) ∧
        ∀ t ∈ Finset.powersetCard 2 Finset.univ, ∃! C, C ∈ K ∧ t ∈ C
l14w_baranyai : 0 < 3 ∧
  3 ∣ 6 ∧
    (6 - 1).choose (3 - 1) = 10 ∧
      ∃ P,
        (∀ (i j : Fin 10), i ≠ j → P i ≠ P j) ∧
          (∀ (i : Fin 10), (P i).parts.card = 2) ∧
            (∀ (i : Fin 10), ∀ t ∈ (P i).parts, t.card = 3) ∧ ∀ (t : Finset (Fin 6)), t.card = 3 → ∃! i, t ∈ (P i).parts
l14w_baranyai' : 0 < 2 ∧
  0 < 6 ∧
    2 ∣ 6 ∧
      Nat.choose 6 2 * 2 / 6 = 5 ∧
        ∃ P,
          (∀ (i j : Fin 5), i ≠ j → P i ≠ P j) ∧
            (∀ (i : Fin 5), (P i).parts.card = 3) ∧ ∀ (t : Finset (Fin 6)), t.card = 2 → ∃! i, t ∈ (P i).parts
l14w_baranyai_of_card : Fintype.card (Fin 2 × Fin 3) = 6 ∧
  ∃ P,
    (∀ (i j : Fin 10), i ≠ j → P i ≠ P j) ∧
      (∀ (i : Fin 10), (P i).parts.card = 2) ∧ ∀ (t : Finset (Fin 2 × Fin 3)), t.card = 3 → ∃! i, t ∈ (P i).parts
l14w_baranyai_finset : {0, 2, 4, 6}.card = 4 ∧
  ({0, 2, 4, 6}.card - 1).choose (2 - 1) = 3 ∧
    ∃ P,
      (∀ (i j : Fin (({0, 2, 4, 6}.card - 1).choose (2 - 1))), i ≠ j → P i ≠ P j) ∧
        (∀ (i : Fin (({0, 2, 4, 6}.card - 1).choose (2 - 1))), (P i).parts.card = 2) ∧
          ∀ (t : Finset ↥{0, 2, 4, 6}), t.card = 2 → ∃! i, t ∈ (P i).parts
l14w_baranyai_partition : ∃ Q,
  Q.parts.card = 10 ∧
    (Finset.powersetCard 3 Finset.univ).card = 20 ∧ ∀ C ∈ Q.parts, C.card = 2 ∧ ∃ t ∈ C, ∃ u ∈ C, t ≠ u ∧ Disjoint t u
l14w_complete_graph_one_factorisation : Even 6 ∧
  ∃ G,
    (∀ (i j : Fin 5), i ≠ j → G i ≠ G j) ∧
      (∀ (i : Fin 5), (G i).IsPerfectMatching) ∧
        (∀ (i : Fin 5), (G i).verts = Set.univ) ∧ ∀ (v w : Fin 6), v ≠ w → ∃! i, (G i).Adj v w
l14w_baranyai_four_two : ∃ G,
  G 0 ≠ G 1 ∧ G 0 ≠ G 2 ∧ G 1 ≠ G 2 ∧ (∀ (i : Fin 3), (G i).IsPerfectMatching) ∧ ∃! i, (G i).Adj 0 1
l14w_dvd_card_of_factorisation : (∃ P, P.parts.card = 2 ∧ ∀ t ∈ P.parts, t.card = 3) ∧
  3 ∣ Fintype.card (Fin 6) ∧ ¬∃ P, ∀ t ∈ P.parts, t.card = 2
```

## Gate
- before: `PASS (32 declarations, standard axioms only)`
- after:  `PASS (49 declarations, standard axioms only)`. Every l14 declaration depends only on [propext, Classical.choice, Quot.sound].
- Forbidden-token scan of L14.lean: clean (no sorry/admit/axiom/native_decide/#eval/set_option/macro/notation/elab/run_cmd).

## Tamper (`bash tests/tamper.sh`, run after the change)
sorry, ax2line, evalfake, macro, falsehyp, wrap: all rejected. Result: `ALL TAMPERING TESTS REJECTED`.

## Hashes (pre-existing files vs fresh clone)
Basic.lean fc63a71e…d31d, Transport.lean 9c59609d…ea76, Partition.lean 551d9d83…d367; scratch/, tests/, lakefile.toml and lake-manifest.json all match the fresh clone (`sha256sum -c` OK). Only `Baranyai.lean` (one appended import line) and `gate.sh` (REQUIRED line only) differ, as intended.

## REQUIRED added (17)
l14_baranyai l14_baranyai' l14_baranyai_of_card l14_baranyai_partition l14_complete_graph_one_factorisation l14_baranyai_four_two l14_baranyai_finset l14_dvd_card_of_factorisation l14w_baranyai_explicit l14w_baranyai l14w_baranyai' l14w_baranyai_of_card l14w_baranyai_finset l14w_baranyai_partition l14w_complete_graph_one_factorisation l14w_baranyai_four_two l14w_dvd_card_of_factorisation

## Logs (jack)
~/l14Baranyai_build0.log, ~/l14Baranyai_gate0.log, ~/l14Baranyai_gate1.log, ~/l14Baranyai_tamper.log, ~/l14Baranyai_typecheck.out, ~/l14Baranyai_constcheck.out, ~/l14Baranyai_hashes.pre
