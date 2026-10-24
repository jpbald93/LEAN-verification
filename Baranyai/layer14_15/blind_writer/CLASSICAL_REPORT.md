# CLASSICAL_REPORT — Paper Baranyai (blind classical writer, layer 15)

File: `/tmp/blindBaranyai/Classical.lean` (identical to `jack:~/reformal/PaperBaranyaiClassical.lean`,
sha256 `c4f5f448fe40a72f0d7bc860d42ccc02cb101f0d955c5e0797ce8af8c97f37e8`). Namespace `BaranyaiClassical`.

## Statements
| Name | Content |
|---|---|
| `classical_Baranyai1_a` | 0<n, 0<k, k∣n, \|X\|=n ⇒ ∃ `M : Fin C(n-1,k-1) → Finset (Finset X)` partitioning the k-subsets, each `M i` a perfect matching with `n/k` blocks |
| `classical_Baranyai1_b` | Arithmetic part `C(n-1,k-1)·n = C(n,k)·k` (the "= C(n,k)·(k/n)" in the statement, division-free) |
| `classical_Baranyai2_a` | Partition of k-subsets into C(n-1,k-1) parallel classes, each a `Finpartition univ` with `n/k` blocks of size k |
| `classical_Baranyai2_b` | "Equivalently" form: C(n-1,k-1) `Finpartition`s into k-sets, each k-subset a block of exactly one |
| `classical_Baranyai3_main` | 0<k≤n, a : Fin t → ℕ, ∑ a = C(n,k) ⇒ partition into A_i with \|A_i\|=a_i, each almost regular |
| `classical_Baranyai3_a` | k∣n, t=C(n-1,k-1), a_i=n/k: existence of such almost-regular partition with each A_i a perfect matching |
| `classical_Baranyai3_a_implication` | Same parameters: any almost-regular partition with \|A_i\|=n/k consists of perfect matchings |
| `classical_Baranyai3_b` | n even, \|V\|=n ⇒ `n-1` perfect matchings `(⊤ : SimpleGraph V).Subgraph` partitioning the edges of K_n |

## Own definitions (marked OWN DEFINITION)
- `IsPerfectMatchingK k M`: members are k-sets, pairwise disjoint, covering X.
- `IsPartitionOfKSubsets k t A`: each `A i ⊆ powersetCard k univ`, each k-subset in exactly one `A i` (∃!).
- `pointDegree A x`: number of members of A containing x.
- `IsAlmostRegular n k A`: every degree equals `⌊k|A|/n⌋₊` or `⌈k|A|/n⌉₊` (computed in ℚ).

Mathlib notions used: `Finset.powersetCard`, `Finpartition`, `Set.PairwiseDisjoint`, `Nat.choose`,
`Nat.floor/ceil`, `SimpleGraph.Subgraph.IsPerfectMatching`, `SimpleGraph.Subgraph.edgeSet`.

## AMBIGUOUS marks
- `Baranyai2_a/b`: n = 0 allowed by "finite set" wording (C(n-1,k-1) with truncated subtraction); alternative add 0<n.
- `Baranyai3_a`: (a) read as existence + conclusion; alternative bare implication — also provided as `classical_Baranyai3_a_implication`.
- `Baranyai3_b`: n = 0 permitted (no edges, n-1 = 0 in ℕ); alternative require 0<n.

## EXTRA HYPOTHESIS marks
None. (0<n, 0<k, k≤n are all stated in the classical text; `Baranyai3_a` keeps `k ≤ n` inherited from the general form, which follows from k∣n, 0<n anyway — but n=0 is allowed there, where k≤n would fail; it is the general-form hypothesis, not extra.)

## Obligations
None needed: all statements are well-formed without non-degeneracy (C(n-1,k-1) is used directly, division `n/k` is ℕ-division under k∣n). The quoted identity C(n-1,k-1)=C(n,k)·k/n is stated as a theorem (`classical_Baranyai1_b`) rather than an obligation.

## Modelling choices
- Vertex set: `Fintype X` with `Fintype.card X = n`; classes indexed by `Fin N`.
- In Baranyai1/3 classes are `Finset (Finset X)`; in Baranyai2 classes are `Finpartition` parts.

## Compiler summary
`lake env lean PaperBaranyaiClassical.lean` on jack: only 8 `declaration uses 'sorry'` warnings, no errors.

## Files read
- `/tmp/blindBaranyai/classical_statements.txt` (only file read; `ls` of `/tmp/blindBaranyai` also showed `brief.txt`, not opened).
- Wrote: `Classical.lean`, `CLASSICAL_REPORT.md`. No web, no other files, no sub-agents.
