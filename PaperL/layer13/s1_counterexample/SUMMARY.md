# S1 counterexample search — result: none found

Date: 2026-11-25 (13:34Z decision by Josh: "Search for a counterexample"; work 13:36–14:0xZ).
Question: is `BlindN1` **false** at the writer's weaker hypothesis `BlindGenPos`
(so that row 1 needs the `GenPosN` rescope), or is it true and merely unbridged?

Answer: **no counterexample found**. `BlindGenPos` configurations do admit blind level
objects up to the levels searched; the degenerate cases are absorbed by the line branch of
`BlindIsGCircle`, not broken by it.

## What is being searched for

`BlindN1` (`scratch/BlindCompareFull.lean:79`) says: for every `n ≥ 1` and every
`c : Fin n → ℂ` with `BlindGenPos c`, some `X` satisfies `BlindClifford n c X`.

`BlindGenPos` is `GenPosN` minus the non-collinearity of the three second points
(`cycP ≠ 0`). So the only configurations where the two hypotheses differ are those whose
second points are collinear, and those are exactly where the writer's level-3 object must be
a **line plus ∞** instead of a circle. A counterexample therefore has to be a configuration
that is perfectly legal for the writer and still has no nested blind object.

## Method

Exact rational model of the blind predicates (circles through 0, `BlindSecond`, `BlindGenPos`,
`BlindIsGCircle`, `BlindCliffordP`), independent of Lean:

- level 1 — circle centred `c 0` through 0; level 2 — the second point singleton;
- odd `n ≥ 3` — a generalised circle containing, for each deletion, one admissible level-`(n-1)`
  singleton (unique: three distinct second points determine a circle, or a line if collinear);
- even `n` — a point lying in one valid level-`(n-1)` object of every deletion.

A blind line always contains `∞`, so an all-lines deletion quadruple forces `p = ∞` at the next
level; that is the natural place for the chain to break.

## Results

| search | configurations | failures |
|---|---|---|
| exhaustive, integer grid `[-2,2]²`, n = 4 | 3,732 `BlindGenPos` 4-tuples | **0** |
| exhaustive, same grid, n = 5 | 25,820 `BlindGenPos` 5-tuples | **0** |
| random, quarters in `[-20,20]`, n = 5, 60-digit mpmath | 1,197 | **0** |
| random, quarters in `[-10,10]`, n = 6, 50-digit mpmath | 60 | **0** |

Sanity check of the model: on 2,955 random `BlindGenPos` 4-tuples it reproduces Morley
concurrence (four level-3 circles through one point), 0 exceptions — the model is implementing
the classical theorem, not an artefact.

Precision note: a first float pass (tolerance 1e-9) reported 48 "n = 5 failures" at larger
coordinates. Every one re-checked at 60 digits was a float artefact — the five points were
concyclic to 40+ digits. The failures disappeared with exact/high-precision arithmetic.

Documented degenerate case (`BRIDGE_NOTES.md`, centres `1+i`, `2`, `3/2 + (√3/2)i`): the three
second points are `(2,2)`, `(0.634, 2.366)`, `(3, 1.732)` — distinct and exactly collinear, so
`GenPosN` fails while `BlindGenPos` holds, and the blind level-3 object is the line through
them. Consistent with the model.

## What this means for S1

- `BlindN1` looks **true** at `BlindGenPos`; the paper's row-1 writer statement is not a
  defective statement, so rescoping it to `GenPosN` would weaken a true claim.
- It is still **unproved in Lean**, and it cannot be derived from `RealN1`: `RealN1` only gives
  `ChainS` under `GenPosN`, and `blindOfChainS` (the general transport) is itself open on the
  radius-zero branch. So row 1 stays open in Lean either way.
- The only route that closes row 1 without weakening the statement is a direct proof of the
  blind Clifford chain at `BlindGenPos` — a self-contained induction in which the collinear
  case becomes a line and `∞` plays the common point. That is a separate, sizeable job.

## Reproduce

```
python3 AFM/PaperL/layer13/s1_counterexample/search5.py     # exhaustive n=4 and n=5
python3 AFM/PaperL/layer13/s1_counterexample/hpsearch.py    # 60-digit random n=5
python3 AFM/PaperL/layer13/s1_counterexample/level6.py      # sampled n=6
python3 AFM/PaperL/layer13/s1_counterexample/verify_hp.py   # re-check one candidate at 60 digits
```

## Limits (stated plainly)

- n = 6 was sampled, not exhausted, and mixed line/circle candidate enumeration there is
  partial; n ≥ 7 not searched at all.
- "No counterexample" is evidence, not a theorem. The claim that `BlindN1` is true remains a
  conjecture until it is proved in Lean or a counterexample is found.
