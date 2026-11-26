# Bridge notes: remaining obstructions

## 1. `blindOfChainS`: radius-zero circle mismatch

`Clifford.IsGCircleS` admits the circle branch for every real radius:

```
∃ o r, X = ((↑) : ℂ → OnePoint ℂ) '' Metric.sphere o r
```

In particular `r = 0` represents the singleton `{(o : OnePoint ℂ)}`. The writer predicate
`BlindIsGCircle` requires `0 < r` in its circle branch, and its line branch always contains `∞`,
so a finite singleton is not a `BlindIsGCircle`.

An odd-level `Clifford.ChainS` object only has to be an `IsGCircleS` containing the level-`(n-1)`
points. If all those points coincide, the radius-zero circle is allowed by the library predicate but
not by the writer predicate. This is exactly the branch named in the header of
`scratch/BridgeBlind.lean` as "modulo the degenerate radius-zero circle".

The library does not rule this branch out under `GenPosN`: `Clifford/Clean.lean` explicitly studies
the case where the five level-4 points coincide, and `GENERAL_REPORT.md` (lines 65-69) records that
radius-zero spheres arise only when all points coincide but that no way to exploit this was found.
Therefore `blindOfChainS` cannot be discharged by the otherwise straightforward recursion without
either (a) proving that coincidence is impossible under `GenPosN`, or (b) exhibiting a genuine
counterexample. Neither was established here, so the `sorry` is left in place rather than faked.

## 2. `N1_RB`: `BlindGenPos` does not imply `GenPosN`

`RealN1` only supplies `Clifford.ChainS n c X` for `c` satisfying `Clifford.GenPosN c`. The writer
hypothesis in `BlindN1` is `BlindGenPos c`, and this is strictly weaker.

Concrete counterexample for `n = 3`:

```
a = 1 + i
b = 2
c = 3/2 + (√3/2) i
```

All three centres lie on the circle `Metric.sphere 1 1`, which passes through `0`, so `cycP = 0`
and `Clifford.GenTriple a b c` fails. On the other hand:

* `conj a * b - a * conj b = -4i`, and the other two pairs are also transversal;
* `triP ≠ 0`, so the three centres are not collinear;
* the three circles have no common nonzero point (a common nonzero point would force the centres
  onto a line determined by that point, contradicting non-collinearity);
* the three second intersections are distinct (approximately `2+2i`, `0.634+2.366i`,
  `3+1.732i`), and they are collinear.

Thus `BlindGenPos` holds while `GenPosN` fails. Consequently `N1_RB` cannot be proved by applying
`RealN1` and the `blindOfChainS` bridge to the given `c`. A direct writer-side construction for
weaker general position, or an additional hypothesis excluding `cycP = 0`, is needed.

## 3. `N6_RB`: existence half

The uniqueness half is proved: `chainS_of_blind` converts a writer object to a library object, and
`Clifford.Counter6S.chainS_six_unique` finishes the job.

For existence, `Clifford.Counter6S.chainS_six` supplies the library object, but converting it back
needs `blindOfChainS` (or an explicit repetition of its proof for the six level-5 line objects
`Clifford.line0`–`Clifford.line5`). The obstruction is the same radius-zero issue above; the
concrete line objects appear to be convertible, but that conversion was not completed here.

## 4. S1 counterexample search (2026-11-25, after Josh's "search for a counterexample")

The witness of §2 shows `BlindGenPos ⇏ GenPosN`, but that is not by itself a counterexample to
`BlindN1`: in that configuration the writer's level-3 object exists, as the line through the three
collinear second points (a blind line contains `∞`).

A search for a genuine counterexample — a `BlindGenPos` `c` with no `BlindClifford n c X` — found
none. Scope: all 3,732 `BlindGenPos` 4-tuples and all 25,820 `BlindGenPos` 5-tuples on the integer
grid `[-2,2]²`; 1,197 random 5-tuples re-checked at 60-digit precision; a 60-config sample at n = 6.
The structurally dangerous case is a quadruple whose four level-3 objects are all lines: every blind
line contains `∞`, so level 4 exists with `X = {∞}`, and the mixed cases still concur. Earlier float
"failures" all dissolved at high precision.

Consequence: `BlindN1` appears **true** at `BlindGenPos`; it is unproved in Lean and not derivable
from `RealN1` (the `blindOfChainS` radius-zero gap remains). Closing row 1 therefore means proving
the blind Clifford chain directly, not rescoping the statement. Details, tables and scripts:
`layer13/s1_counterexample/SUMMARY.md`.
