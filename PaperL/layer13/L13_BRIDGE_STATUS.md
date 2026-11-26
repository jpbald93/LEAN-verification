# Layer 13 bridge layer — status (2026-11-25, second pass)

State of `layer13/BridgeBlind.lean`. First pass collected 11:35Z (8 of 11 targets); second pass
13:05Z closed the existence half of `N6_RB` by an explicit per-level construction. **Row 6 is now
closed in both directions.**

Separate file, separate question — `layer13/BlindChain.lean` (the direct S1 route, row 1): levels
1–4 proved as of 16:58Z 2026-11-25 (`blindChain_three`, `blindChain_four`); one `sorry` left, the
`n ≥ 5` induction inside `blindN1_direct`. Row 1 itself is still open. See the last section.

## Header

- File: `BridgeBlind.lean`, sha256 `f3819d69a6f0fb2296453db9d5d59e9d3796bdcedcb36e37fc79508a37af79ff`,
  829 lines (first pass `9cc060d7…`, 429 lines, kept in git history of the pin). Byte-identical copies on jack (`~/paperL_jack/scratch/BridgeBlind.lean`) and here.
- Compile: `cd ~/paperL_jack && env PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$HOME/paperL_jack lake env lean scratch/BridgeBlind.lean`
  → **exit 0**, no errors, exactly **2 `sorry` warnings** (lines 331 `blindOfChainS`, 640 `N1_RB`),
  no other diagnostics.
- Dependency file untouched: `scratch/BlindCompareFull.lean` md5 `b7b5d257…` on jack and here.
- Integrity: every one of the eleven target statements is textually identical to the frozen skeleton
  (whitespace-normalised comparison of each declaration's signature, proof bodies stripped). Only
  `chainS_of_blind` changed form — `:= by` became a pattern-match `| …` — with the type text
  unchanged. **No statement weakened, no hypothesis added, nothing restated.**
- Axioms (`#print axioms` on the whole file): every proved target depends only on
  `[propext, Classical.choice, Quot.sound]`. `blindOfChainS`, `N1_RB`, `N6_RB` additionally depend
  on `sorryAx`; nothing else does.

## The eleven targets

| # | target | status |
|---|---|---|
| 1 | `mem_sphere_iff_onCircleM` | **PROVED** |
| 2 | `blindTransversal_iff` | **PROVED** |
| 3 | `BlindSecond_eq` | **PROVED** |
| 4 | `genPosN_blindGenPos` | **PROVED** |
| 5 | `isGCircleS_of_blindIsGCircle` | **PROVED** |
| 6 | `chainS_of_blind` | **PROVED** (induction on level; covers all `n`) |
| 7 | `BlindSix_eq` | **PROVED** (`rfl`) |
| 8 | `N7_RB` | **PROVED** — and unconditionally: the proof never uses `h : RealN7` |
| 9 | `N6_RB` | **PROVED** (13:05Z) — existence by explicit per-level construction, uniqueness unchanged |
| 10 | `blindOfChainS` | **UNPROVED** (line 331) |
| 11 | `N1_RB` | **UNPROVED** (line 640) |

**Nine of eleven fully proved; two open** (`blindOfChainS`, `N1_RB`).

## Row status (rows 1, 7, 6)

**Row 7 — CLOSED in both directions.** `N7_RB : RealN7 → BlindN7` is proved, and stronger than
asked: `BlindN7` holds outright (`∀ c, BlindGenPos c → ∃ Y, BlindIsGCircle Y ∧` the three
`BlindSecond` points lie on `Y`). The proof takes `p q r` the three blind second points, gets
`hpq : p ≠ q` from `BlindGenPos`, applies `Clifford.exists_gcircle (cospherical_or_collinear p q r)`,
and converts the resulting `IsGCircle s` (plane, two distinct points) to a blind generalized circle
by the new lemma `blindIsGCircle_of_isGCircle_of_two`, which rules out `r = 0` from `p ≠ q` and
handles the line branch through `rfl`-level rewriting. With `N7_BR` already closed, row 7 now has
a real Lean equivalence — prose and Lean agree for this row.

**Row 6 — CLOSED.** Uniqueness: `chainS_of_blind` plus `BlindSix_eq` (`rfl`) and
`Counter6S.chainS_six_unique`. Existence (second pass): explicit recursion over the fixed
configuration — level 6 is the even singleton `{∞}` from `h.1`; each of the six level-5 children is
handled by `blindCliffordP5_of_chainS`; every level-4 child is a finite singleton, established by
fifteen concrete `chainS4_finite_XXXX` lemmas (one per four-subset of `Fin 6`) after enumerating all
30 nested deletions with `fin_cases`. New helpers `blindIsGCircle_lineS`,
`blindIsGCircle_of_isGCircleS_of_two` and the level-2/3/4/5 steps
`blindCliffordP2..5_of_chainS` are general at their level but were not pushed further. `#print
axioms N6_RB` = `[propext, Classical.choice, Quot.sound]`: no `sorryAx`. Row 6 therefore has a Lean
equivalence, and the paper may say prose and Lean agree for it.

**Row 1 — OPEN.** `N1_RB` cannot be obtained from `RealN1` plus `blindOfChainS`: `RealN1` only
supplies `ChainS` for `c` with `GenPosN`, while `BlindN1` quantifies over `BlindGenPos`, which is
strictly weaker — `BlindGenPos ⇏ GenPosN` because `BlindGenPos` does not require the three second
points to be non-collinear (the plan file already flagged this asymmetry). A concrete `n = 3`
witness is recorded in `BRIDGE_NOTES.md`: centres `1+i`, `2`, `3/2 + (√3/2)i` are transversal,
have `triP ≠ 0`, no common nonzero point, distinct collinear second points — `BlindGenPos` holds,
`GenPosN` fails (`cycP = 0`). Whether `BlindN1` itself is true under `BlindGenPos` is **not**
settled; closing the row needs either a direct writer-side construction at the weaker hypothesis, or
a scoping change to the writer's statement (a statement change, which is Josh's call, not ours).
**Counterexample search (2026-11-25, Josh's call): none found** — see
`layer13/s1_counterexample/SUMMARY.md`. All 3,732 `BlindGenPos` 4-tuples and all 25,820 5-tuples on
the integer grid `[-2,2]²`, plus 1,197 random 5-tuples at 60 digits and a 60-config n = 6 sample, all
admit the blind object (the all-lines case is absorbed because a blind line contains `∞`). So
`BlindN1` appears **true** at the weaker hypothesis; rescoping would weaken a true statement, and row
1 stays open in Lean because `blindOfChainS`'s radius-zero gap remains the only route from `RealN1`.
Closing row 1 now means proving the blind Clifford chain directly, not changing the statement.

**Direct route progress (16:58Z):** levels 1–4 of the blind chain are now proved at `BlindGenPos` in
`BlindChain.lean`, level 4 including the mixed-degenerate case. What remains for row 1 is the
induction from level 5 upward — see "S1 direct proof — second attempt" at the end of this file.

## Every other row (unchanged from `L13_FULL_COMPARE.md`)

- Rows 2 and 3: still open in the real ⇒ writer direction, and not a bridge problem. The writer
  demands incidence of *every* certified singleton on one circle; the library proves it for the
  canonical `EptInf` only, and general `UniqEven` is false (`scratch/not_UniqEven.lean`). Needs a
  new universal-incidence theorem.
- Rows 4 and 5: still open. Needs the plane ⇄ sphere encoding translation (`Chain` on `Set ℂ` versus
  `BlindCliffordFin`/top-contained variants on `Set (OnePoint ℂ)`), `r > 0` handling and the
  radius-zero case. Phase 2.

## What blocks `blindOfChainS`

`Clifford.IsGCircleS` admits the circle branch for every real radius, including `r = 0`, which is the
finite singleton `{o}`. `BlindIsGCircle` requires `0 < r` in its circle branch and its line branch
always contains `∞`, so a finite singleton is not blind. An odd-level `ChainS` object whose
level-`(n-1)` points all coincide is therefore legal in the library and illegal for the writer. The
library does not exclude this under `GenPosN` (`Clifford/Clean.lean` studies the coincident case and
`GENERAL_REPORT.md` lines 65-69 record radius-zero spheres arising exactly when all points coincide,
with no way found to exploit it). The run left the `sorry` rather than faking the branch — correct
call. Two routes remain: (a) prove coincidence impossible under `GenPosN`; (b) exhibit a
counterexample to `blindOfChainS` as stated (which would be a real negative result about the bridge,
not about the rows). The third, cheaper route was taken in the second pass and closed row 6 existence
without the general lemma: the construction works level by level on the concrete `Counter6.cx`
configuration, where coincidence is decided by computation rather than by general-position theory.
So `blindOfChainS` now blocks only the general transport, and with it row 1 — not row 6.

## Caveats

- The nine proved targets have **not** been through a mutation/tamper battery; this is a
  statement-and-proof check only. The statements are the frozen ones, so a mutation pass would test
  proof robustness, not fidelity.
- `~/paperL_jack` is now a git repo pinned at `d15464f` (2026-11-25 13:08Z, tree clean, 153 files,
  `MorleyKernel` `dce7b011…`); nothing pushed (no remote). Both commits already contain the
  second-pass `BridgeBlind.lean` (`f3819d69…`). `scratch/_bb_ax.lean` and `scratch/_bb_ax2.lean` are
  the run's own axiom-check working copies and are not part of the audited set — `scratch/BridgeBlind.lean`
  is the only bridge source.
- `N7_RB` being unconditional makes the row strictly stronger than the paper states; the paper's
  row-7 claim can say equivalence, and may note the strengthening.
- The N6 construction is specific to `Counter6.cx`; it does not generalise to `blindOfChainS`, whose
  radius-zero obstruction is unchanged. `blindOfChainS` and `N1_RB` are the two remaining `sorry`s.

## Independent re-check (2026-11-25 13:33Z, scheduled look on jack)

The scheduled check that was set for 08:30 ET fired *after* the second pass had already been
collected, so it re-verified the collected state from scratch rather than collecting:

- no `opencode run` live (the second pass ended 11:55Z, run log `~/paperL_bridge2/run.log` tail
  `EXIT_CODE=0`, `SORRY_COUNT=2`); `scratch/BRIDGE_REPORT2.md` present, sha256 `2af44bfd…`;
- `sha256sum scratch/BridgeBlind.lean` = `f3819d69…`, 829 lines, byte-identical to
  `layer13/BridgeBlind.lean` here;
- fresh compile: **rc 0**, exactly two `sorry` warnings (lines **331** `blindOfChainS`, **640**
  `N1_RB`); no `axiom` / `native_decide` / `unsafe` anywhere in the file;
- `#print axioms` on all eleven targets: nine on `[propext, Classical.choice, Quot.sound]`;
  `N6_RB` and `N7_RB` among them with no `sorryAx`; only `blindOfChainS` and `N1_RB` carry `sorryAx`;
- all eleven declaration signatures textually identical (whitespace-normalised, proof bodies cut) to
  the pass-1 file `~/paperL_bridge2/BridgeBlind.before.lean` (sha `9cc060d7…`), which was itself
  diffed against the frozen skeleton — so no statement regressed across pass 2.

Remaining open targets: **two** — `blindOfChainS` (general transport; radius-zero branch) and
`N1_RB` (row 1 R→B; `BlindGenPos` vs `GenPosN` gap). Rows 2/3 and 4/5 are open for the reasons above.

## S1 direct proof — first attempt (2026-11-25 15:47Z, jack, 80 min)

New file `layer13/BlindChain.lean` (sha `3a05d805…`, 242 lines, namespace `BlindChain`), report
`layer13/BRIDGE_REPORT3.md`. Compile exit 0, exactly **2 `sorry`s**, no `axiom`/`admit`/
`native_decide`/`unsafe`. `BridgeBlind.lean` and its eleven signatures untouched.

**Proved (all on `[propext, Classical.choice, Quot.sound]`):**

- `blindChain_three : BlindGenPos c → ∃ Y, BlindCliffordP false 3 c Y` — **stage A complete**,
  for `c : Fin 3 → ℂ`, including the branch where the three second points are collinear (the
  writer object is the line through them plus `∞`).
- `blindChain_four_of_genPos4` — level 4 whenever all four triples have non-collinear second
  points, via `Clifford.chain4_ofS` and `blindCliffordP3_of_chainS`.
- supporting `second_eq_of_collinear`, `noncollinear_centres_of_blind`, `genTriple_of_blind`,
  `genPosN_three_of_genPos4`, `genPos4_of_blindGenPos` (the last two are the exact
  `BlindGenPos → GenPosN` translation on a quadruple, given the four non-collinearity facts).

**Open (the two `sorry`s):**

- `blindChain_four` — the mixed-degenerate branch: at least one but not all triples collinear.
  The obstruction is that `Clifford.chain4_of`, `clifford_one` and `gamma_cospherical` all need
  `cycP ≠ 0`, and in the mixed case `mD = 0` makes `Clifford.miquel` the junk value `0`. The
  missing identity is recorded in the report (`cD_second_of_cycP_zero` plus three permutations):
  for a collinear triple `a b c`, the four-point sets `{s_ac, s_ad, s_cd, s_ab}` and
  `{s_bc, s_bd, s_cd, s_ab}` are cospherical-or-collinear, which `cD_eq_zero_iff` and
  `exists_gcircle` would then convert.
- `blindN1_direct` for `n ≥ 5` (stage C): needs a degenerate Clifford second theorem
  (`clifford_two_clean_blind`) and a `ChainS → Blind` transport at `BlindGenPos`.

So S1 moved from nothing to "levels 3 and the generic level 4 proved, two named lemmas short".
Row 1 is still open: the statement covers all `n`.

## S1 direct proof — second attempt (2026-11-25 16:58Z, jack, 60 min of a 90-min box)

Report `layer13/run4/BRIDGE_REPORT4.md`, run log `layer13/run4/run.log`, source
`layer13/BlindChain.lean` sha256 `85fe68f5…`, 927 lines (was 242). Verified here after collection,
not taken from the report:

- fresh compile on jack (`env PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$HOME/paperL_jack lake env lean
  scratch/BlindChain.lean`) → **exit 0**, 9 s, no errors, exactly **one `sorry` warning**
  (line 908 `blindN1_direct`, the `n ≥ 5` tail). No `axiom` / `admit` / `native_decide` / `unsafe`.
- `blindChain_four` (line 544) is **proved** — the mixed-degenerate branch is closed. Its signature
  is textually identical to the pre-run copy `~/paperL_bridge4/BlindChain.before.lean`, so no
  statement moved.
- `#print axioms` via a built `.olean`: `blindChain_four`, `blindChain_three`,
  `miquel_gcircles_of_one_degenerate`, `degenerate_gcircle_of_cycP_zero` all on
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

How level 4 was closed: the case split is generic (all four triples non-degenerate → the pass-3
`blindChain_four_of_genPos4`), exactly one degenerate triple (new core lemma
`miquel_gcircles_of_one_degenerate` on `q = Clifford.miquel a b c d`, with
`degenerate_gcircle_of_cycP_zero` for the degenerate triple and `Clifford.gamma_cospherical` for the
other three), and all four degenerate (`p = ∞`, since a blind line contains `∞`). **Two degenerate
triples cannot occur** under `BlindGenPos`: `all_four_collinear_of_two_degenerate` contradicts the
hypotheses. Also new: `gq0_ne_zero_of_transversal`, `cycP_all_zero_of_two`,
`blindGenPos_succAbove`, `blindChain_three_of_gcircle`, `blindChain_three_of_collinear`,
`blind_second_symm`, and the `ring` identities
`crs12 * cycP(a,c,d) = -crs14 * cycP(a,b,c) + crs13 * cycP(a,b,d)` and its `(b,c,d)` mirror.

**Negative result recorded:** the `cD_second_of_cycP_zero` identity the previous report nominated as
the missing step is **false** — sympy counterexample `cD(s03,s02,s23,s01) = 256/5` — and was not
used. The mixed case is closed by the Miquel route above instead. Do not re-dispatch the `cD` target.

**Still open in S1:** level 5 and the induction step, one `sorry` inside `blindN1_direct` (line 908).
Needs a degenerate Clifford second theorem (`clifford_two_clean_blind`) and the `ChainS → Blind`
transport at `BlindGenPos`. Levels 1–4 of the direct route are now proved, so row 1 is short by the
induction, not by its base cases.

## S1 direct proof — third attempt (2026-11-25 17:45Z, jack, ended 60 min early)

Report `layer13/run5/BRIDGE_REPORT5.md`, log `layer13/run5/run.log`, source
`layer13/BlindChain.lean` sha256 `6d5bfe5d…`, 1296 lines (was 927). Verified here, not taken from
the report:

- fresh compile on jack → **exit 0**, 23 s, zero errors, exactly **one `sorry` warning**
  (line 1248, `blindClifford_second`).
- signatures of `blindChain_three`, `blindChain_four`, `blindN1_direct`,
  `miquel_gcircles_of_one_degenerate` byte-identical to the run-4 file (`run5/BlindChain.run4.lean`);
  six new declarations. No statement weakened.
- `#print axioms`: `blindChain_five_of_genPos5`, `blindChain_five_of_finite_miquel`,
  `clifford_two_clean_blind`, `blindCliffordP5_of_five_points`, `blindChain_four`,
  `blindChain_three` → `[propext, Classical.choice, Quot.sound]`.
  `blindClifford_second` → `sorryAx` (the one gap); `blindChain_succ` and `blindN1_direct` inherit
  it, correctly — they are derived, not assumed.

**Level 5, general position — CLOSED.** `blindChain_five_of_genPos5 : Clifford.GenPosN c →
∃ Y, BlindCliffordP false 5 c Y`. Route: the five level-4 blind objects via
`blindCliffordP4_of_chainS` on `Clifford.chain4_ofS`; concyclicity of the five Miquel points from
`Clifford.clifford_two_clean h.pos5` + `Clifford.exists_gcircle`, with the radius-`0` sphere
replaced by a unit circle through the common point and lines transported by
`Clifford.lineS`/`blindIsGCircle_lineS`.

**Level 5, finite Miquel subcase of `BlindGenPos` — CLOSED.**
`clifford_two_clean_blind` is `Clifford.clifford_two_clean` with `GenPos5` replaced by exactly the
hypotheses its proof uses (pairwise transversality, ten non-collinear centre triples, `mD ≠ 0` on
every 4-subset); + `blindCliffordP5_of_five_points` + `blindChain_five_of_finite_miquel`. Covers
every `BlindGenPos` 5-tuple in which no deletion has all four triples degenerate.

**All-`n` reduction — CLOSED, with the gap named.** `blindN1_direct` now proves the induction for
all `n` using `blindClifford_second m` as the step; `blindChain_succ` is the paper-facing alias.
The single `sorry` is exactly `blindClifford_second (m) (hm : 3 ≤ m)`:
from a level-`m` object for every deletion, build the level-`(m+1)` object. For odd `m+1` that is
"the `m` level-`m` points lie on one blind generalized circle"; for even `m+1` the dual concurrency.
`m = 4` is proved (above). So S1 is no longer "levels 1–4"; it is "levels 1–5, and one named
per-level lemma for the rest".

**What remains, exactly:** the deletion whose four triples are all degenerate (`mD = 0`, level-4
object `∞`) needs a line through the other four level-4 points plus `∞`. The report gives a checked
rational instance of that case: centres `1, 1/2+i/2, 1/5+2i/5, 4/5+2i/5, −4−6i`; the first four
lie on `x²+y²=x`, deletion 4 has object `∞`, and the other four level-4 points
(`8/35+36i/35, 48/35+4i/5, 68/35+24i/35, 107/140+129i/140`) are collinear, so the expected level-5
object is that line plus `∞`. Verifying that in general is the next concrete target.
