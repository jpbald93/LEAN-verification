# Bridge report 2: `N6_RB` existence closed

Status after this pass:

| declaration in `scratch/BridgeBlind.lean` | status |
| --- | --- |
| `N6_RB` existence half | proved explicitly for fixed `BlindSix = Clifford.Counter6.cx` |
| `N6_RB` uniqueness half | unchanged, proved |
| `blindOfChainS` | still `sorry` (`scratch/BridgeBlind.lean:331`) |
| `N1_RB` | still `sorry` (`scratch/BridgeBlind.lean:640`) |

The former `sorry` in the existence half of `N6_RB` was replaced by a concrete recursive construction.
No theorem statement was changed, no general `blindOfChainS` was used, and no `axiom`, `admit`,
`native_decide`, `unsafe`, or new `sorry` was introduced. Only files under `scratch/` were touched.

## Construction

The existence proof now:

1. rewrites `BlindSix` to `Clifford.Counter6.cx` and reduces level 6 with
   `rw [BlindCliffordP, if_neg (by decide : ¬ Odd 6)]`;
2. takes the singleton `∞` from `h.1` and fixes the orientation mismatch using
   `Set.singleton_eq_singleton_iff`;
3. for each of the six level-5 children, obtains `Y` and `∞ ∈ Y` from `hchildren i`;
4. applies `blindCliffordP5_of_chainS` using `Clifford.Counter6.cx_genPosN.comp_succAbove i`;
5. proves finiteness of every level-4 singleton by enumerating all pairs `i : Fin 6`,
   `j : Fin 5` with `fin_cases`, converting the nested deletion map to one of the fifteen explicit
   four-point vectors by `convert hq using 1` followed by function extensionality and
   `simp [Clifford.Counter6.cx, Fin.succAbove]`, then applying the matching
   `chainS4_finite_XXXX` lemma.

New helper lemmas are in `PaperLBlind` before `N1_RB`:

* `blindIsGCircle_lineS` — line circles are writer circles (`scratch/BridgeBlind.lean:389`).
* `blindIsGCircle_of_isGCircleS_of_two` — circle branch for two finite points
  (`scratch/BridgeBlind.lean:400`).
* `blindCliffordP2_of_chainS` (`scratch/BridgeBlind.lean:415`),
  `blindCliffordP3_of_chainS` (`scratch/BridgeBlind.lean:423`),
  `blindCliffordP4_of_chainS` (`scratch/BridgeBlind.lean:452`), and
  `blindCliffordP5_of_chainS` (`scratch/BridgeBlind.lean:621`) — the odd/even recursion steps
  actually needed by this construction.
* `chainS4_finite_of_colD` (`scratch/BridgeBlind.lean:477`) plus fifteen concrete
  `chainS4_finite_XXXX` lemmas (`scratch/BridgeBlind.lean:486`–`scratch/BridgeBlind.lean:616`) —
  every four-subset of `Fin 6`.

## Per-level status

| level | status in the new `N6_RB` existence proof |
| --- | --- |
| 6 | Closed directly: even singleton `∞`, using `if_neg (¬ Odd 6)` and `h.1`. |
| 5 | Closed by `blindCliffordP5_of_chainS`: odd circle/line predicate from `hchildren i`, plus the five finite level-4 singletons under `i.succAbove`. |
| 4 | Closed by the fifteen `chainS4_finite_XXXX` lemmas and `blindCliffordP4_of_chainS`; all 30 nested deletions are enumerated explicitly. |
| 3 | Closed by `blindCliffordP3_of_chainS`, reached inside `blindCliffordP4_of_chainS`. |
| 2 | Closed by `blindCliffordP2_of_chainS`, reducing to `BlindSecond`. |
| 1 / 0 | Not unfolded in this level-6 tree; pre-existing circle/singleton machinery is unchanged. |

## Verification

Compile command:

```
cd /home/jackagent/paperL_jack && env PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$HOME/paperL_jack lake env lean scratch/BridgeBlind.lean
```

Exit code: `0`.

Exact final compile output:

```
scratch/BridgeBlind.lean:331:8: warning: declaration uses `sorry`
scratch/BridgeBlind.lean:640:8: warning: declaration uses `sorry`
```

Sorry count from the final compile output:

```
grep -c "declaration uses .sorry." /tmp/opencode/bridge_final_compile.txt
2
```

Line numbers from the final compile output:

```
1:scratch/BridgeBlind.lean:331:8: warning: declaration uses `sorry`
2:scratch/BridgeBlind.lean:640:8: warning: declaration uses `sorry`
```
