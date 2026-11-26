# Layer 13 bridge layer — plan (2026-11-25)

Goal: close the real ⇒ writer direction of the layer-13 comparison by supplying the predicate
bridges the library lacks. Created and dispatched 2026-11-25 02:35Z.

Targets, in dependency order (`layer13/BridgeBlind.lean`, statements fixed and typechecked):

1. `mem_sphere_iff_onCircleM` — writer's circle `Metric.sphere c ‖c‖` ↔ library `OnCircleM c`.
2. `blindTransversal_iff` — `BlindTransversal c d` (unique nonzero common point) ↔ `Transversal c d`
   (`conj c * d ≠ c * conj d`). The two failure modes (tangency at `M`, identical circles) must both
   give "no unique nonzero point".
3. `BlindSecond_eq` — under `Transversal`, the choice in `BlindSecond` is `Clifford.second`. Needs
   uniqueness of the nonzero intersection, which follows from the radical-axis argument.
4. `genPosN_blindGenPos` — `GenPosN ⇒ BlindGenPos`: `triP ≠ 0` rules out a common nonzero point of a
   triple (such a point puts all three centres on one line); distinctness of the second points then
   follows from that. Note the asymmetry: `BlindGenPos` does **not** require the three second points
   to be non-collinear, so `BlindGenPos ⇏ GenPosN` — only the direction we need is true.
5. `isGCircleS_of_blindIsGCircle` — writer's circle branch has `0 < r`, so it maps into `IsGCircleS`;
   the line branch matches `lineS`. The converse fails only at `r = 0`, which is why it is not
   stated.
6. `blindOfChainS` — induction: the even-level branch needs the extra conjunct `BlindIsGCircle Y`
   that `ChainS` omits; it comes from the induction hypothesis at the odd level `n + 2`.
   `chainS_of_blind` is the converse and is not needed for the rows, but stated for completeness.
7. Rows: `N1_RB` (from `RealN1`), `N7_RB` (level 3), `N6_RB` (existence and uniqueness at level 6,
   with `BlindSix_eq : BlindSix = Counter6.cx`).

What this cannot close:
- **Rows 2 and 3**: the writer asks for incidence of *every* certified singleton on one circle; the
  library proves it for the canonical `EptInf` point only. Since general `UniqEven` is false
  (`scratch/not_UniqEven.lean`), no bridge can identify the certified points with `EptInf`; a new
  universal-incidence theorem is required. This is a real mathematical gap, not a definitional one.
- **Rows 4 and 5**: need a plane ⇄ sphere encoding translation (`Chain` on `Set ℂ` vs
  `BlindCliffordFin`/top-contained variants on `Set (OnePoint ℂ)`), plus the `r > 0` and
  radius-zero handling. Phase 2.

Run: `jack:~/paperL_jack` (opencode), file `scratch/BridgeBlind.lean`, log `~/paperL_bridge/run.log`,
report `scratch/BRIDGE_REPORT.md`. Compile check:

```
cd ~/paperL_jack && env PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$HOME/paperL_jack \
  lake env lean scratch/BridgeBlind.lean
```
(`LEAN_PATH` is required so `import scratch.BlindCompareFull` resolves; its `.olean` is built at
`scratch/BlindCompareFull.olean`.) Skeleton compiles at 2026-11-25 02:30Z with 11 `sorry` warnings,
which is the statement-level gate: every signature typechecks as written.
