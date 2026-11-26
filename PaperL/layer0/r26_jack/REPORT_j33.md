# J33 — `EvenCornerQL`: status report

## Outcome
**Closed.** `theorem evenCornerQL_proof : EvenCornerQL` is proved in
`scratch/ChainEvenCornerQL.lean`, together with the one-liners

- `EvenCorner_proof : EvenCorner := evenCorner_of_cornerQL evenCornerQL_proof`
- `heven_inf_all` (statement of `heven_inf_all_of_corner` without `hC`) `:= heven_inf_all_of_corner EvenCorner_proof`
- `cliffordChainS_inf (n) (hn : 3 ≤ n) : CliffordChainS n := cliffordChainS_of_corner EvenCorner_proof n hn`

## File / compile
- Prefix lines 1–5344 untouched (sha256 of `head -5344` = `0d1839e8…0a0f55f`, same as given).
- File is now 5611 lines: **267 extra lines** (5345–5611).
- `lake env lean scratch/ChainEvenCornerQL.lean` → rc = 0, no errors, ~58 s wall.
- No `sorry`/`admit`/`axiom`/`native_decide`/`#eval`/new `set_option` in the appended part.
- Axioms (`#print axioms`, all four new theorems): `[propext, Classical.choice, Quot.sound]`.

## What was proved (lines 5345–5611)
Section `J33` (generic `CommRing R`):
- `kpe5_eq_kpe6_succAbove` — child entry `kpe (2k+5) x y j` = parent entry at column
  `(k+3).succAbove j` (column `k+3` deleted).
- `kpe5_row_dehom` — at `x = -(t y)` the child row sum equals
  `y^(k+3) Σ W_j t^j − y^(k+2) Σ W_{k+3+j} t^j`.
- `reflect_sum_pow` — `t^(k+2) Σ a_j u^j = Σ a_j t^(k+2-j)` when `t u = 1`.
- `child_row_all` (step 1) — if `crossVec (KP (2k+6) x y) (k+3) = 0`, the child cross vector satisfies
  the child row equation at **every** parent point, including the deleted row `i`
  (proof: `det_border` of the row-`i`-bordered child matrix = `det_permute` (by `i.cycleRange⁻¹`) of the
  parent minor without column `k+3`, which is 0).

Complex part (steps 2–3, done directly on dehomogenised polynomials rather than kernel vectors):
- `polyP, polyQ` (the `P`/`Q` halves of `W` as polynomials in `t`), `polyPs, polyQs` (conjugated and
  reversed), `polyF := −X·Q·Ps − P·Qs` (the resultant `R` after dehomogenising, `t = −c/c̄`).
- `polyF_eval_zero` — the row equation `c̄·P(t) = Q(t)` at `t = −c/c̄` (and its conjugate, using
  `conj t = 1/t`) gives `polyF(t) = 0`.
- `polyF_natDegree_le` — `natDegree ≤ 2k+5`; `polyF_coeff_top` — coefficient `2k+5` is `−W_{2k+5}·conj W_0`.
- `evenCornerQL_proof` — `t_r = −c_r/c̄_r` is injective (from `Transversal`, i.e. `GenPosN.1`), so
  `polyF` has `2k+6` roots, hence `polyF = 0` (`eq_zero_of_natDegree_lt_card_of_eval_eq_zero`), so
  `w_last · conj (w 0) = 0`, and `w 0 ≠ 0` gives `w_last = 0`. Only `hV` (its `k+3` component), `hP0`
  and `GenPosN.1` are used; `hall` is not.

## Residual gap
None for this target.
