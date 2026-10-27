# FIX18 — inradius form of the Spieker radical-centre value (Layer 13 finding)

Repo: the arm64 machine:~/lean/paperg_nagel. Finding: Paper G's thm:radical gives the common power as (s² + r²)/4, with r the inradius. The library only had the (s−a)(s−b)(s−c)/s form, and `inradius` appeared nowhere in it.

## Files
- **NEW** `NagelLine/Inradius.lean` (imports `NagelLine.Extensions`):
  - `theorem inradius_sq (t : Triangle ℝ P) : t.inradius ^ 2 = (semiperimeter t - sideA t) * (semiperimeter t - sideB t) * (semiperimeter t - sideC t) / semiperimeter t`. The proof is ported unchanged from the comparer's `inradius_sq_doc` in `~/lean/l13_nagel/scratch/L13_compare.lean`. It uses Heron via `dblArea`/`height0_sq`/`heron_factor`, and Mathlib's `exradius_eq_abs_inv_sum`.
  - `theorem spiekerCenter_power_exsphere_eq_inradius (t) (i : Fin 3) : dist t.spiekerCenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 = (semiperimeter t ^ 2 + t.inradius ^ 2) / 4`. Proof: `rw [spiekerCenter_power_exsphere_eq, inradius_sq]`.
- `NagelLine.lean`: added `import NagelLine.Inradius` just before `import NagelLine.L15Classical`.
- `gate.sh`: added `NagelLine.inradius_sq NagelLine.spiekerCenter_power_exsphere_eq_inradius` to REQUIRED, right after `NagelLine.spiekerCenter_power_exsphere_eq`.
- No other existing files changed. No forbidden tokens (the gate's token check passed).

## Build / gate / tamper
- `~/lean/jl build`: `Build completed successfully (8713 jobs).` The only warnings are the existing unused-variable warnings in L15Classical.
- `~/lean/jl gate`:
  - `'NagelLine.inradius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]`
  - `'NagelLine.spiekerCenter_power_exsphere_eq_inradius' depends on axioms: [propext, Classical.choice, Quot.sound]`
  - `PASS (151 declarations, standard axioms only)` (was 149)
- `~/lean/jl -g tamper`: the tests sorry, ax2line, evalfake, macro, wrap, falsehyp and falsehyp_ext were all rejected → `ALL TAMPERING TESTS REJECTED`

## Commit
`e6e039066074d46b8818afbda02cf01d2aa973e3`, author Josh Bald <jpbald93@gmail.com>, message "Inradius form of the Spieker radical-centre value (Layer 13 finding)". It contains Inradius.lean, NagelLine.lean and gate.sh.

## rb_18_clean
File: `~/lean/paperg_nagel/scratch/RB18_clean.lean`. It is untracked and not committed, and it is outside the gate's SOURCES. It holds:
- verbatim copies of the Blind definitions it needs from `~/lean/reformalG/PaperGBlind.lean` (sha256 f271e87d…, checked): BlindSideA/B/C, BlindSemiperimeter, BlindSpiekerCentre;
- `blind18_stmt`, which is the verbatim `blind_18` written as a Prop.

```
theorem rb_18_clean :
    (type_of% (@NagelLine.spiekerCenter_power_exsphere_eq_inradius V P _ _ _ _)) ∧
      (type_of% (@NagelLine.spiekerCenter_power_exsphere_eq V P _ _ _ _)) →
    blind18_stmt V P
```
The proof only repackages: it uses the definitional agreement lemmas (sides by `rfl`, the semiperimeter as `1/2*(…)` vs `(…)/2` by `ring`, `Sphere.power` unfolded), `rw` with the two real theorems, and `ring`. No new geometric fact is involved.

Compile result (`~/lean/jl lake env lean scratch/RB18_clean.lean`): no errors.
`'PaperGBlind.rb_18_clean' depends on axioms: [propext, Classical.choice, Quot.sound]`

Pair 18 now goes through cleanly in the real → blind direction. The earlier `br_18` (blind → real `_eq`) still holds.
