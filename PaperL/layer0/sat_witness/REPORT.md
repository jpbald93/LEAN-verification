# Layer 8 — curated witness-table pass (jack), round 1: 0 of 107 closed

Run 2026-11-26 02:21Z → 03:53Z on `jackagent@[build host]` (92 min, 2 workers, `TABLE_ONLY=1`,
one attempt per name), instrument `lc_sat_witness.py` — a copy of `~/lc_mod/lc_sat.py` with two
additions: a `WITNESS_TABLE` lookup that runs **before** the deterministic patterns, and `TABLE_ONLY`
which returns immediately on a table failure instead of calling the model.

- Input: the 107 unresolved declarations judged most tractable out of jack's 196 (see
  `witness_names.txt`).
- Table (`witness_table_round1.json`): **data values only** — `ℂ` slots from the verified `GenPos5`
  5-tuple `1, 1/2+i/2, 1/5+2i/5, 4/5+2i/5, −4−6i`; `Fin n → ℂ` slots from the parabola
  `j ↦ (j+1) + i(j+1)²` (distinct, no three collinear, no real ratio); `ℕ` slots `1`; every
  propositional slot left to the instrument's `auto` tactic.
- Result: **0 certified, 107 unresolved.** Log ends `ALL DONE`; `round1.log`.

## Why every row failed

| failure class | rows | example |
|---|---|---|
| propositional slot could not be proved — `Inhabited` fallback | 48 | `Transversal.ne` |
| propositional slot could not be proved — unsolved goals | 40 | `miquel_mul` |
| instance synthesis failed inside the witness term | 7 | `chain4_of` |
| witness term misapplied (unknown identifier / type) | 12 | `exists_eqn_of_cD` |

88 of 107 fail on the **hypothesis side**, not on the data: the goal is
`∃ (c d : ℂ) (h : Transversal c d), True`, so the certificate must also *prove* `Transversal c d` for
the chosen `c`, `d`. The instrument's `auto` tactic (`decide`, `norm_num`, `simp` with the file's local
definitions) is not strong enough for complex arithmetic. Two concrete blockers, both verified by
direct compiles on jack:

- its simp set leaves `(starRingEnd ℂ) 2` — the conjugate of a numeral — unreduced inside products and
  quotients, so `norm_num` sees a symbolic expression instead of a number;
- `decide` cannot discharge an equality over `ℂ` (no computable `DecidableEq`), so the cheap route is
  closed.

Proofs do exist and are short when written by hand:

```lean
example : Transversal 1 (1/2 + I/2) := by
  simp only [Transversal]; norm_num [Complex.ext_iff, map_ofNat]   -- closes (verified)
```

but `GenTriple`, `GenPos4`/`GenPos5` (structures with 6+4 and 10+10 fields), `Chain 4 ![…] {q}` and
`mD ≠ 0` each need their own lemma set; the experiments for `GenTriple` did not close with
`norm_num`/`ring_nf` variants.

## What closing them would take

A per-family proof library, roughly 1–2 days of Lean work:

1. `Transversal` for concrete centres — the one-line recipe above generalises.
2. `GenTriple a b c` = `triP ≠ 0 ∧ cycP ≠ 0` — needs the determinant expanded and the `star` of
   numerals reduced; likely a `decide`-free `norm_num`/`ring_nf` combination per configuration.
3. `GenPos4`/`GenPos5`/`GenPosN` — assemble from (1) and (2) with `refine ⟨?_, …⟩`; the field counts
   are known (GenPos4: 10, GenPos5: 20).
4. `Chain 4 ![c₀,c₁,c₂,c₃] {q}` — supply the level-4 point from `Clifford/Counter6.lean`
   (`q0134 = ⟨-6,-4⟩`, `q0135 = ⟨4,-24⟩`, `q0234 = ⟨-8/3,-4⟩`, `q0235 = ⟨4,-2/3⟩`,
   `q1234 = ⟨2/3,-4⟩`, `q1235 = ⟨4,8/3⟩`, `q1245 = ⟨16/3,16/3⟩`, `q1345 = ⟨-8/3,-32/3⟩`,
   `q2345 = ⟨16/9,-16/9⟩`) and close with `chain4_of` plus a `GenPos4` proof from (3).
5. `mD ≠ 0` — `norm_num` on the determinant with the same star-reduction fixes.

Until that exists, the paper's layer-8 claim stands on the two-machine numbers only: **397 of the 577
shared declarations (68.8%) certified by at least one machine, 180 unresolved on both, nothing
refuted.** The witness table does not change that number, and DRAFT §5.2 (v0.7) says so.

## Files

- `round1_results.jsonl` — 107 `sat` rows, all `unresolved` with the Lean error in `history`.
- `round1.log`, `lc_sat_witness.py`, `witness_table_round1.json`, `witness_names.txt`.
- `SHA256SUMS`.
