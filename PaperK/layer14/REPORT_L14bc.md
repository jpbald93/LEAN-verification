# Paper K — Layer 14 parts 2 and 3, collection status (2026-11-16)

## Part 3 (L14c) — counted: 5 rows, 5 E
Job `/tmp/afmrun/paperK/l14c` (john), 18:11–18:20 on 2026-11-10. Deliverable `paperK_l14c.lean`
(ns `PaperKL14c`, `import Mathlib` only, 257 lines) plus `RESTATE_c.md`. Verdicts: the five ℝ³ claims,
all **E** — with the explicit caveat that row 5 (`tetra_thm36`, now `tetra_E1_apollonius`) is a faithful
restatement of an **E1 fact**, not of the source's Theorem 3.6. The report's naming audit is the reason
the repository renamed the theorem.

Report: `RESTATE_L14c.md`. Independent recompile in this collection pass (2026-11-16, john,
`~/lean/l13_inversion/scratch/paperK_l14c.lean`): `lake env lean` rc=0, no `sorry`/`admit`/`native_decide`/
`axiom` token, 257 lines, sha256 `cd82f7313ed9ebdc0999ea324c5904f0236e2f73788576cf16b71300e44b093d`
(identical to the copy here), tracked tree clean. The axiom report for its declarations was written by the
run itself (`RESTATE_c.md`: 5 rows, all on the standard axioms). Status: counted with the E1 caveat on
row 5, and the paper (§9) says the layer-14 part-3 verdicts are as reported.

## Part 2 (L14b) — NOT counted
Job `/tmp/afmrun/paperK/l14b` (jack). The runner wrote `paperK_l14b.lean` (25,878 bytes) and then died at the
write step: the log's last line is the proxy's `credits have been exhausted` error, and no report was
written. Collected 2026-11-16 by compiling the delivered file on jack inside `~/paperK/scratch`:

```
lake env lean scratch/paperK_l14b.lean   -> rc=1
389:4: error: `simp` made no progress
430:11: error: Application type mismatch (rfl vs True)
480:10: error: ring failed, ring expressions not equal
554:2: error: No goals to be solved
```

Rows 1–6 of the eight compile; the two failures are in row 7 (`Msq` rank / kernel, the `simp` at 389 and
the `rfl` at 430) and row 8's bridge chain (`D3 ≠ 0 ↔ AffineIndependent`, the `ring` at 480 and the
trailing `simp` at 554). So the layer is **6 of 8 rows, unverified as a whole**, and the paper reports it
as partial rather than as passing. `scratch/` is excluded through `.git/info/exclude`; the tracked tree
stayed clean (`git status --short` empty).

Next: repair the four proofs (or drop rows 7–8, which overlap L14a's `PX_circumcentre` and
`equal_power_point_unique` rows) and re-run. Until then no L14b row is quoted anywhere in the paper.
