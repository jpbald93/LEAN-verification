# Paper K — supporting material

Companion to *Apollonius centres in Lean 4: the cofactor construction, equal Laguerre power, and
degenerate configurations* — `paperk.pdf` in the Zenodo record. The Lean development is a single repository,
`paperk` (`paperk_apollonius` on GitHub), pinned at commit
`464a59df987e149e1e545cbd5299196ecce354ed`. This folder holds the evidence that is not the library code:
prior art, the layer reports, the receipts, the battery reports, the reviews and the name-gate output.

| item | what it is |
|---|---|
| `SCOUT.md` | prior-art scout written **before** any proof was dispatched (protocol: `AFM/NOVELTY_SCOUT_PROTOCOL.md` in the author's workspace); its own header requires a pre-draft re-run, which was not made — the paper says so |
| `L11_K_ANCHORS.md` | Layer 11 name/line gate: every `\decl` and `\src` in the paper checked against the pinned tree (NAME GATE PASS, 57 declarations, 18 anchors, 0 ungated) |
| `namegate_k.py` | the checker behind it (`python3 namegate_k.py paperk.tex repo_flat_464a59d`) |
| `repo/` | pristine export of the gated repository at `464a59d`: `PaperK.lean`, the five library files, `gate.sh`, `tests/tamper.sh`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, plus `paperK_464a59d.bundle` (the exact object that was pushed) |
| `layer10/` | Layer 10 definition bridges: `Bridge_paperK.lean` (36 bridges), `REPORT_L10.md`, the independent `gate.sh` run |
| `layer13/` | Layer 13 blind re-formalisation: the frozen prose the writer was given (`paperk_frozen_v2.tex`, plus the plain `paperk_prose.txt` it extracted), the blind statement file (43 statements), the comparer's `BlindCompare_K.lean` and its report, and the writer's statement/ambiguity table |
| `layer14/` | Layer 14 restatements (a: 8 rows, b: 8 rows, c: 5 rows) and the repair report for rows 7–8 |
| `layer15/` | Layer 15 classical comparison against the verbatim source (17 rows) and its verifier |
| `reports/` | the numbers the paper quotes at the pin: gate output, battery/tamper report, promotion report, and the two clean-export second-machine receipts |
| `reviews/` | the three review rounds and their triages: draft v1 (12 major / 25 minor), v3 (Argon 9 / Astra 16), v4 (Astra fix-check + Opus 2 major / 14 minor) |
| `numerics/` | the independent numerical checks: the `K0` formula (`FORMULA.md`, `k0_formula.py`), the explicit `P_X`, the degenerate loci, the at-infinity behaviour, the iteration/continuity probes, and `EXTENSION.md` (the extension analysis and the numeric refutations the paper cites) |

Notes a reader of the paper needs:

- **Two negative results are kept visible, not dropped.** The general-`n` "centroid" reading of the
  degenerate case is false — `PaperKn.brief_E_false` proves a counterexample at `n = 2` — and the
  completion map of the source's Theorem 3.4 does **not** fix `P_X` (refuted numerically, `numerics/`).
  Anything written about this paper must keep both.
- **The at-infinity case is outside the paper's claim.** Paper K does not formalise the at-infinity /
  improper classification and does not discuss it: §`sec:not` records the hyperplane encoding only as the
  missing ingredient of Theorem 3.6. (Carver's 1920 classification is cited in Paper I, not here.)
- **Source status**: Proposition 3.1's collinearity step is formalised (with its spanning hypothesis made
  explicit, the source's derivation of it not formalised); Theorem 3.4, Theorem 3.6 and the Morita corollary
  are **not** formalised in any dimension, and §`sec:not` says exactly what would be needed.
- **Sign convention**: the source's display `(X|Y) = −rr' + c·c' + vw' + wv'` is the negative of the Lean
  `B`; zero-set statements transfer, value statements flip. §3 of the paper states it in that form.
