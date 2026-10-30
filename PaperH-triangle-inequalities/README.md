# Supporting material — Classical triangle inequalities and the Fermat–Napoleon configuration in Lean 4

- `paperh.tex`, `paperh.pdf` — the paper.
- Lean sources (Lean v4.33.1, Mathlib 0df444a3):
  - https://github.com/jpbald93/paperh_euler (commit 0c95102c792b8d47d2720f4e9fbc39aa5f21a424) — Euler family, Gerretsen, Kooi, Weitzenböck, Hadwiger–Finsler, isoperimetric, Leibniz, Neuberg–Pedoe, Ptolemy's inequality
  - https://github.com/jpbald93/paperh_mordell (commit 7b2270146195cf2a4c589e403143dba0abd0f6a7) — Erdős–Mordell (with equality case), Barrow, Fermat–Torricelli
  - https://github.com/jpbald93/paperh_fermat (commit 8f680c86b068196a4d27201209c856a5d038aaa4) — Ptolemy equality case, Fermat–Napoleon lines, Napoleon
  In each repository the first commit is the library described in the paper (the development history is not included); the next two add the Layer-14 and Layer-13/15 files without changing any earlier file.
- `reports/` — prior-art scout, builder reports (groups H1–H4), the draft report, the Layer-13/15 integration report.
  - `reports/battery/` — statement-level battery reports; `x86` = x86-64 Linux, `arm64` = arm64 macOS; `*.pub_*` are the runs on fresh clones of the published commits.
  - `reports/receipts/` — fresh-clone receipts from GitHub on both machines (build, gate line, tamper line, digest of the library `.lean` files), at the first public commits and at the final commits.
- `layer13/` — blind re-formalisation from the prose: blind text, writer brief, blind Lean statements, writer report, and the two comparison reports (the comparison proofs are in the libraries as `<Lib>/L13Blind.lean`).
- `layer14/` — Mathlib-only restatements with explicit witnesses: report and fully-qualified type listings (the files are `<Lib>/L14.lean`).
- `layer15/` — statements written from the classical literature: writer brief, Lean file, writer report, and the two comparison reports (proofs in `<Lib>/L15Classical.lean`).
- `reviews/` — the three independent reviews of the draft (Claude Opus 5.5, GPT-6 Astra, Gemini 4 Argon).

Machine names, IP addresses and home-directory paths are redacted throughout.
