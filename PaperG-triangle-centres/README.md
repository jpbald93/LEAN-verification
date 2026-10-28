# Supporting material — Triangle centres in Lean 4: the Nagel line family and the symmedian and Brocard points

Zenodo: this version https://doi.org/10.5281/zenodo.23741529 · all versions (concept DOI) https://doi.org/10.5281/zenodo.23741528

- `paperg.tex`, `paperg.pdf` — the paper.
- Lean sources: https://github.com/jpbald93/paperg_nagel (commit e40ee54f20588f5181d348767f3f31be20406cc1) and
  https://github.com/jpbald93/paperg_brocard (commit ebb35755a81aec2c7c0673fe93baf8cc5d6eb22d); Lean v4.33.1, Mathlib 0df444a3.
  Each repository is published as a single commit; the development history is not included.
- `reports/` — scout and builder reports (groups A–D, Layer 14, cross-machine run, Layer-15 integration, the
  inradius addition after Layer 13, the draft report), the author's hand-check sheet.
  - `reports/battery/` — every statement-level battery report, on both machines and at every stage; file names give the
    machine (`x86` = x86-64 Linux, `arm64` = arm64 macOS) and the start time; `*_pub_*` are the runs on fresh clones of the
    published commits.
  - `reports/receipts/` — fresh-clone receipts from GitHub on both machines (build, gate line, tamper line, digest of the
    library `.lean` files).
- `layer13/` — blind re-formalisation from the prose: blind text, blind Lean statements, writer report and brief, and the
  two comparison reports.
- `layer14/` — Mathlib-only restatements with explicit witnesses, fully-qualified type listings, gate and tamper logs.
- `layer15/` — statements written from the classical literature (writer brief, report, Lean file) and the two comparison
  reports with their Lean files; the proofs are integrated as `NagelLine/L15Classical.lean` and `Brocard/L15Classical.lean`.
- `reviews/` — the independent reviews of the draft (three rounds by one model family, one by another).

Machine names, IP addresses and home-directory paths are redacted throughout.
