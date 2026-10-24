# Paper D — source archive

- `paperd.tex`, `bib.tex`, `paperd.pdf`: the paper (build with `pdflatex paperd.tex` twice).
- `numerics/`: reproducible numerical re-check (`python3 paperd_numerics.py`; seed 20261014, 60 digits) and its output.
- `layer13/`: blind re-formalisation. The redacted text given to the blind writer, its Lean statements and report,
  its tool log (`writer_tool_log.json`: every tool call, with host names and local paths redacted), the comparer's report,
  the eleven comparison files, and our recompilation log.
- `reports/`: verification battery reports, the final fresh-clone receipts on x86-64 Linux and arm64 macOS
  (`receipt_final_*.log`, `receipt_cc_*.log`, the scripts, `receipt_final_ADDENDUM.md`), and the hand-check sheet.
- `reviews/`: the independent model reviews and the fix log.

Host names and local paths have been redacted from logs. The Lean developments are in the eight GitHub
repositories at the commits cited in the paper. `SHA256SUMS` covers every file here.
