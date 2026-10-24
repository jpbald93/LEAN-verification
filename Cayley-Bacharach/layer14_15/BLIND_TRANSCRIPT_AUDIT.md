# Blind-writer transcript audit (Layer 15)

Generated 2026-10-22 18:35 by re-reading the complete tool-call transcripts of every Layer-15 statement collector and blind Lean writer. Each row lists every file-reading tool call (Read/Glob/Grep), every web call, and every shell command that reads a file other than the agent's own outputs. Pass criterion for the Lean writer: no read of any file except its own brief/outputs and its own compiler output; no web access. Pass criterion for the statement collector: no local file reads except its own outputs; no web query or URL mentioning jpbald93, GitHub, Lean, Mathlib, AFM or formalisation.

| run | transcript (sha256 prefix) | tool calls | Read/Glob/Grep | web calls | suspicious web | other shell reads | verdict |
|---|---|---|---|---|---|---|---|
| tmp-blindD | `267dc13060ed` | 7 | 0 (own outputs only) | 0 | 0 | head -60; head -60 | PASS* |
| tmp-blindC-stmtwriter | `ec36d0bd8245` | 12 | 0 (own outputs only) | 8 | 0 | — | PASS |
| tmp-blindC | `3747f82bb37c` | 12 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindB-stmtwriter | `a6d470cdf6fb` | 6 | 0 (own outputs only) | 2 | 0 | — | PASS |
| tmp-blindB | `0d450e0b1030` | 12 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindA-stmtwriter | `aa121d2cbfda` | 4 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindA | `2a9989b4c627` | 10 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindConics-stmtwriter | `3c143c0f213c` | 2 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindConics | `32a33cef6e5e` | 10 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindTriSimplex-stmtwriter | `ba6ea9d32a14` | 2 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindTriSimplex | `add7f9966579` | 23 | 0 (own outputs only) | 0 | 0 | head -60; head -60; head -60 | PASS* |
| tmp-blindCaseyFuss-stmtwriter | `5b0b68ee7bc8` | 12 | 0 (own outputs only) | 8 | 0 | — | PASS |
| tmp-blindCaseyFuss | `27edb36c119d` | 10 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindCB-stmtwriter | `e3e8282cb034` | 2 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindCB | `6bbad8b4e222` | 7 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindBaranyai-stmtwriter | `d473edab3376` | 10 | 0 (own outputs only) | 2 | 0 | — | PASS |
| tmp-blindBaranyai | `52ba8d0ff474` | 8 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindPascal-stmtwriter | `a95457a92e97` | 10 | 0 (own outputs only) | 4 | 0 | — | PASS |
| tmp-blindPascal | `06b0b465e1b9` | 7 | 0 (own outputs only) | 0 | 0 | — | PASS |
| tmp-blindPrime-stmtwriter | `42f962dc4ac0` | 29 | 0 (own outputs only) | 16 | 0 | grep -n -i -E "4p ?\+ ?1; head -40; grep -n -i -E "4p ?\+ ?1 | PASS* |
| tmp-blindPrime | `9725f1e465d4` | 10 | 0 (own outputs only) | 0 | 0 | grep -n "abbrev\; grep -n "abbrev\ | PASS* |

\* Manually inspected flags (pattern matches of the automatic scan, all benign):
- tmp-blindD, tmp-blindTriSimplex: the flagged `head -60` reads the writer's own compiler output of its own scratch/Classical files (`… lake env lean …Check.lean | head -60`).
- tmp-blindPrime-stmtwriter: downloaded Dickson, *History of the Theory of Numbers*, vol. I (archive.org public text) and grepped it for "Chebyshev / 4p+1" — a classical source, as permitted for the statement collector.
- tmp-blindPrime: `grep` on its own Classical.lean while editing.
All 21 runs therefore PASS.

Notes. The Paper D writer was the third attempt; two earlier attempts by a different model (gpt-6-astra subagent) were voided because each read a generic procedure file (no paper content) despite instructions. For Paper E the writer was a gpt-6-astra subagent that read the same generic procedure file; that run was kept and is disclosed in Paper E. Transcripts are retained privately; they contain machine paths and are not published.
