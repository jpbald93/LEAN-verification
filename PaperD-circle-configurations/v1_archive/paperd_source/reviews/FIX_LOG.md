# Response to Astra layer-12 review (REVIEW_astra_d.md) — applied 2026-10-13

Each Astra finding was checked by the author's assistant before being applied; the edits are in
astra_changes.diff (paperd.tex.bak-preastra -> paperd.tex).

Independent checks made before applying:
- M3 (Lester): Astra's 120° isosceles counterexample A=(0,1/√3),B=(-1,0),C=(1,0) re-computed: N=A=F1, F2=O (incidences exact to 2e-16). Separately computed that generic isosceles triangles A=(0,h), h in {0.3,0.5,1,2.5} give FOUR DISTINCT collinear points (min separation 0.048..0.33) -> not concyclic. So the scalene hypothesis cannot be weakened to "not equilateral", but the old universal sentence was false.
- M4 (Kosnita): Astra's boundary example O=0, A=(1,0), B,C=(1/2,±√3/2) re-computed: all equidistances exact, sum of squared sides = 5 = 5R², Oa = A, BOb and COc both the line x=1/2. NOTE: Astra did not say, and the paper now says, this triangle is isosceles with a 120° angle at A (sides 1, √3, 1), not equilateral.
- M7: "no mutants generated" lists confirmed in every battery report.
- M8: satisfiability breakdown re-derived from reports: with-hypotheses 49, hypothesis-free 136, closed 11 (sum 196 ✓).
- M5: verify_john.md line 50 confirms 999/1000; Blundon/Steiner–Lehmus indeed have no numeric re-check.
- M6: per-file SHA-256 manifest taken on john (all 8 repos, same Lean v4.33.1, same Mathlib 0df444a360ea); jack gate/tamper/hash run for all 8 launched (receipt table is still a placeholder until it finishes).
- Numeric scripts: the re-verification agents wrote their scripts to /tmp on jack/john; those directories no longer exist. Disclosed in the paper (placeholder asks Josh whether to re-run with archived scripts).

Not applied / deferred:
- M6 receipt table: placeholder until jack's gate/hash run is in.
- M10 linter/ablation for clifford: placeholders until jack's battery finishes.
- m7 "Lester found the theorem by computer": wording removed (unsourced).

## Round 3 (REVIEW_opus_d3.md, MINOR REVISION, 0/2/8) — applied 2026-10-14
- MAJOR blind framing: cp gap now called a real underspecification of our prose, not a redaction artefact; "no difference" qualified.
- MAJOR unsourced 5000-config numeric (and wrong test for uniqueness): REMOVED.
- MINOR tool log: transcript + tool-call list archived (layer13/writer_transcript.jsonl, writer_tool_calls.txt); Mathlib probe mentioned. Recompile log archived (layer13/L13_recompile_jack.log). SHA256SUMS.
- MINOR chainfail: kernel scope stated precisely (9 level-4 points, 3 lines); 1-based numbering (omit 5 -> Re z=4, omit 6 -> Im z=-4, omit 1); cites Classify:57/167; "together settle the predicate"; cliff6-unaffected sentence marked as argument.
- MINOR abstract/intro/contributions updated with the n>=6 result.
