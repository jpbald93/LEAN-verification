# Paper C — fixes applied for REVIEW_astra_L1415.md

Date: 2026-10-23. Done inline. Backup: `AFM/PaperC/paperc.tex.bak-preastrafix` (byte-identical to the pre-fix file, 54507 bytes).
Edits were made with a Python script that asserts each old string occurs exactly once (`<oc>/tmp/fixes/C/scripts/apply.py`, plus one follow-up wording edit for issue 3).
No theorem statement, theorem/label numbering, `\src`/commit macro or `NEWCOMMIT` token was touched.

## Issue 1 — Reuleaux boundary identification overclaimed — **ACCEPT** (reworded to stay close to the evidence)
Evidence: L15_COMPARE.md:36 "missing: the frontier = union of the three arcs (set equality on the writer's `⋂ closedBall`) … no theorem links the repo's γ_{R_w} to the writer's `⋂ closedBall A w ∩ …`"; :38 "missing: identification `E '' K_{R_w}` (or range γ_{R_w}) with the writer's `reuleauxTriangle A B C w` / its frontier". Paper (d)/(e) (P:270–273) state only pairwise distances and |γ(θ)−γ(0)|=w on [5π/6,7π/6].
- OLD: `Parts (d) and (e) identify the curve with the boundary of a Reuleaux triangle: (d) gives an equilateral triangle of side $w$, and (e) says one side is an arc of radius $w$ about the opposite corner (the other two follow by the $2\pi/3$-periodicity of $R_w$).`
- NEW: `Parts (d) and (e) establish an equilateral triple of points of side $w$ on the curve and, on one parameter interval, that the curve lies at distance $w$ from the opposite point (rotated counterparts follow by the $2\pi/3$-periodicity of $R_w$); they do not establish that the trace of the curve equals the boundary of the intersection of the three discs.`
- The following sentence ("We do not prove that the body of $R_w$ … area") is kept, as the review asks.

## Issue 2 — C² four-vertex hypotheses conflated with do Carmo's C³ variant — **ACCEPT** (wording slightly adjusted)
Evidence: L15_COMPARE.md:42 "For C³ 2π-periodic h with ρ>0, α = E∘γ_h satisfies **all** hypotheses of `classical_C3_a` … **and** its conclusion (4 increasing vertices in [0,2π))"; :44 "four increasing zeros of `deriv (signedCurvature α)` in [0,2π) … ContDiff ℝ 3 α was not proved (it needs h ∈ C⁴); the statement is the conclusion for α = E∘γ_h." Constant width: :34 "For `PiecewiseConstWidth h w`, `w>0`: `E '' K_h` … `HasConstantWidth (E '' K_h) w` (writer's notion …)".
- OLD (P:672–675): `For curves given by support functions these statements hold in the writer's sense: for $\gamma_h$ the writer's hypotheses of the four-vertex theorem hold and its conclusion (four increasing vertices in $[0,2\pi)$) is proved, and $K_h$ has constant width in the writer's sense.`
- NEW: `For $C^3$ $2\pi$-periodic support functions with $\rho>0$, the transported curve $\gamma_h$ satisfies the writer's hypotheses of the $C^2$ four-vertex statement, and its conclusion (four increasing vertices in $[0,2\pi)$) is proved. For do~Carmo's variant only the conclusion (four increasing stationary points of the curvature in $[0,2\pi)$) is proved; $C^3$ regularity of the curve is not established. For a piecewise constant-width support function of width $w>0$, $K_h$ has constant width $w$ in the writer's sense.`
  (The reviewer's "under the stated width hypotheses" is made concrete from L15_COMPARE.md:34.)
- OLD (P:712): `covers strictly convex $C^3$ curves given by $C^3$ support functions` → NEW: `covers strictly convex curves given by $C^3$ support functions`. Thm `fvtextbook` (P:463) itself only assumes h ∈ C³, ρ>0; the curve's C³ regularity is not stated there.

## Issue 3 — "its transcript was audited" lacks audit evidence — **PARTIAL** (reviewer's alternative taken: supply the audit, keep the claim)
Evidence: the review was right that PAPER_UPDATE_REPORT.md:64 found "no separate audit report file" at the time. That report now exists: `AFM/L14L15/BLIND_TRANSCRIPT_AUDIT.md` (generated 2026-10-22 18:35, after the review), row `| tmp-blindC | 3747f82bb37c | 12 | 0 (own outputs only) | 0 | 0 | — | PASS |`, with pass criterion "no read of any file except its own brief/outputs and its own compiler output; no web access", and "All 21 runs therefore PASS." It agrees with /tmp/blindC/CLASSICAL_REPORT.md "Files read". So the claim is kept rather than weakened, as the brief allows, and a citation of the audit is added.
- OLD: `separated two well-formedness obligations; its transcript was audited.`
- NEW: `separated two well-formedness obligations; its transcript was audited (a transcript audit archived with the reports found no read of any file other than the writer's own brief, outputs and compiler output, and no web access).`
- Not changed: "A writer model, given only these statements and no code or paper". The audit backs it.

## Issue 4 — "earlier … Lean files are unchanged; only root imports/gate lists" — **ACCEPT**
Evidence: INTEGRATE_REPORT.md:7 "`scratch/` removed"; :100 "`scratch/Ax.lean` is tracked in the published repos … ` D scratch/Ax.lean`"; Commit step :125/:140 "Committed changes: M Barbier.lean, A …L14.lean, A …L15Classical.lean, M README.md, M gate.sh, D scratch/Ax.lean"; :48/:87 README "Layers 14 and 15" section added; hash tables :35–46, :75–82 all "same".
- OLD: `The earlier statements and Lean files are unchanged (checked by hash); only the root import files gain the imports of the new files, and the gate lists gain the new declarations.`
- NEW: `The pre-existing library modules and their statements are unchanged (checked by hash); the root import files and gate lists are extended, the READMEs are updated, and the tracked \lean{scratch/Ax.lean} files are removed.`
- P:697 "The earlier library files are byte-identical" is left as is (the reviewer agrees it is supported).

## Issue 5 — finite disc-intersection hypotheses missing — **ACCEPT**
Evidence: L15_scratch/L15_compare_barbier.lean:301–303 (identical in L15_compare_fourvertex.lean:301–303): `theorem isPlaneConvexBody_iInter {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → Plane) (w : ℝ) (hw : 0 < w) (hd : ∀ i j, dist (v i) (v j) ≤ w)`. INTEGRATE_REPORT.md:10 says the integrated file is byte-identical to the scratch writer block, and the comparison section follows it.
- OLD: `that an intersection of finitely many closed discs of radius $w$ about points pairwise at distance at most $w$`
- NEW: `that an intersection of a nonempty finite family of closed discs of common radius $w>0$ about points pairwise at distance at most $w$`

## Missing-integration check (step 3)
INTEGRATE_REPORT.md was re-read, including the Commit step. Both repos are committed locally (barbier `0dd68bd…`, fourvertex `8f2ae82…`), but nothing is pushed. The paper's file names, line counts (290/578/138/727) and gate counts (96/66) match it. The `NEWCOMMIT` tokens are kept, as instructed (2 occurrences).

## Compile
- `pdflatex -interaction=nonstopmode paperc.tex` run twice: rc=0, rc=0.
- `grep -c undefined paperc.log` = 0; 0 Overfull boxes.
- **Pages: 14** ("Output written on paperc.pdf (14 pages, 475050 bytes)"), unchanged.
- `\PH{` count: 0 before, 0 after. `NEWCOMMIT`: 2.
- diff backup→new: 32 changed lines, all inside the 6 edit sites above.
