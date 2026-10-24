# FIXES_APPLIED — Paper Conics, review REVIEW_astra_L1415.md (gpt-6-astra)

Date: 2026-10-23. Backup: `AFM/Conics/conics.tex.bak-preastrafix` (made with cp before any edit).
Edits were exact-substring replacements in python (`/tmp/fix_conics.py`); each old string was asserted to occur exactly once.
No theorem statements, theorem numbering, commit macros or NEWCOMMIT tokens were changed (NEWCOMMIT count is 2 before and 2 after).

## Issue 1 — gate coverage overstated (§7.1, P:839–843) — **ACCEPT**
Evidence:
- INTEGRATE_REPORT.md:128: "The L14 files declare more lemmas (dandelin 35, marden 12) than REQUIRED lists (17 and 6, the restatements and witnesses chosen in L14)."
- INTEGRATE_REPORT.md:41: "Not gate-listed: the writer's `def`s (`cone`, `IsDandelinSphere`, `classical_*` …), which are reference statements."
- INTEGRATE_REPORT.md:43/91: "All 158 report `[propext, Classical.choice, Quot.sound]`" / "All 56 report …". These lines are about gate-listed declarations only.
- INTEGRATE_REPORT.md:75,120: root `Dandelin.lean` / `Marden.lean` "changed (+2 import lines)", and every other pre-existing proof file is "same".
- Re-read for check 3: the four files and both commits (8930918, b4fbe75) are integrated. The new text matches the report.

Old:
> Version~2 adds two further checks. Each is a library file in both repositories, listed in full by the gates: \path{Dandelin/L14.lean} and \path{Marden/L14.lean} for Layer~14, and \path{Dandelin/L15Classical.lean} and \path{Marden/L15Classical.lean} for Layer~15 (namespaces \lean{Dandelin.Classical} and \lean{Marden.Classical}). All their declarations depend only on the three standard axioms. The earlier Lean files are unchanged.

New (the reviewer's text, verbatim):
> Version~2 adds a Layer-14 and a Layer-15 library file to each repository: \path{Dandelin/L14.lean}, \path{Marden/L14.lean}, \path{Dandelin/L15Classical.lean} and \path{Marden/L15Classical.lean}. The Layer-15 namespaces are \lean{Dandelin.Classical} and \lean{Marden.Classical}. The gates check selected Layer-14 declarations and the Layer-15 proof declarations, not every declaration in these files. Every gate-listed declaration reports only the three standard axioms. The pre-existing proof modules are unchanged; each root module gains two imports.

I checked that "the Layer-15 proof declarations" is accurate. In the L15 scratch copies, `cov_*`/`l15_*` declarations number 56 (dandelin) and 32 (marden). These equal the added REQUIRED counts at INTEGRATE_REPORT.md:39 ("The 56 added declarations are 8 `cov_*` plus 48 `l15_*`") and :85 ("The 32 added declarations"). The `classical_*` defs, which are not gate-listed, are reference statements, not proofs.

## Issue 2 — "directrix … a line" lacks the non-circular hypothesis (P:948–950) — **ACCEPT**
Evidence:
- /tmp/blindConics/CLASSICAL_REPORT.md:13: "`classical_Conics3_obligation` | well-formedness: if β < π/2 then P ⊓ affineSpan C is a line".
- /tmp/blindConics/CLASSICAL_REPORT.md:59: "the directrix P ∩ P_C is a line when β < π/2".
- L15_scratch/L15_compare_dandelin.lean:118: `(hVP : V ∉ P) (hβ : planeAxisAngle u P < π / 2)` in the obligation.
- conics.tex:403–404: "The hypothesis $m^2<1$ excludes the plane perpendicular to the axis. There the section is a circle and $\ell_d$ is empty."
- The equivalence m²<1 ⇔ β<π/2 follows from the bullet's own `l15_planeAxisAngle` claim, cos β = √(1−m²).

Old: `plane is the directrix $\ell_d$, a line.`
New: `plane is the directrix $\ell_d$, which is a line when $m^2<1$ (equivalently, $\beta<\pi/2$).`

## Issue 3 — unqualified line counts in the abstract (P:71) — **ACCEPT**
Evidence:
- INTEGRATE_REPORT.md:36–37: `Dandelin/L14.lean` | 732, `Dandelin/L15Classical.lean` | 1555. Sum: 2287.
- INTEGRATE_REPORT.md:82–83: `Marden/L14.lean` | 213, `Marden/L15Classical.lean` | 666. Sum: 879.
- PAPER_UPDATE_REPORT.md (Open items): "The Abstract's line counts ("about 2170 and 760 lines") describe the v1 developments … Dandelin adds 732 + 1555 lines and Marden 213 + 666."

Old: `The developments have about 2170 and 760 lines.`
New: `The version-1 developments have about 2170 and 760 lines, respectively; version~2 adds 2287 Dandelin lines and 879 Marden lines in the Layer-14 and Layer-15 files.`

## Issue 4 — wrong theorem number in PAPER_UPDATE_REPORT.md (report only) — **ACCEPT**
Evidence: AFM/Conics/conics.aux:39: `\newlabel{thm:ellipse}{{2}{5}{Dandelin, ellipse}{theorem.2}{}}`. The paper uses the symbolic `\ref{thm:ellipse}`, so the paper is unchanged.

Edit in PAPER_UPDATE_REPORT.md:
Old: ``- `l14_dandelin_ellipse` (Thm 3)``
New: ``- `l14_dandelin_ellipse` (Thm 2)``

## Not changed
- The transcript-audit sentence ("its transcript was audited", P:909–910) was left as written. BLIND_TRANSCRIPT_AUDIT.md (22 Oct) backs it: lines 14–15 give `tmp-blindConics-stmtwriter` and `tmp-blindConics` both as **PASS**. The review raised no issue here.

## Compile
- `pdflatex -interaction=nonstopmode conics.tex` ×2: rc 0, rc 0.
- `grep -c undefined conics.log`: 0.
- Output: **19 pages** (500296 bytes). This is unchanged from the review build.
- `\PH{` count: 0 in the backup, 0 in the new file. None added.
- NEWCOMMIT tokens: 2 before, 2 after.
- No overfull boxes reported in the log.
