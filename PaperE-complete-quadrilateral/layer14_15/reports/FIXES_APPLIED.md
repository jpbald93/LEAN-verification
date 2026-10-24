# Fixes applied — Paper E (L14/L15 version-2 update), review REVIEW_astra_L1415.md (gpt-6-astra)

Date 2026-10-23. Backup: `AFM/PaperE/papere.tex.bak-preastrafix` (byte-identical to the pre-fix file, 42768 bytes).
Edits were exact-substring replacements in Python, with each old string asserted to occur exactly once.
No theorem statement, theorem number, commit macro or `NEWCOMMIT` token was touched (2 `NEWCOMMIT` remain).

Note on inputs: `/tmp/blindE/CLASSICAL_REPORT.md` and the same-folder `L14_REPORT.md` / `L15_COMPARE.md` do not exist.
I used the copies archived under `AFM/PaperE/layer14/` (L14_REPORT_newton.md) and `AFM/PaperE/layer15/`, as the
reviewer did (PAPER_UPDATE_REPORT.md:8–10).

## Issue 1 — root import files claimed unchanged — ACCEPT
Evidence, INTEGRATE_REPORT.md:
- `| QuadNewton.lean (root) | 5cb4e2e86eefa5a8 | 84eeef2f80869211 | changed (+2 import lines) |`
- `| QuadMiquel.lean (root) | 40e264fd0c8b0dd9 | cc62d1b9c00efffc | changed (+2 import lines) |`
- All other old modules show `same`.
- papere.tex:143 counts library files "including the root import file", so the original sentence was false for the roots.

Old (papere.tex:163–164):
> two import lines in each root file, and the extended gate lists and README. All earlier library
> files and statements are unchanged (same SHA-256 hashes), so the source links above remain valid.

New:
> two import lines in each root file, and the extended gate lists and README. Apart from the two root
> import files, all earlier library files are unchanged (same SHA-256 hashes), and all earlier theorem
> statements are unchanged, so the source links above remain valid.

Old (papere.tex:540):
> rejected every planted defect, and the earlier library files are unchanged.

New:
> rejected every planted defect, and the earlier library files other than the root import files are
> unchanged.

(These are the only two "unchanged" claims about library files. The grep found no other occurrence.)

## Issue 2 — perpendicular-witness orthocentre wording — ACCEPT
Evidence, PaperE/layer14/L14_REPORT_newton.md:
- :122 `H1=1+i, H2=2+2i, H3=H4=0`
- :17 `P: 3 distinct, H3 = H4`

So there are three distinct locations in total. "H_3=H_4 and the other three distinct" wrongly suggests three further distinct points besides the coincident pair (four locations).

Old (papere.tex:499–500):
> (in the perpendicular case $H_3=H_4$ and the other three distinct)

New:
> (in the perpendicular case $H_3=H_4$, with $H_1,H_2,H_3$ pairwise distinct)

## Other checks
- Integration (task step 3): INTEGRATE_REPORT.md "Commit step" records the local commits c3a4ce5 (quadnewton) and 4089a97 (quadmiquel), with "Nothing was pushed". The paper already lists all four new files, which matches the report. The `NEWCOMMIT` placeholders stay, as instructed.
- Transcript audit: the review raises no issue about it ("No transcript audit is claimed"), so no edit was needed. BLIND_TRANSCRIPT_AUDIT.md (21/21 PASS) is available if a later edit wants to cite it. Its notes confirm the Paper E writer (gpt-6-astra) read the generic procedure file, and the paper already discloses this.

## Compile
- `pdflatex -interaction=nonstopmode papere.tex`, run twice: rc 0 and rc 0.
- `grep -c undefined papere.log` = 0.
- Output: **12 pages** (411867 bytes).
- `grep -c '\PH{' papere.tex` = 0 (none added).
- Diff against the backup: 12 changed lines (the three replacements only).
