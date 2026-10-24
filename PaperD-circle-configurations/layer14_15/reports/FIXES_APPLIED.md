# Paper D — review fixes applied (review: REVIEW_astra_L1415.md, gpt-6-astra)

Date: 2026-10-23. File: `AFM/PaperD/paperd.tex`. Backup: `paperd.tex.bak-preastrafix`.
Edit script: `<oc>/tmp/fixes/D/edit.py`. It makes 8 exact-substring replacements and asserts each old string occurs exactly once.
Evidence used. `L14_REPORT.md` and `L15_COMPARE.md` are not in `L14L15/D/`. As PAPER_UPDATE_REPORT.md (lines 6–13) records, I used `/tmp/PAPERD_L14_REPORT.md` and `PaperD/layer15/PAPERD_L15_COMPARE.md` instead. There are no `*.lean` scratch copies in the folder. The other sources were INTEGRATE_REPORT.md, `/tmp/blindD/CLASSICAL_REPORT.md`, `/tmp/blindD/brief.txt` and `L14L15/BLIND_TRANSCRIPT_AUDIT.md`.

## Issue 1: source-collection provenance and isolation wording — ACCEPT (1b with a wording change)
**1a: who collected the statements.**
- The review brief says: `ASTRA_REVIEW_BRIEF.md:20`: "textbook statements collected by another agent / by the author for D,E".
- The transcript audit has no `tmp-blindD-stmtwriter` row; Paper D has only the writer run `tmp-blindD`. Paper D therefore had no statement-collector agent.
- old: `A second agent collected textbook statements`
- new: `The author collected textbook statements`

**1b: what the writer read.**
- CLASSICAL_REPORT.md:63–65: "/tmp/blindD/brief.txt was not opened as a file; its content was given in the prompt. / Only my own files: …Classical.lean, …scratch/Check.lean (a #check probe…), …scratch/out.txt (compiler output). / No other files were read…, and no web search was done."
- BLIND_TRANSCRIPT_AUDIT.md: row `tmp-blindD` reads "0 (own outputs only) | 0 | 0 | head -60; head -60 | PASS*". The footnote says the `head -60` calls read "the writer's own compiler output".
- Per the task, I cite the transcript audit as archived with the reports instead of weakening the claim.
- old: `and the accepted run read nothing but its brief (its transcript was\naudited).`
- new: `and the accepted run received the statements in its prompt and otherwise\naccessed only its own generated statements, Mathlib probes and compiler output (a transcript audit\narchived with the reports found no other file read and no web access).`

## Issue 2: abstract overstates witness coverage — ACCEPT
- L14 report, Summary: "(B) Witnesses: all of the above except `clifford_three`".
- L14 report: "Not restated: `not_cliffordChain_of_six_le`, `cliffordChain_iff`".
- old: `Version~2 adds Mathlib-only restatements of the\nmain theorems with explicit witnesses, and`
- new: `Version~2 adds twelve Mathlib-only restatements of the\nmain theorems, eleven with explicit witnesses (the Clifford $n=6$ witness and a restatement of the\ngeneral-$n$ classification remain open), and`

## Issue 3: blanket "no extra hypothesis" hides the Clifford n=6 strengthening — PARTIAL
- L14 report, clifford_three row: "The library hypotheses m₁…m₆ … are stated for **every** point satisfying the defining property … This is stronger than the library's hypothesis about the explicit `cliffordPoint`; the two are equivalent because the Clifford point is unique, but that is not proved here."
- Why only partial: the reviewer's text would repeat "The witness remains open", which the same paragraph already states ("The exception is Theorem~\ref{thm:cliff6} …"). I added only the missing qualification.
- old: `No\nrestatement was false or needed an extra hypothesis.`
- new: `No\nrestatement was found false. Apart from the Clifford $n=6$ restatement, whose universally quantified\nnon-collinearity hypotheses are stronger than the library's (equivalent to them given uniqueness of the\nClifford point, which is not formalized), none needed a hypothesis beyond the library theorem's.`

## Issue 4: writer-added hypotheses for Clifford n=5 not disclosed — ACCEPT
- CLASSICAL_REPORT.md:44: "D1_b `hXu`, D1_c `hXu` (EXTRA): the Clifford point of each four circles is unique".
- CLASSICAL_REPORT.md:45: "D1_b `hnc` … (EXTRA + AMBIGUOUS): the points are not collinear, so the result is 'one circle'".
- PAPERD_L15_COMPARE.md, row D1_b: "writer uniqueness identifies all five supplied X; writer noncollinearity removes line branch."
- old: `\decl{Blundon.Classical.cov_D6_upper}, \decl{SteinerLehmus.Classical.cov_D7}). Not covered:`
- new: `… \decl{SteinerLehmus.Classical.cov_D7}). For Clifford $n=5$ the\nwriter additionally assumes that each four-circle common point is unique and that the five points are\nnot collinear; these assumptions identify the supplied points with ours and remove the line alternative.\nNot covered:`

## Issue 5: local or unpushed commits and the root-file exception — ACCEPT (5b worded slightly differently)
Evidence from INTEGRATE_REPORT.md:
- line 4: "**One local commit per repo, NOT pushed.**"
- line 41 (commit step): "one commit per repo … **Not pushed.**"
- line 66, and the same in every repo: "root: +2 import lines (L14, L15Classical) only". All other pre-existing `.lean` files are "unchanged".

Edits:
- **5a**
  - old: `\emph{Version~2.} Each repository has one new commit that adds`
  - new: `\emph{Version~2.} Each repository has one new local commit, not yet pushed, that adds`
- **5b.** The sentence already begins "All other library files", i.e. other than the root and new files, which the previous sentence lists. The only false part was "every statement … cited in this paper", because that includes the new declarations. I narrowed it to statements cited from those files.
  - old: `All other library files, and\nevery statement and source line cited in this paper, are unchanged;`
  - new: `All other library files, and\nthe statements and source lines cited from them, are unchanged;`
- **5c**
  - old: `No earlier library file changed.`
  - new: `No pre-existing library file changed except the root file, which gained the two import lines.`

The NEWCOMMIT tokens are untouched: 9 occurrences before and after (8 in the availability text, 1 in the REPIN comment).

## Checks
- `pdflatex` run twice: rc 0 both times.
- `grep -ci undefined paperd.log` gives 0.
- **Pages:** 19, unchanged ("Output written on paperd.pdf (19 pages, 460333 bytes)").
- `\PH{` count: 0 before and 0 after, so none added.
- Theorem environments and labels: identical to the backup (diffed).
- `commitof` macros: identical (diffed).
- Overfull boxes: the only one is the existing Theorem 5 header box (lines 324–325), which was not touched.
- Diff against the backup: 27 changed lines, all in the abstract, the Version-2 paragraph and §sec:l1415.
