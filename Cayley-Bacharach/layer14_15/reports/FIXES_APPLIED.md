# Paper CB — fixes applied for REVIEW_astra_L1415.md (2026-10-23)

Paper: `AFM/CayleyBacharach/cayley_bacharach.tex`. Backup: `cayley_bacharach.tex.bak-preastrafix` (taken before any edit).
Edits: `python3 -I <oc>/tmp/fixes/CB/apply.py`. It made 11 exact-substring replacements and asserted that each old string occurred exactly once.
All work was inline, with no subagents. I did not change any theorem statement, theorem numbering, `\commit`/`\shortcommit` macro, or label. There are still 3 `NEWCOMMIT` occurrences, the same number as before the edits.

## Issue 1 — gate inventory overstated → ACCEPT
Evidence:
- L14_REPORT.md:47: "…is `toP E c` … (`eq_toP` plus explicit surjectivity …)". `eq_toP` is not in the REQUIRED list (L14_REPORT.md:101–102).
- INTEGRATE_REPORT.md:26–27 lists 17 `cov_*` declarations and 24 NEW PROOF declarations (41 in all). The comparison proofs section of L15_compare.lean (lines 915–1630) declares 59 theorems. Supporting lemmas such as `l15_li`, `l15_meet` and `l15_cb` are not gated.

Change:
- old: `Every theorem and lemma in\nthem is listed in \path{gate.sh}`
- new: `The gate explicitly lists 27 Layer-14\ndeclarations and 41 Layer-15 declarations in \path{gate.sh}`

The total "(100 earlier, 27 from Layer~14, 41 from Layer~15)" = 168 is unchanged.

## Issue 2 — "Fulton's multiplicity version" lacks the semantic caveat → ACCEPT
Evidence: L15_COMPARE.md:24: "I did not check the writer's claim that `intMult` equals Fulton's multiplicity. Only the support lemma `l15_intMult_ne_zero_iff` is proved."

Changes:
1. After the `l15_intMult_ne_zero_iff` item:
   - old: `nonzero if and only if both forms vanish there.\n\end{itemize}`
   - new: `nonzero if and only if both forms vanish there. The comparer did not verify that this definition agrees with Fulton's local intersection multiplicity; only its support equivalence was proved.\n\end{itemize}`
2. Narrower list:
   - old: `\item Fulton's multiplicity version, with simple points`
   - new: `\item The writer's proposed encoding of Fulton's multiplicity version, with simple points`
3. Limitations, Multiplicities:
   - old: `distinct points of Fulton's multiplicity version (Section`
   - new: `distinct points of the writer's proposed encoding of Fulton's multiplicity version (Section`

## Issue 3 — unqualified zero-warning / "all 99 cited" narrative → PARTIAL
Evidence:
- PAPER_UPDATE_REPORT.md:68: the paper now checks 137 names, 38 of them new.
- INTEGRATE_REPORT.md:9 and :70: `scratch/PaperAxioms.lean` and `paper_axioms.out` are unchanged.
- INTEGRATE_REPORT.md:76: "the paper run covers the 99 paper declarations while the gate checks more".
- L15_COMPARE.md:53: "The 233 warnings are all linter warnings". This refers to the scratch file. INTEGRATE_REPORT.md:31 records the final build only as "rc 0, Build completed successfully" and gives no warning count.

Changes:
- old: `A full \lean{lake build} finishes with 0 errors and 0 warnings.`
  new: `At the published commit, a full \lean{lake build} finishes with 0 errors and 0 warnings.`
- old: `On the final sources, a single scratch file`
  new: `On the published-commit sources, a single scratch file`
- old: `on all 99 declarations cited in this paper and one`
  new: `on the 99 declarations cited in the paper before version~5 and one`

Why PARTIAL: the reviewer proposed "version 4 of this paper". PAPER_UPDATE_REPORT.md:74 (open item 4) says the "version 5" label has not been confirmed, so I avoided naming a previous version number. The new wording ties the claim to the paper as it stood before version 5, which is the label the paper itself uses ("Version~5 adds…").

## Issue 4 — "copied verbatim … either proved it from the library or classified it" → ACCEPT
Evidence:
- L15_COMPARE.md:12: "Each `theorem classical_X … := by sorry` became `def classical_X : Prop := ∀ <same binders>, <same conclusion>` (a mechanical Python rewrite …)".
- L15_COMPARE.md:37–42: "NEW PROOFS".
- INTEGRATE_REPORT.md:19–20: the definitions and Prop defs were carried over verbatim from the scratch file.

Changes:
- old: `A comparer\ncopied each statement verbatim and either proved it from the library, with no change to the library\nfiles, or classified it.`
  new: `A comparer\npreserved every binder and conclusion, mechanically rewriting each theorem with a placeholder proof\nas a Prop-valued definition. It proved coverage by library derivations or new proofs, or recorded a\nnarrower or out-of-scope result, without changing the existing library files.`
- old: `with the writer's definitions and statements\nreproduced verbatim, in`
  new: `with the writer's definitions and mechanically\nrewritten statement definitions preserved from the comparison file, in`

The new wording avoids the word `sorry`, so the token grep is unaffected. "Without changing the existing library files" is backed by L15_COMPARE.md:65 (library hash unchanged) and INTEGRATE_REPORT.md:46–70.

## Issue 5 — "none is false as written" upgraded from "none found" → ACCEPT
Evidence:
- L15_COMPARE.md:35: "**No classical statement was found false.**"
- L15_COMPARE.md:24: "I did not search for a counterexample".
- L15_COMPARE.md:50: "Open: CB2(b) (alg. closed form), the general multiplicity case of CB1(b), and uniqueness in CB2(b)-distinct."

Changes:
- old: `and none\nis \emph{false as written}.`
  new: `and none\nwas classified as \emph{false as written}.`
- old: `\emph{Writer statements false as written}: none.`
  new: `\emph{Writer statements found false as written}: none; this does not establish the truth of the\nunproved statements.`

## Not changed
- The sentence "Its transcript and self-reported file list were audited" is supported by BLIND_TRANSCRIPT_AUDIT.md:20–21 (tmp-blindCB-stmtwriter and tmp-blindCB both PASS). The review did not raise this issue, so the sentence was left as it is.
- Integration text: I re-read INTEGRATE_REPORT.md. The 168 gate count, BSD gate PASS, GNU-only tamper.sh and unpushed commit d9c674c all match the existing text, so nothing needed adjusting.

## Compile
- `pdflatex -interaction=nonstopmode` was run twice. Both runs gave rc 0.
- `grep -c undefined cayley_bacharach.log` = 0. There are 0 `!` errors and 0 overfull boxes.
- **18 pages.** The previous build had 17; the added caveat text pushed it onto an 18th page.
- `\PH{` occurrences: 0 in both the backup and the new file, so none was added.
- The count of theorem/lemma/proposition/example/corollary environments is the same in the backup and the new file.
