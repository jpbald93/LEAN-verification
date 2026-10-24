# FIXES APPLIED — Paper Baranyai (review by gpt-6-astra, REVIEW_astra_L1415.md)

Date: 2026-10-23. All work was done inline; no subagents were used.
- **Backup:** `AFM/Baranyai/baranyai.tex.bak-preastrafix`, made before any edit.
- **Edit method:** a Python exact-substring replacement. Each old string was asserted to occur exactly once.
- **Not changed:** theorem statements, theorem numbering and commit macros. The 3 NEWCOMMIT occurrences (l.31, 145, 628) are kept.
- **Integration status:** INTEGRATE_REPORT.md was re-read. Both new files and the root/gate/README changes are recorded there, so no text had to be adjusted for a missing integration.

## Issue 1: definition inventory omits the Prop wrapper. Verdict: **PARTIAL**
- **Evidence for the omission:**
  - I:26: "It is kept as `def classical_Baranyai3_main : Prop := …` … only the theorem-to-Prop wrapper was added."
  - I:41: "the 4 writer definitions, 7 bridges, 8 cov, 7 classical theorems and the `classical_Baranyai3_main` Prop."
- **Correction to the reviewer's text:** the reviewer kept "one bridge definition", but the evidence shows **two** bridge `def`s.
  - L15_compare.lean l.34: `def classesOf …`
  - L15_compare.lean l.78: `def toFinpartition …`
  - I:33 lists both among the 7 bridges. The other five bridges are `lemma`s.
  - So the old "one bridge definition", which came from PAPER_UPDATE_REPORT edit 7, was already wrong. It is corrected here.
- **Old:** `of version~2 adds the writer's four definitions and one bridge definition.)`
- **New:** `of version~2 adds the writer's four definitions, two bridge definitions, and a proposition-valued definition recording the unproved general almost-regular statement.)`
- **Effect on the total:** none. The count is still 76.

## Issue 2: overbroad "All checks below" / "earlier files … unchanged". Verdict: **ACCEPT**
- **Evidence:**
  - I:62–64: "Baranyai.lean (root) | … | +2 import lines"; "gate.sh | … | REQUIRED line + mktemp line"; "README.md | … | count 32→76 (3 places) + new section".
  - I:57–60: Basic/Partition/Transport/tests/tamper.sh are unchanged.
  - I:45–49: the gate and tamper runs were on the new commit.
- **Fix (a):**
  - Old: `All checks below were run on commit \texttt{\shortcommit}.`
  - New: `Except for the version-2 checks explicitly identified below, the checks in this section were run on commit \texttt{\shortcommit}.`
- **Fix (b):**
  - Old: `the earlier files and statements are unchanged`
  - New: `the three original library source files and their statements, together with the tampering script, are unchanged`
  - The hash parenthesis that follows already names exactly those 4 files.
- NEWCOMMIT and the old source-link pin are kept.

## Issue 3: "the names of that section are declared only in the new commit". Verdict: **ACCEPT**
- **Evidence:**
  - PAPER_UPDATE_REPORT D6: "`namegate.sh` passes on every pre-existing name. It reports 15 MISSING, all of them new L14/L15 names".
  - Paper l.637–639 cites the old names `baranyai`, `Baranyai.baranyai_partition` and others inside sec:l1415.
- **Old:** `the names of that section are declared only in the new commit`
- **New:** `the 15 newly introduced declaration names cited in that section are declared only in the new commit`

## Issue 4: Table 1 "lists every informal statement of this paper". Verdict: **ACCEPT**
- **Evidence:**
  - Table 1 ends before §5. Section sec:l1415 discusses further statements, for example `cov_Baranyai3_a_implication` (NEW PROOF) and the unproved `classical_Baranyai3_main` (L15:17–20; I:26–32).
- **Old:** `Table~\ref{tab:thms} lists every informal statement of this paper with its formal counterpart.`
- **New:** `Table~\ref{tab:thms} lists the original development's informal statements with their formal counterparts; Section~\ref{sec:l1415} identifies the additional verification statements.`

## Compile
- `pdflatex -interaction=nonstopmode baranyai.tex`, run twice: **rc 0 and rc 0**.
- `grep -c undefined baranyai.log`: **0**.
- Output: **15 pages** (unchanged).
- `grep -c '\PH{'`: **0** in both the new file and the backup, so none was added.
- The theorem/lemma/definition `\begin` lines are identical to the backup (same md5).
- `diff` against the backup shows only the 5 prose replacements above.

## Not changed / open
- NEWCOMMIT remains a placeholder. The integration commit `1ab2162` is local and unpushed (I:74–78), so repinning and rerunning the name gate against the new commit are still open.
- The review asked for no change to the transcript-audit wording. It was not touched.
