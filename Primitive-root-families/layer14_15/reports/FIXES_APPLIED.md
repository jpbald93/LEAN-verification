# FIXES_APPLIED — Paper Prime (prf.tex), response to REVIEW_astra_L1415.md

**Paper:** `AFM/Prime/prf.tex`
**Backup:** `prf.tex.bak-preastrafix` (cp, taken before any edit)

**Method**
- Five exact-substring replacements in `python3 -I`; each old string was asserted to occur exactly once.
- Script: `<oc>/tmp/fixes/Prime/scripts/edit.py`.
- All work was done inline, with no subagents.

**Key evidence change since the review.** `INTEGRATE_REPORT.md` now exists (dated 23 Oct, 09:14). The review was written at 22 Oct 23:19, when the report did not exist. It says:
- L20: "uses namespace `PrimitiveRootFamilies.Classical`"
- L17: `PrimitiveRootFamilies/L15Classical.lean` | 704 lines
- L22: "The writer's definitions and the 26 `classical_*` statements … are **byte-identical**"
- L51: "Gate: `PASS (83 theorems, standard axioms only)`"
- L55: "`ALL TAMPERING TESTS REJECTED`. All six tests were rejected"
- L98–99: "Commit (addendum d), not pushed — SHA: `b4ae30a…`"

So the review's *interim* fix for issue 1 ("pending", namespace `PaperPrimeClassical`) is now out of date. The text was aligned with INTEGRATE_REPORT.md instead.

## Issue 1 (MAJOR): integration and namespace asserted without evidence — PARTIAL

**Verdict.** The concern was valid when the review was written: PAPER_UPDATE_REPORT says "INTEGRATE_REPORT.md was NOT present." The integration has now been done, so the review's "pending / scratch namespace" wording would make the paper less accurate.

**What I did instead**
- Kept the file name and namespace, which INTEGRATE_REPORT.md L17 and L20 now confirm.
- Disclosed the scratch-to-integration path.
- Added the facts the integration report supplies: the line count, the byte-identical statements, the gate count of 83 and the tamper result.
- Kept `NEWCOMMIT`, because commit b4ae30a is "not pushed" (L98).

**Old (§7.1, Layer 15):**
```
theorems depend only on the three standard axioms. They are in
\lean{PrimitiveRootFamilies/L15Classical.lean}, in the namespace
\lean{PrimitiveRootFamilies.Classical}. The outcome for the 26 statements:
```
**New:**
```
theorems depend only on the three standard axioms. The comparison was first checked as a scratch
file; it was then integrated as \lean{PrimitiveRootFamilies/L15Classical.lean} (704 lines), in the
namespace \lean{PrimitiveRootFamilies.Classical}, with the writer's definitions and statements
byte-identical and every proof kept. With both layers the gate passes with
\texttt{PASS (83 theorems, standard axioms only)}, and all six tampering tests are still rejected.
The outcome for the 26 statements:
```
- Evidence for "every proof kept": INTEGRATE L23 "It keeps every proof unchanged" and L32 "Nothing was dropped."
- Note: the integration did change `instance` to `local instance` for six helpers (L30). This is not a proof change, so "every proof kept" stays accurate.

**Old (Limitations):** `audits only the seventeen named theorems; with Layer~14 it audits 53 declarations.`
**New:** `audits only the seventeen named theorems; with Layer~14 it audits 53 declarations, and with Layers~14 and~15 together 83.`
- Evidence: INTEGRATE L36 "REQUIRED count: published 17 → L14 53 → final 83."
- This also closes PAPER_UPDATE_REPORT open item 2.

**Artifact paragraph:** the file names and `NEWCOMMIT` are unchanged. They are confirmed by INTEGRATE L16–17, and the commit has not been pushed. The "unchanged" sentence was edited under Issue 2.

## Issue 2 (MINOR): blanket "files are unchanged" claims are too broad — ACCEPT

**Evidence**
- INTEGRATE L59: "changes: root file +2 import lines, README Layers 14/15 section and counts, gate.sh REQUIRED + chk line".
- INTEGRATE L65, L69, L73: the files marked CHANGED are PrimitiveRootFamilies.lean, README.md and gate.sh.
- INTEGRATE L79: "All the published Lean library files (Chebyshev, SafePrime, General) are unchanged."
- L14_REPORT hash section: the same three files are listed as unchanged.

**Old (Artifact):**
```
\texttt{NEWCOMMIT}. The earlier statements and files are unchanged, and the links in
Table~\ref{tab:thms} still point to commit~\texttt{\commit}.
```
**New:**
```
\texttt{NEWCOMMIT}. The statements and contents of \lean{Chebyshev.lean}, \lean{General.lean} and
\lean{SafePrime.lean} are unchanged; version~2 updates the root import file, the gate's
required-declaration list and the README. The links in
Table~\ref{tab:thms} still point to commit~\texttt{\commit}.
```

**Old (§7.1 intro):** `agents. The earlier library files are unchanged: their hashes were compared before and after.`
**New:**
```
agents. The library files \lean{Chebyshev.lean}, \lean{General.lean} and \lean{SafePrime.lean} are
unchanged: their hashes were compared before and after. Version~2 updates the root import file
and the gate's required-declaration list.
```

**Not mentioned in the text:** the one-line portability change to gate.sh's `mktemp` line (INTEGRATE L45). It is a minor detail. If full precision is wanted, "required-declaration list" could become "required-declaration list and one portability line".

## Issue 3 (MINOR): wrong declaration-to-result mapping for cov_Prime5_reptend — ACCEPT

**Evidence**
- Scratch lean L125–127: `def classical_Prime5_reptend : Prop := ∀ (p : ℕ) (hp : p.Prime) (hq : (4 * p + 1).Prime), IsPrimRootMod (4 * p + 1) 10 ↔ decimalPeriod (1 / ((4 * p + 1 : ℕ) : ℝ)) = 4 * p + 1 - 1`
- L649–650: `lemma decimalPeriod_eq_orderOf (q : ℕ) [Fact q.Prime] (h10 : (10 : ZMod q) ≠ 0) : decimalPeriod (1 / (q : ℝ)) = orderOf (10 : ZMod q)`
- L684: `rw [decimalPeriod_eq_orderOf _ h10]`

**Old:** `\item \lean{cov\_Prime5\_reptend}: the decimal period of $1/q$ equals the order of $10$ modulo $q$.`
**New:**
```
\item \lean{cov\_Prime5\_reptend}: for primes $p$ and $q=4p+1$, $10$ is a primitive root modulo $q$
iff the decimal period of $1/q$ is $q-1$, using \lean{decimalPeriod\_eq\_orderOf}, which proves the
period/order equality for prime $q$ with $q\nmid10$.
```
This is the reviewer's suggested text, verbatim.

## Other checks
- **Transcript audit.** The review raised no issue here, and the paper's sentence "Its transcript was audited" was kept unchanged. It is backed by `AFM/L14L15/BLIND_TRANSCRIPT_AUDIT.md`, row `tmp-blindPrime … PASS*` (flagged item: "`grep` on its own Classical.lean while editing"), and "All 21 runs therefore PASS." No citation was added, because the review did not ask for one. The optional wording "a transcript audit archived with the reports" is available if wanted.
- **Unchanged:**
  - theorem environments and statements (`diff` touches no `\begin{theorem|lemma|corollary|remark}` line);
  - numbering and labels;
  - the `\commit` and `\repo` macros;
  - `NEWCOMMIT`: 2 occurrences before and 2 after.
- **`\PH{`:** 0 occurrences in prf.tex, and 0 in the backup.

## Compile
- `pdflatex -interaction=nonstopmode prf.tex` was run twice: pass 1 rc=0, pass 2 rc=0.
- `grep -c undefined prf.log` = 0, and there are 0 overfull boxes.
- `Output written on prf.pdf (11 pages, 371119 bytes)`: 11 pages, the same as before.

## Remaining open items
- Replace `NEWCOMMIT` with `b4ae30a…` once the commit is pushed; it is currently not pushed (INTEGRATE L98). Act on the L1415-REPIN comment at the same time.
- The author's hand check of the L14/L15 statements is still outstanding; the acknowledgements already disclose this.
- The Dickson p.~196 attribution has still not been checked against the book.

## Round-2 items (applied by orchestrator, 2026-10-23 12:55)
- r2 #1 ACCEPT (evidence L15_COMPARE.md:21 packaging change theorem→def Prop): "copied them verbatim" → "preserved their hypotheses and conclusions, repackaging …"; "byte-identical" now relative to the checked comparison file.
- r2 #2 ACCEPT (evidence INTEGRATE_REPORT.md:21–39, file now imported): "not in the main library" → "absent from the version-1 library and now included in the Layer-15 file". Backup prf.tex.bak-prer2.
