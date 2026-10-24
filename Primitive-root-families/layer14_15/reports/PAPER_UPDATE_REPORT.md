# PAPER_UPDATE_REPORT — Paper Prime (prf.tex), Layers 14 and 15

**Paper:** `<ws>/AFM/Prime/prf.tex`
**Backup:** `prf.tex.bak-prel1415` (cp, taken before any edit)

**Inputs**
- L14_REPORT.md
- L15_COMPARE.md
- /tmp/blindPrime/CLASSICAL_REPORT.md
- classical_statements.txt
- statements_sources.md

**INTEGRATE_REPORT.md was NOT present.** File names and the namespace therefore come from the brief:
- `PrimitiveRootFamilies/L14.lean` (this name is confirmed by L14_REPORT)
- `PrimitiveRootFamilies/L15Classical.lean`
- namespace `PrimitiveRootFamilies.Classical`

**Method:** all edits were exact-substring replacements in python (`python3 -I`, each old string asserted to occur once). Script: `<oc>/tmp/paperupd/Prime/scripts/edit.py`, plus two small follow-up patches. All work was done inline, with no subagents.

## Edits (old -> new)
1. **Preamble, before `\newcommand{\repo}`:** (none) -> `% L1415-REPIN: \commit (e30457a; used by \src) stays for the version-1 files; add the version-2 hash at each NEWCOMMIT in the Artifact paragraph`. The `\commit` macro and its hash are unchanged.
2. **`\date`:** `27 September 2026` -> the same date plus the line "Version 2 adds the Layer-14 and Layer-15 checks (Section~\ref{sec:l1415})".
3. **Abstract end:** "…tampered versions of the source." -> the same, plus a 3-sentence version-2 note:
   - L14: all 17 theorems are restated with Mathlib-only types and have witnesses.
   - L15: the blind writer's 26 statements were compared.
   - The general Wertheim criterion as transcribed is false; a corrected form is proved.
4. **Contributions:** new last bullet "(Version 2) restatement of all seventeen theorems … comparison with independently written classical statements (Sec. l1415)".
5. **Artifact paragraph:** added that version 2 adds `PrimitiveRootFamilies/L14.lean` and `PrimitiveRootFamilies/L15Classical.lean` in a new commit `NEWCOMMIT`, that the earlier statements and files are unchanged, and that the Table 1 links still point to `\commit`.
6. **§5, after "the case k=2 does not … composite.":** added "The Layer-15 file of version 2 covers p=5 and the textbook form with a≢−1 in place of a²≢1".
7. **§5, before "The criterion turns a primitive-root question…":** new paragraph:
   - Thm 12 (`thm:gen`) is the case p−1=2^kℓ of the criterion Dickson attributes to Wertheim (Dickson Vol. I p. 196), plus its converse.
   - As summarised there, the general form for 2^kℓ^j is false when j≥2 (refers to Sec. l1415).
8. **§7, new `\subsection{Layers 14 and 15}\label{sec:l1415}`**, placed before "Limitations". It has three paragraphs.
   - **Intro:** both layers were done by AI agents; the library hashes are unchanged.
   - **Layer 14:**
     - L14.lean (376 lines) restates 17/17 theorems; none was omitted.
     - Bridges: `Nat.Prime`, `orderOf`, `jacobiSym`. The namespace check found 0/36 hits.
     - Witnesses: both truth values for each ↔; a=3 mod 41 and a=5 mod 13 show the a^{2^k} condition is needed; `IsLeast` is realised at 23 ↦ 5; p=89, and 3 is not a primitive root mod 41.
     - No restatement was false and none needed an extra hypothesis.
     - The gate passes with 53 theorems and the tamper tests are OK. It also records the `wrap` tamper-test fragility and the fix (the restated Cor 4 is derived from Thm 3).
   - **Layer 15:**
     - Process: the statements were collected with citations; the writer was blind and its transcript audited; 26 statements, 2 of them obligations; copied verbatim; no hypothesis added; the library unchanged; 28 theorems on the standard axioms; the file and namespace are named.
     - Counts: covered 8, narrower 1, out of scope 16, writer statement false as written 1, each listed.
     - Every new proof is listed.
9. **Limitations:** "it audits only the seventeen named theorems." -> "At commit \commit it audits only the seventeen named theorems; with Layer 14 it audits 53 declarations."
10. **Limitations:** "does not compare theorem statements against a trusted specification: …" -> the same, plus "Layer 15 compares them with independently written classical statements, but that comparison was done by AI agents."
11. **Conclusion:** "Natural extensions are primes p with p−1=2^kℓ^j … adds a condition," -> the same, then:
    - "The sufficient direction for 2^kℓ^j, with condition a^{2^kℓ^{j−1}}≢1, is proved in the Layer-15 file; the converse and further prime factors remain."
    - "Other extensions are …" (the cubic-reciprocity and Table 2 items, unchanged).
12. **Acknowledgements:** added "The Layer-14 and Layer-15 checks of version 2 (Sec. l1415) were carried out entirely by AI agents."
13. **Bibliography:** new `\bibitem{Dickson}`, Dickson, *History of the Theory of Numbers* Vol. I (1919). It backs the attribution to Wertheim and comes from statements_sources.md.
14. **Follow-up patches:**
    - In edit 7, "is false as usually summarised" -> "As summarised there, … false when j≥2".
    - In the Layer-15 paragraph, "Its own log records…" -> "Its transcript was audited, and its report records that it opened no other file".
    - The Layer-14 paragraph is wrapped in `sloppypar` to remove a 19.7pt overfull hbox.

## Layer-15 classification used (26 statements; source: L15_COMPARE table)
- **Covered (8):** Prime4, Prime5_a, Prime5_b, Prime5_iff, Prime5_examples, Prime5_note, Prime6, Prime6_obligation.
- **Narrower (1):** Prime3_b.
  - The repository has it only for ℓ≠2 and with a²≢1.
  - p=5 and the a≢−1 form were missing.
  - New proof `cov_Prime3_b` closes both.
- **Out of scope / background, all proved (16):** Prime1_a/b/c, Prime2_a–d, Prime3_a, the two Prime3_b remarks, Prime5_reptend, Prime6_examples, Prime6_a, Prime6_a_obligation, Prime6_b, Prime6_b_aux.
- **Writer statement false as written (1):** Prime3_c, Wertheim with l≥1.
  - Counterexample p=19, a=8 (order 6).
  - The fault is in the source/textbook statement.
  - The paper's l=1 case is correct.
  - `new_Prime3_c_corrected` is proved.
- **Note on the comparer's own labels:** L15_COMPARE's summary line "E: 10" counts Prime3_b and Prime3_c_part (an auxiliary theorem, not one of the 26). In the paper, Prime3_b is counted as narrower and Prime3_c as false, so 8+1+16+1 = 26.

## Discrepancies fixed
1. **The paper said the gate "audits only the seventeen named theorems".** That is outdated with L14, where the gate passes with 53 declarations (L14_REPORT). It is now qualified per commit.
2. **The limitations said there is no comparison with any specification.** That is now partly superseded: L15 is an AI-only comparison. Added this and kept the human-reading caveat.
3. **§5 said the k=1 bridge omits p=5, with no further remark.** L15 proves the full safe-prime criterion, including p=5 (`cov_Prime3_b`). Added a pointer.
4. **The conclusion listed p−1=2^kℓ^j as open.** L15 proves the corrected sufficient direction (`new_Prime3_c_corrected`). Narrowed to "the converse and further prime factors remain".
5. **The literature's general Wertheim form is false for l≥2, but the paper did not mention it.** The paper's Theorem 12 relates to it, so §5 now attributes Theorem 12 correctly and warns, citing Dickson.
6. **The acknowledgements implied that all checking was AI review plus the author's hand-check.** Added that L14/L15 were done entirely by AI agents.
7. **Nothing in the abstract, contributions or "not claimed" text was contradicted:**
   - No L14 restatement failed.
   - Every paper claim about its own results is covered (Chebyshev both directions, RM plus existence, 2 mod 4ℓ+1).
   - The paper has no explicit "what is not claimed" section.
   - The novelty disclaimers (converse = folklore; families: no novelty claim) are consistent with the findings and were left unchanged.

## Pins
- `\commit{e30457a}` and `\repo` are unchanged.
- The `% L1415-REPIN:` comment is placed directly above the pin definitions.
- The literal token `NEWCOMMIT` appears once, in the Artifact paragraph.

## Compile
- pdflatex was run twice: rc=0, 0 undefined references or citations, 0 overfull boxes.
- **Pages:** before 9, after 11.
- **Theorem numbering:** unchanged. The `\newlabel` numbers of all pre-existing labels are identical to those of the backup's compile (diff empty). The only new label is `sec:l1415` (subsection 7.1).

## Open items
1. **INTEGRATE_REPORT.md is missing.** Confirm the final names `PrimitiveRootFamilies/L15Classical.lean` and namespace `PrimitiveRootFamilies.Classical`:
   - The comparer's scratch file used `namespace PaperPrimeClassical`, with names `cov_*`, `not_classical_Prime3_c` and `new_Prime3_c_corrected`.
   - If integration renames these, update the subsection.
2. **Gate count "53"** is the L14-only count (L14_REPORT). If L15Classical.lean is added to the gate's REQUIRED list, the count changes. Update the subsection and Limitations sentences (search "53").
3. **Replace `NEWCOMMIT`** with the version-2 hash at publication, and act on the L1415-REPIN comment.
4. **Not stated in the paper because no report gives it:** the line count of L15Classical.lean, and whether the tamper suite was re-run with L15 included.
5. **Human check outstanding:** the classical statements and the comparison are all AI-produced. The author has not yet checked the L14/L15 statements by hand. The acknowledgements say so.
6. **Dickson page reference:** the citation for Wertheim (Vol. I, p. 196) comes from the statement collector's notes. It has not been checked against the book.
