# Paper CB — PAPER UPDATE for Layers 14 + 15 (2026-10-22)

Paper: `AFM/CayleyBacharach/cayley_bacharach.tex`. Backup: `cayley_bacharach.tex.bak-prel1415` (cp, taken before any edit).
All edits were exact-substring replacements in Python (`/tmp/cbupd/edit.py` and `edit2.py`), each asserting that its old string occurs exactly once. All work was inline, with no subagents.
Inputs: L14_REPORT.md, L15_COMPARE.md, INTEGRATE_REPORT.md (final names: `CayleyBacharach/L14.lean` in namespace `CBL14`, `CayleyBacharach/L15Classical.lean` in namespace `CayleyBacharach.Classical`; gate 100 → 127 → 168; nothing dropped), /tmp/blindCB/CLASSICAL_REPORT.md, classical_statements.txt, and /tmp/blindsrc_CB/statements_sources.md.

**Version label.** The paper was already "version 4", so this update is called **version 5**, not "version 2" (the brief's "version 2" assumed a first revision). Every occurrence in the paper says version 5.

## Edits (old -> new)
1. Preamble: (none) -> `% L1415-REPIN: \commit \shortcommit (keep 9a4f11e for the line references; fill the NEWCOMMIT tokens in the Availability paragraph and in Section sec:l1415)`, placed right above the `\repo`/`\commit` definitions. The macros and hashes themselves were not changed.
2. `\date{4 October 2026 (version 4)}` -> same + `\\ \small Version~5, October 2026: adds Layers~14 and~15 (Section~\ref{sec:l1415})`.
3. Abstract: "…for fields with more than ten elements. We also" -> "…for fields with more than ten elements; version 5 adds direct proofs, not through Cayley–Bacharach, of Pascal's and Pappus's theorems and of the Braikenridge–Maclaurin converse over every field (Section 9.1). We also".
4. Abstract: "about 4,150 lines and uses no sorry" -> "about 4,150 lines (the Layer-14/15 check files added in version 5 have about 2,100 more) and uses no sorry". Source: 1050 + 1040 lines in INTEGRATE.
5. Contributions, Pascal/Pappus bullet: appended "Version 5 adds direct proofs of Pascal, Pappus and Braikenridge–Maclaurin over every field (Section 9.1)". Added a new bullet: "Version 5: the main theorems restated with Mathlib-only types, each with an explicit non-degenerate witness, and a comparison with Lean statements written blind from textbook statements".
6. Availability: "…all declarations are in the namespace PlaneCubic." -> "…all declarations of the main files are in the namespace PlaneCubic; the version-5 files use the namespaces CBL14 and CayleyBacharach.Classical (Section 9.1)".
7. Availability: appended "Version 5 of this paper adds the Layer-14 and Layer-15 files of Section 9.1 in a new commit, NEWCOMMIT. The earlier statements and library files are unchanged in that commit (only the root file gains two import lines, and gate.sh, .gitignore and the README are updated), so the line references above are valid at both commits."
8. Table 2 (tab:finite): kept the row "Pascal, Pappus as formalised | q≥11 | not investigated" but renamed it "Pascal, Pappus via Cayley–Bacharach". Added a row "Pascal, Pappus, direct proofs (Section 9.1) | all q | ---".
9. §Applications: "…such a direct proof exists [PascalHexagon]." -> same + ", and version 5 of this development contains direct proofs over every field as well (Section 9.1)".
10. §Verification: "…on a fresh clone of commit 9a4f11e it prints PASS (100 declarations, standard axioms only)." -> same + " with GNU tools (on macOS the published script stops at a GNU-only mktemp option; see Section 9.1)".
11. §Verification: "…216 theorems and 32 definitions." -> same + " (at the published commit; version 5 adds the two modules of Section 9.1)".
12. §Verification, after the hand-check sentence: added "The Layer-14 and Layer-15 statements of Section 9.1 have not been checked by hand."
13. NEW `\subsection{Layers 14 and 15}\label{sec:l1415}` (it is §9.1), placed at the end of §Verification and before Limitations. It covers:
    - files, line counts, namespaces and NEWCOMMIT;
    - gate PASS with 168 declarations (100 + 27 + 41); tamper rejects all 6 planted defects; earlier files byte-identical;
    - gate portability: the published gate.sh failed on macOS because of GNU `mktemp`; the new commit uses a portable temp name and passes with BSD tools; tamper.sh still needs GNU sed.
    - **Layer 14:** the encoding, and the bridges `l14b_*`. Twelve restatements cover nine paper results:
      - Thm 5, Thm 6, Thm 7 (infinite case, and the finite case for |K|∉{4,5,7}), Thm 9, Thm 3;
      - Thm 11/12, including the `_points` variants;
      - the cubic part of Lemma 2, and `line_lemma_false_zmod_two`.
      The mechanical namespace check found nothing; none turned false or needed an extra hypothesis. Six witnesses, each with its non-degeneracy facts. Not restated (time box): Prop 13 (`det_gram_eq_zero_iff`, `det_gram_linMul`, `pascal_clean_det`), the conic part of Lemma 2, and the auxiliary lemmas.
    - **Layer 15:**
      - Pipeline: sources with citations (EGH, Fulton §5.6, Reid, Coxeter, Wikipedia; page numbers "as best known"), the blind writer, the audited transcript, and the comparer.
      - Counts: 15 statements (11 theorems + 4 obligations) = 9 covered / 3 narrower / 3 out of scope (2 of them proved) / 0 false as written.
      - **New proofs:** `cov_CB3_a` (Pascal over every field, via the BM conic and `conics_le_one`), `cov_CB3_b` (Braikenridge–Maclaurin over every field), `cov_CB4_a` and `cov_CB4_b` (Pappus, including the hexagon form, over every field; `l15_papid`), and `l15_intMult_ne_zero_iff`. Also listed: the library-route versions `cov_CB3_a_part`, `cov_CB4_a_part` and `cov_CB4_b_part`, which carry |K|>10.
      - **Narrower:**
        - CB1(b) and CB1(b)-irreducible: proved only for distinct points; missing are genuine multiplicities (Bézout plus local intersection numbers).
        - CB2(b)-distinct: existence is proved; missing is uniqueness (at most 9 common rational points, i.e. Bézout).
      - **Out of scope:** CB2(b) over an algebraically closed field (not proved), and BM with its obligation (proved).
      - **Writer mis-statements:** none.
14. Limitations, Multiplicities: appended "The Layer-15 file proves only the case of distinct points of Fulton's multiplicity version (Section 9.1)".
15. Limitations, Rational points: "…counted with multiplicity''." -> "…counted with multiplicity'', nor that two coprime cubics have at most nine common rational points; the uniqueness half of the corresponding Layer-15 statement is therefore open".
16. Limitations, "Pascal and Pappus over small fields": rewritten so that the CardGT K 10 restriction and the "neither has been done" plans apply to the *Cayley–Bacharach route*. It adds "Pascal and Pappus themselves now hold over every field by the direct proofs of version 5 (Section 9.1)".
17. Limitations, Representation: appended "The Layer-14 file bridges forms to MvPolynomial for the restated theorems, and the Layer-15 file connects some of them to points of Projectivization (Section 9.1); the main files are unchanged".
18. Acknowledgements/AI: added "The Layer-14 and Layer-15 files, the collection of classical statements, the blind formalisation and the comparison (Section 9.1) were all done by AI agents and have not been checked by hand."

Names use the paper's name-gated `\decl{}` macro: 38 new names. Namespaces and module paths use `\lean{}` / `\path{}`.

## Discrepancies fixed
- **Outdated / overclaim:** Limitations said Pascal/Pappus over small fields was open ("Neither has been done"), and Table 2 listed small-field Pascal/Pappus as "not investigated". L15 proves both over every field (cov_CB3_a, cov_CB4_a, cov_CB4_b). Fixed by edits 3, 5, 8, 9 and 16. The CB-route statements remain correct as written.
- **Incomplete:** the paper had no Braikenridge–Maclaurin converse. It is now reported as a new L15 proof (edits 3, 5 and 13).
- **Outdated:** the namespace sentence ("all declarations are in PlaneCubic") no longer holds for the new files (edit 6). The gate count of 100 is valid only at the old commit; 168 at the new commit is in §9.1 (edits 10 and 13). Module/line counts are marked as published-commit counts (edits 4 and 11).
- **Portability (gate):** "on a fresh clone it prints PASS" was true only with GNU tools; the published gate.sh fails on macOS (L14 finding 2). Disclosed in edit 10; the fix in the new commit is described in edit 13, and so is the remaining GNU-sed dependence of tamper.sh.
- **Limitations, multiplicities and rational points:** now state precisely what L15 adds (the distinct-points case) and what stays open (genuine multiplicities; uniqueness, i.e. at most nine rational common points). Edits 14 and 15.
- **Hand-check scope:** the author's hand check covers Table 1 only. The L14/L15 statements are disclosed as unchecked (edits 12 and 18).
- **Checked, no conflict found:**
  - Intro Theorem 1 and related work: L15 found no false statement.
  - Example 4's claim that "no four collinear, no seven on a conic" is sufficient: consistent with cov_CB2_a.
  - The Prop 13 text: not restated, and disclosed as such.
  - The paper has no "what is not claimed" section.

## Pages and compile
- Before: 15 pages (backup recompiled in /tmp/cbupd, rc 0).
- After: **17 pages**. `pdflatex` ran twice, rc 0 both times; 0 undefined references, 0 multiply-defined labels, 0 overfull boxes, no `!` errors.
- Theorem numbering is unchanged: textbook=1, line=2, criterion=3, ex=4, gp=5, ncf=6, classical=7, f3=9, counter=10, pascal=11, pappus=12, gram=13. The new subsection is 9.1.

## Name check
- `namegate.sh` with SRC = ~/Projects/cayley-bacharach-repo/CayleyBacharach (a local tree at 9a4f11e; the script's default path lacks ClassicalF3.lean): **PASS before the edits (99 names)**.
- After the edits it checks 137 names and fails only on the 38 new L14/L15 names, because that tree predates the new commit. All 38 new names were verified separately: each appears in the REQUIRED lists of L14_REPORT/INTEGRATE_REPORT or as a `theorem` in L15_compare.lean (which INTEGRATE says was carried over verbatim). The three cited existing names (`conics_le_one`, `pascal_clean`, `pappus_clean`) exist at 9a4f11e. All 39 anchors are unchanged.

## Open items
1. After pushing commit `d9c674c68c0a1b475a284f9bd33ec5f7e6d52689` (local on john, unpushed, branch master), replace the two `NEWCOMMIT` tokens (Availability and §9.1). Keep `\commit`/`\shortcommit` = 9a4f11e unless the line links should move; per INTEGRATE all line references stay valid.
2. Re-run namegate.sh against a checkout of the new commit to name-check the 38 new names mechanically. The local machine has no tree with L14/L15 files, and john was not reachable from here.
3. INTEGRATE notes that the commit message carries a Co-Authored-By trailer, and that tests/tamper.sh still uses GNU-only `sed -i` (owner decision). The paper discloses the latter.
4. The "version 5" label (rather than "version 2") should be confirmed.
5. The citations for Reid and Coxeter in §9.1 are named in the text and not added to the bibliography, because the paper's bibliography does not contain them. Add bibitems if wanted.
