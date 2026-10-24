# Paper D — paper update for Layers 14 and 15

Date: 2026-10-22. File: `AFM/PaperD/paperd.tex`. Backup: `paperd.tex.bak-prel1415`.
Edit scripts: `<oc>/tmp/paperupd/D/edit.py` and `edit2.py`. Each edit is an exact-substring replacement, asserted to occur exactly once.

Inputs:
- `L14L15/D/INTEGRATE_REPORT.md`
- `/tmp/PAPERD_L14_REPORT.md` (fetched with scp from john)
- `PaperD/layer15/PAPERD_L15_COMPARE.md` and `PAPERD_L15_GAPS.md`
- `/tmp/blindD/CLASSICAL_REPORT.md`
- `PaperD/layer15/classical_statements.txt`

`/tmp/L14L15/D/L15_COMPARE.md` and `/tmp/blindsrc_D/` do not exist; I used the layer15 copies instead.

## Edits (old -> new)
1. **E1 Pins:** added the comment `% L1415-REPIN: commitof:clifford … commitof:steinerlehmus (and the eight short hashes in the Availability table; NEWCOMMIT tokens …)` above the `\def commitof:` lines. No hashes changed.
2. **E2 Date:** "14 October 2026" -> "14 October 2026; version 2, 22 October 2026 (adds Section ref{sec:l1415})".
3. **E3/F1 Abstract:** after "...its Clifford point lies at infinity." added:
   - this concerns our predicate (general position only for initial pairs and triples), not the textbook chain, which needs a genuine circle at every odd level, whereas here a level-5 object provably lies on no circle;
   - version 2 adds the Layer-14 restatements with witnesses and the Layer-15 comparison, which also proves existence of the Fermat points and Thébault circles (for its definitions) and Kosnita in the form "concurrent or all parallel".
4. **E4 Contributions item 1:** "general position has its Clifford point at infinity…" -> "general position in the predicate's sense (pairwise transversal, every triple non-degenerate) … This is a statement about the predicate, not a counterexample to Clifford's chain."
5. **E5 What is not claimed:** added "That failure does not refute the textbook chain, in which every level is a genuine circle or a unique point; the all-n chain in that form remains open here."
6. **E6/F4 Availability:** new paragraph "Version 2":
   - one new commit per repo adds `<Lib>/L14.lean` and `<Lib>/L15Classical.lean`, two root import lines, the extended gate list and the README;
   - the eight new hashes are the literal token `NEWCOMMIT`;
   - all other library files, cited statements and source lines are unchanged; counts and links refer to the original commits.
7. **E7 End of §chainfail:** "(an argument, not a machine-checked statement)" -> adds that, for the subfamily omitting circle 6, Layer 15 proves any level-5 object contains three distinct collinear points.
8. **E8/F2 §chainfail:** after "…not of Clifford's theorem for n≥6." added:
   - the failure is about this predicate (odd levels a circle *or a line*; general position only for initial pairs and triples);
   - it does not refute the textbook chain (genuine circles and unique points at every level);
   - `cov_D1_d_no_spherical_level_five`: the level-5 object omitting circle 6 contains 2/3−4i, −8/3−4i, −6−4i and lies on no circle;
   - `cov_D1_d_counterexample_not_writer_data`, stated with its identification premise (the full translation between the two chain structures is not formalized).
9. **E9 Lester:** "assumes the Fermat points and does not assert their existence." -> adds that existence is proved in Layer 15 (`Lester.Classical.cov_D3_obligation`).
10. **E10 Thébault:** same addition, giving the Layer-15 formulation of the two circles (`Thebault3.Classical.cov_D4_obligation`).
11. **E11 Kosnita:** after "…the exclusion is a weakening." added "Layer 15 removes it": on S=5R² the lines (when defined) are pairwise parallel (`cov_Kosnita_zero_locus`), so "concurrent or all parallel" holds (`cov_D5`).
12. **E12 Degeneracy table, Kosnita row:** added "; lines parallel there (Layer 15)".
13. **E12b Degeneracy table, Lester row:** added "; Fermat points assumed (existence: Layer 15)".
14. **E13 Verification, satisfiability:** after "evidence, not a certificate." added that in version 2 the Layer-14 witnesses are Lean certificates for every main theorem except Thm 3 (Clifford n=6) and the general-n classification.
15. **E14 New subsection** "Layers 14 and 15" (`\label{sec:l1415}`), placed at the end of §Verification, before Limitations. It covers:
    - file names, the namespace `<Lib>.Classical` and the gate counts 63/63/61/75/34/25/15/10 (346 in all); tamper tests all rejected; nothing dropped; no `set_option`;
    - **Layer 14:** 12 restatements; 11 witnesses (not Thm 3, whose witness would need uniqueness); `not_cliffordChain_of_six_le` and `cliffordChain_iff` not restated (recursive predicate); none false; the Thébault restatement is implied by the library theorem, not shown equivalent;
    - **Layer 15:** the writer setup (Opus CLI, isolated folder, read only its brief, transcript audited); 18 statements; 16 proved exactly (10 main + 6 obligations); 0 narrower; D1(d) all-n out of scope (only odd n=3 exact); 0 writer statements false;
    - the NEW PROOFS list: Kosnita parallel case; five circles without extra distinctness; D1(c) canonical identification (uses the writer's uniqueness hypothesis); Lester with geometric Fermat points; Thébault with either side assignment; six obligations; the chain level-5 obstruction;
    - direct specializations; what is not covered; the earlier writer attempts by another model were voided and not used.
16. **E15 Limitations 1:** added that the n≥6 failure does not refute the textbook chain, which remains open.
17. **E16 Limitations 3 (Existence):** "we do not prove that they exist" -> "their existence is proved only in the Layer-15 files, for the definitions used there".
18. **E17 Limitations 4:** added that the Layer-14/15 work was also done by AI, the writer's isolation rests on its audited transcript, and no human has checked the textbook statements; the Layer-15 D1(c) comparison uses the writer's uniqueness hypothesis; general-n chain not covered.
19. **F3:** the chain bullet in the new subsection notes that the identification of the two chain structures is a premise.

## Discrepancies fixed
- **Chain failure presented without scope:** the abstract, contributions, §chainfail, "What is not claimed" and Limitations now say it concerns the paper's predicate and does not refute the textbook chain. Report lines: L15_COMPARE "Verdict"; GAPS Gap 5.
- **Existence outdated:** "We do not prove that [Fermat points / Thébault circles] exist" in Limitations, §lester and §thebault is now qualified, since Layer 15 proves existence for its definitions (GAPS 4b, 4c).
- **Kosnita:** the S=5R² exclusion was described only as a weakening. The paper now records the new parallel-case proof (L15_COMPARE row D5, item 8).
- **Satisfiability:** the paper said no main theorem had a Lean certificate of satisfiable hypotheses. It now says Layer-14 witnesses exist for all but Thm 3 and the general-n classification (L14 report).
- **Unchanged on purpose:** the §blind sentence "We have not proved uniqueness" stays, because uniqueness of the Clifford point is still not proved in the developments (Layer 15 *assumes* it as a writer hypothesis).

## Checks
- `pdflatex` run twice: rc 0 both times. No undefined references or citations, and no rerun warning.
- **Pages:** 16 before -> 19 after.
- **Theorem numbering:** unchanged. Labels thm:cliff4…thm:steiner = 1…11 in both builds, compared from the .aux files.
- **Overfull boxes:** one, in the Theorem 5 header. It was already in the old build and was not touched.
- **New `\decl` names:** all 23 occur in the REQUIRED additions listed in INTEGRATE_REPORT.md or in the L14 report. The paper's `namegate_d.sh` was NOT re-run: it reads gate lists from jack's original repo directories, not the `pubD_*` copies. It must be re-run after the new commits are pushed and the directory map is updated.

## Open items
- Replace the 8 `NEWCOMMIT` tokens once the commits are pushed. The local commits are 927f7f8, b6649f4, 6040681, d307293, 2edce1e, 7eaae53, 50e1f17, 53b6246. They are not pushed and could change if amended.
- Decide whether the `\src` pins (`commitof:*`) should move to the new commits. Line numbers of the old files are unchanged, so the current links stay valid.
- Re-run the name gate against the new commits.
- Still unproved:
  - D1(d) for all n in the textbook form;
  - uniqueness of the Clifford point in the developments;
  - a Layer-14 witness for Thm 3 (Clifford n=6);
  - a Mathlib-only restatement of the general-n classification.
- Layer-15 sources: `/tmp/blindsrc_D/statements_sources.md` was missing, so the subsection only says the statements were "collected from the literature … with their sources" and gives no per-item citations.
