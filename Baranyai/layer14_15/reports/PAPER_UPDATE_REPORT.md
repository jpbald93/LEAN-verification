# PAPER UPDATE REPORT — Paper Baranyai (Layers 14 + 15)

Date: 2026-10-22. All work was done inline, with no subagents.
- **Paper:** `AFM/Baranyai/baranyai.tex`
- **Backup:** `baranyai.tex.bak-prel1415` (cp, made before any edit)
- **Edit scripts:** `/tmp/barupd/edit.py`, `edit2.py`, `edit3.py`. They used exact-substring replacement, and each old string was asserted to occur exactly once.

## Inputs used
- `L14L15/Baranyai/L14_REPORT.md`
- `L15_COMPARE.md`
- `INTEGRATE_REPORT.md`
  - File names: `Baranyai/L14.lean` (409 lines) and `Baranyai/L15Classical.lean` (358 lines).
  - Namespace: `Baranyai.Classical`.
  - Declaration counts: 32 → 49 → 76.
  - Nothing was dropped.
- `/tmp/blindBaranyai/CLASSICAL_REPORT.md`
- `/tmp/blindBaranyai/classical_statements.txt`
- `/tmp/blindsrc_Baranyai/statements_sources.md`

## Edits (old -> new, one line each)
1. **Preamble, pin comment:** (none) -> `% L1415-REPIN: \commit, \shortcommit (… new commit NEWCOMMIT; replace the NEWCOMMIT tokens …)` added just above `\newcommand{\repo}`/`\commit`/`\shortcommit`. The macros and hashes themselves are unchanged.
2. **`\date`:** "2 October 2026" -> "2 October 2026; version 2, 22 October 2026 (adds the Layer-14 and Layer-15 checks of Section 6.1)".
3. **Abstract:** "…its 32 checked declarations use only Lean's three standard axioms." -> the same text, plus "; with the two verification files added in version 2 … the gate checks 76 declarations, again with standard axioms only."
4. **Contributions, verification bullet:** text added: "in version 2, the main theorems restated with Mathlib-only types (Finpartition, SimpleGraph perfect matchings) with explicit witnesses, and a comparison with textbook statements formalised by a writer that saw neither code nor paper (§6.1)".
5. **Availability:**
   - "all other declarations are in the namespace Baranyai" -> "all other declarations of these three files are in the namespace Baranyai".
   - Added: version 2 adds `Baranyai/L14.lean` (409 lines, top level) and `Baranyai/L15Classical.lean` (358 lines, namespace `Baranyai.Classical`) in a new commit `NEWCOMMIT`. The library files and the statements of 051ae8c are unchanged, and the line references remain valid.
6. **§5 paragraph "No bridge to Mathlib's graph and hypergraph notions"** -> retitled "Bridges to Mathlib's graph and hypergraph notions".
   - It still says the three library files have no bridge.
   - It now says the version-2 files supply the bridges to Finpartition and to SimpleGraph `IsPerfectMatching`.
   - It says no bridge to Hypergraph is formalised.
   - Removed: "We believe these bridges are routine, but they have not been formalised."
7. **§5 Size:** "The definitions are Inv and dem" -> "In these three files the definitions are …", plus a parenthesis saying that the Layer-15 file adds the writer's 4 definitions and 1 bridge definition.
8. **§6 Axiom gate:** sentence added after "PASS (32 …)": with the version-2 files the gate prints "PASS (76 declarations, standard axioms only)" and the tampering tests are all rejected again.
9. **§6 Limits of these checks:** "None of these checks shows…" -> "None of the checks above shows… (Section 6.1 adds an independent comparison with textbook statements)".
10. **§6 Name check:** "It passes." -> "It passes on commit 051ae8c for every name outside Section 6.1; the names of that section are declared only in the new commit, and the check is to be re-run against it."
11. **NEW `\subsection{Layers 14 and 15}\label{sec:l1415}`**, at the end of §6, with these parts:
    - **Opening paragraph:** new commit NEWCOMMIT; earlier files unchanged (hashes); gate 76 = 32 + 17 + 27; tamper all rejected; forbidden-token scan clean outside comments.
    - **Layer 14 paragraph:**
      - 8 theorems restated and proved.
      - Mathlib-only forms are described for `l14_baranyai`, `l14_baranyai_partition`, `l14_complete_graph_one_factorisation` and `l14_dvd_card_of_factorisation`.
      - Mechanical type check: no repo constant appears in any restated type.
      - Witnesses: (6,3) 10 distinct partitions; Fin 2 × Fin 3; (6,2) 5 partitions; K6 5 spanning perfect matchings; K4 3 perfect matchings plus a decide-checked explicit factorisation; {0,2,4,6}; partition form (6,3) 10 classes of 2 disjoint triples; converse with Fin 6 / Fin 5.
      - Not restated, and why: Inv, dem, the arithmetic and counting lemmas, step, `factorisation_congr` and the partition lemmas are internals or are subsumed.
      - No false statement and no extra hypothesis (only `DecidableEq` instances).
      - The n=0 observation: the one-Finpartition form needs 0<n; the family form does not.
    - **Layer 15 paragraph:**
      - Collector: 3 statements with citations (Baranyai 1975, van Lint–Wilson Thm 38.1, Wikipedia).
      - Blind writer: saw no code or paper, transcript audited; 8 statements, 4 own definitions, 3 AMBIGUOUS marks, no extra hypotheses.
      - Counts: 6 covered, 1 new proof, 1 out of scope, 0 narrower, 0 writer statements false.
      - Itemised list of all 8, with the `\decl` names in `Baranyai.Classical`.
      - The bridges are new proofs, and the verbatim check was byte-for-byte.
      - The library is stronger than the textbook in places: n=0, and no 0<n needed for 1_a.
      - All-AI caveat, including that the collector's van Lint–Wilson wording is from memory.
12. **`\section{Limitations and further work}`:** added `\label{sec:limits}`.
13. **Limitations, Bridges:** "Connecting them with Hypergraph, SimpleGraph perfect matchings and Finpartition would make…" -> the version-2 files restate them with Finpartition and SimpleGraph perfect matchings; the Hypergraph bridge is still missing; the bridges live in verification files, not in the library API.
14. **Limitations, Generalisations:** sentence added: Layer 15 states the general almost-regular form (vLW 38.1) as an unproved proposition and proves only its divisible instance.
15. **Acknowledgements and use of AI:** sentence added: in version 2, AI agents wrote the L14 restatements, collected the textbook statements, wrote the blind Lean versions and carried out the comparison.
16. **(edit2) New subsection, token sentence:** "neither file contains sorry, admit, …" -> "a scan … finds no occurrence outside comments (the gate's own token check also passes)". This is accurate because L14.lean contains the English word "admits" inside a docstring (INTEGRATE_REPORT).

## Discrepancies fixed
- **D1.** §5 said there was no bridge to SimpleGraph `IsPerfectMatching` or Finpartition and that the bridges "have not been formalised". This is outdated: L14 and L15 formalise both. Fixed by edits 6 and 13. The Hypergraph bridge is still correctly stated as missing.
- **D2.** The abstract and §6 gate gave 32 declarations only, but the new commit has 76. Fixed by edits 3 and 8; the 32 for 051ae8c is kept.
- **D3.** Availability said "all other declarations are in namespace Baranyai". The L14 declarations are top level and the L15 ones are in `Baranyai.Classical`. Fixed by edit 5.
- **D4.** "Size: the definitions are Inv and dem" is no longer true of the whole repository. Fixed by edit 7.
- **D5.** "None of these checks shows that the formal statement says what the prose says" is now partly addressed by L15. Fixed by edit 9 with a scoped wording.
- **D6.** The name-check claim "It passes" would be false for the new `\decl` names when run against 051ae8c. Fixed by edit 10.
  - Verified: on the local tree at 051ae8c, `namegate.sh` passes on every pre-existing name. It reports 15 MISSING, all of them new L14/L15 names (`l14_*`, `l14w_*`, `Baranyai.Classical.*`), which exist only in commit 1ab2162 / NEWCOMMIT.
- **D7.** The AI-use statement did not cover the new work. Fixed by edit 15.
- **Checked, and no change needed:**
  - The "Generalisations: … None is formalised" bullet is consistent with L15 (classical_Baranyai3_main is out of scope and unproved). Clarified by edit 14.
  - The n=0 discussion is confirmed by L14.
  - No mis-statement or overclaim about theorem content was found: L14 found 0 false statements and L15 found 0 writer mis-statements and 0 narrower cases.

## Compile
- **Before:** pdflatex ×2, rc 0, **13 pages**.
- **After:** pdflatex ×2, rc 0, **15 pages**. No undefined references or citations and no "Rerun" warning.
- **Theorem numbering:** unchanged. Theorems/lemmas/definitions 1–8 have the same numbers; the only new label is `sec:limits`, and the new subsection is §6.1.

## Open items
1. **Repin:** set `\commit`/`\shortcommit` (see the `% L1415-REPIN` comment) and replace the two literal `NEWCOMMIT` tokens (Availability, and the opening of §6.1).
   - The local commit is `1ab21623da9572cb10a8630a086c010b9e554269`, but it is **not pushed** (INTEGRATE_REPORT).
   - Decision needed: whether `\src` line links should keep pointing at 051ae8c (they remain valid, since the files are unchanged) or move to the new commit.
2. **Name gate:** after the push, update `~/Projects/baranyai` to the new commit and re-run `namegate.sh`. It currently fails only on the 15 new names, because the local tree is still at 051ae8c and the gate also checks the pin.
   - `namegate.sh` only accepts `namespace Baranyai` … `end Baranyai` blocks. It may need extending for `namespace Baranyai.Classical` (L15Classical.lean). Its awk matches only the exact line `namespace Baranyai`.
3. **New Mathlib name list:** no new `\mdecl` names were introduced; only the existing `Finpartition` and `SimpleGraph.Subgraph.IsPerfectMatching` are used.
4. **Review of the version-2 date line:** it is placed in `\date`; move it to a footnote if preferred.
5. **Human check:** no human has checked the textbook statements against the printed sources. This is stated in §6.1.
