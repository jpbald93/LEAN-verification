MINOR — Paper D — 5 issues

Paths below are relative to AFM/ unless absolute. P = PaperD/paperd.tex; U = L14L15/D/PAPER_UPDATE_REPORT.md; I = L14L15/D/INTEGRATE_REPORT.md; C = PaperD/layer15/PAPERD_L15_COMPARE.md; G = PaperD/layer15/PAPERD_L15_GAPS.md; W = /tmp/blindD/CLASSICAL_REPORT.md; L = /tmp/PAPERD_L14_REPORT.md.

1. MINOR — Incorrect source-collection provenance and overly literal isolation description (P:802–807).
   The paper credits “a second agent” with collecting the textbook statements, whereas the review brief explicitly specifies author collection for D/E (L14L15/ASTRA_REVIEW_BRIEF.md:20). “Read nothing but its brief” is also literally inaccurate: the brief was supplied in the prompt, and the writer read its own statements/probe/output (W:62–65; PaperD/layer15/writer/transcript.jsonl:22,35,37,41,43).
   Exact fix: replace “A second agent collected” with “The author collected”; replace “the accepted run read nothing but its brief (its transcript was audited)” with “the accepted run received the source brief in its prompt and otherwise accessed only its own generated statements, Mathlib probes and compiler output (its transcript was audited)”. This preserves the supported blindness claim.

2. MINOR — Abstract overstates witness coverage (P:86–87).
   “Restatements of the main theorems with explicit witnesses” does not disclose that the Clifford n=6 restatement has no witness and the general-n classification was not restated. The body is appropriately qualified (P:793–797), and L:10–15,99,109 explicitly records these omissions.
   Exact fix: replace that phrase with “twelve Mathlib-only restatements, eleven with explicit witnesses; the Clifford n=6 witness and general-n restatement remain open”.

3. MINOR — Blanket absence of extra hypotheses obscures the L14 Clifford n=6 weakening (P:793–800).
   The paper describes the universally quantified non-collinearity premises but then says no restatement “needed an extra hypothesis”. L:99 explicitly calls these premises stronger than the library's explicit-point premises, with equivalence dependent on uniqueness not proved there. The report's blanket summary (L:115) does not erase this qualification. The Thébault one-way implication is already honestly disclosed (P:798–800; L:118–122).
   Exact fix: replace “No restatement was false or needed an extra hypothesis.” with “No false restatement was found. For Clifford n=6, the universally quantified non-collinearity premises are stronger than the explicit-point premises; their equivalence has not been formalized. The witness remains open.”

4. MINOR — Writer-added assumptions for Clifford n=5 are not explicitly disclosed in the new comparison summary (P:844–846,871–873).
   The summary calls n=5 a direct specialization and highlights uniqueness only for n=6. W:44–45 and C:27 show that D1(b) also assumes uniqueness of the four-circle common points and non-collinearity of the five supplied points. Exact signature coverage is valid, but is not an unconditional upgrade of the published circle-or-line theorem to arbitrary supplied points on a genuine circle.
   Exact fix: after the direct-specialization sentence add “For Clifford n=5, the writer additionally assumes uniqueness of each four-circle common point and non-collinearity of the five supplied points; these assumptions identify our explicit points and remove the line alternative.”

5. MINOR — Version-2 availability/integrity wording needs the root-file exception and local-commit status (P:201–207,775).
   I:4,27,36,41 and the per-repo hash tables (e.g. I:66–68) establish local, unpushed commits and changed root import files. “No earlier library file changed” is therefore false literally; “every statement ... cited in this paper” also needs to exclude the newly cited declarations. Eight NEWCOMMIT placeholders are correctly present and should remain (P:203–205; U:65–67).
   Exact fix: start the availability paragraph “Each repository has one new local commit, not yet pushed, ...”; replace P:205–206 with “All pre-existing non-root library files, and the statements and source lines cited from them, are unchanged; ...”; replace P:775's sentence with “No pre-existing library file changed except for the two appended root imports.”

Checks completed:
- Required same-folder L14_REPORT.md and L15_COMPARE.md are absent. Used the documented substitutes L and C, plus G for the completed gap pass (U:6–13). No missing-file claim is counted against the mathematics.
- Numeric checks pass: 63+63+61+75+34+25+15+10 = 346 (P:773–774; I:10–17); twelve L14 restatements/eleven witnesses (P:781–795; L:10–15,97–109); eighteen writer statements and sixteen exact proofs = ten main + six obligations, zero remaining narrower cases, two all-n chain statements outside coverage (P:807–815; W:9–25; C:26–43; G:189–201). No numerical mismatch found.
- New-proof claims and existence corrections are supported: P:418–420,441–444,471–474,817–837 versus C:35–43,107–110 and G:18–23,48–61,83–91,97–158. The chain obstruction's identification premise and unformalized translation are disclosed (P:353–358,838–842; C:83–99; G:170–185). General-n noncoverage and voided writer attempts are stated (P:846–852; U:44,68–72).
- Diff against PaperD/paperd.tex.bak-prel1415 contains only L14/L15-related changes. All eleven theorem-environment blocks are byte-identical, so numbering is unchanged (P:231–496; backup:212–458; U:60). All 23 newly cited declaration names occur in I:54,99,151,195,241,285,329,373 or L:151,153. The paper name gate was not independently rerun (U:62).
- Ran the requested two-pass pdflatex command: second-pass rc = 0; `grep -c undefined paperd.log` = 0. The shell command's final status 1 is grep's expected no-match status, not a LaTeX failure. Output is 19 pages (PaperD/paperd.log:715), agreeing with U:58–59. Paper source was not edited.
