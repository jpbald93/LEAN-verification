# Paper B — Layer 14/15 paper update report (2026-10-22)

Paper: `AFM/PaperB/paperb.tex`. Backup: `paperb.tex.bak-prel1415` (cp, before any edit).
Edits: exact-substring replacement in Python. Each old string was asserted to occur exactly once. Scripts: `<oc>/tmp/paperupd/B/s/edit.py` (16 edits) and `edit2.py` (3 follow-up edits). No commit macro or hash was changed.
Inputs: L14_REPORT.md, L15_COMPARE.md, INTEGRATE_REPORT.md, /tmp/blindB/CLASSICAL_REPORT.md, classical_statements.txt, /tmp/blindsrc_B/statements_sources.md. The version-2 REQUIRED lists were read from jack `~/pubB_<repo>/gate.sh`, where the commits exist.

## Edits (old -> new)
1. `\date{7 October 2026}` -> `\date{7 October 2026 (version~2: 22 October 2026)}`
2. Abstract, after the arm64 sentence: (nothing) -> version-2 sentence covering Layer 14 (Mathlib-only restatements + witnesses), Layer 15 (model-written statements from textbook statements), the new proofs (Malfatti containment, angle-form Bretschneider), 1 writer statement false as written, and 2 ways the libraries are narrower (Lebesgue area; Malfatti uniqueness).
3. Contributions, last bullet: "...together with the limits of these checks." -> adds "; and, in version~2, Mathlib-only restatements ... (Layer 14) and a comparison ... (Layer 15, Sec. l1415)".
4. Pins block: (nothing) -> `% L1415-REPIN: \commitfeuerbach \commitbrahmagupta \commitmiquel \commitmalfatti and commitof:feuerbach commitof:brahmagupta commitof:miquel commitof:malfatti (...)`, placed directly above the `\newcommand{\commitfeuerbach}` line.
5. Availability, after "All declarations are in the namespace of the library name.": (nothing) -> a "Version 2" paragraph. It gives the new commit per repo as `\texttt{NEWCOMMIT}` (×4), names the eight files `<Lib>/L14.lean` and `<Lib>/L15Classical.lean` with their line counts, says that root/gate.sh/README also change, gives the namespace `<Lib>.Classical`, and says the earlier files are byte-identical so earlier statements, line references and counts are unchanged.
6. Miquel model: "...each of the three circles exists and is unique." -> adds a parenthesis: non-collinearity is stated only in prose and is proved in v2 as `Miquel.Classical.cov_B2_obligation`.
7. Malfatti §Scope: "Containment is proved only in part ... we do not prove that each circle lies inside the triangle" -> "In the files of the first version containment is proved only in part ...; Version 2 proves full containment (`Malfatti.Classical.l15_malfatti_subset`)".
8. Verification preamble (italic): (nothing) -> "Layers 14 and 15 (Sec. l1415) were added in version 2, on 21–22 October 2026."
9. "Limits of these checks": "...complemented by a blind re-formalisation." -> "...a blind re-formalisation and, in version 2, by a comparison with classical statements (Sec. l1415)."
10. NEW `\subsection{Layers 14 and 15}\label{sec:l1415}` at the end of §Verification, before Limitations. Contents: an italic header (gates 71/101/50/93 vs 46/84/30/77, tamper 6/6, forbidden grep empty); Layer 14 (6 restatements, namespace-free type check, a witness table with the distinctness proved, no restatement false or strengthened, the finrank-2 remark, and the Table 1 rows not restated with the reason); Layer 15 (sources with citations, writer saw only those statements, 19 statements of which 4 are obligations, 3 own definitions, transcript audited, comparer; counts: covered 13 / narrower 4 / out of scope 1 / writer false 1; every narrower case with what is missing; the writer mis-statement with its counterexample; the list of new proofs (i)–(v); the caveat that the writer is a model).
11. Limitations, Feuerbach prior art: "...produces it inside an existential; and" -> adds "(version 2 proves that it is unique for a non-equilateral triangle, `Feuerbach.Classical.cov_B1_remark_unique`)".
12. Limitations, Brahmagupta area: "...but this is not proved inside Lean." -> adds "For the same reason the Layer-15 classical statements (Lebesgue measure) are proved only under this identification as an explicit hypothesis."
13. Limitations, "Brahmagupta: no trigonometric Bretschneider. The angle form ... is not proved; only ... diagonal form" -> "Brahmagupta: trigonometric Bretschneider only for convex quadrilaterals. ... proved in version 2, shoelace area, convex (`Brahmagupta.Classical.l15_bretschneider_shoelace`); version-1 files have only the diagonal form, valid for every quadrilateral."
14. Limitations, Miquel model: "...a restatement would be routine but has not been done." -> "Version 2 adds such restatements: `Miquel.l14_miquel_cospherical` (Collinear, side lines, Cospherical, still in ℂ) and the classical statements in EuclideanSpace ℝ (Fin 2) (`Miquel.Classical.cov_B2_b`)."
15. Limitations, "Malfatti: uniqueness and containment. ... We do not prove that each circle lies inside the triangle ..." -> "Malfatti: uniqueness. Uniqueness not proved; hence the radius formula holds for the constructed circles, and for an arbitrary classical triple only under uniqueness as a hypothesis (`cov_B4_b_of_unique`). Containment, listed here in version 1, is now proved (`l15_malfatti_subset`)."
16. Brahmagupta "Relation to the earlier Lean proof": "...verification record of Section verify." -> adds "Version 2 adds the angle form of Bretschneider's formula for convex quadrilaterals; we did not search for earlier formal proofs of it."
17. (edit2) L14/15 italic header: "...is empty.}" -> adds "The battery layers (mutation, ablation, satisfiability) and the arm64 rebuild were not repeated on the new files." (Neither report says they were run.)
18. (edit2) Covered bullet: "the two remarks, new" -> "the two remarks, which the paper does not state and which are proved here for the first time".
19. (edit2) Narrower bullet: "...angle form of Bretschneider's formula are proved for the shoelace area" -> inserts "(the last not stated in the version-1 files)".

## Discrepancies fixed (paper text contradicted by the findings)
- D1. Limitations + Malfatti §Scope said containment of the Malfatti circles in the triangle is not proved. It is now proved (L15_COMPARE NEW PROOF 5, `l15_closedBall_incenter_subset`, `l15_malfatti_subset`). Edits 7, 15.
- D2. Limitations said the trigonometric Bretschneider formula "is not proved". It is now proved for convex quadrilaterals with the shoelace area (NEW PROOF 3, `l15_bretschneider_shoelace`). For Lebesgue area it holds only under AreaBridge. Edit 13; also edit 16 so that "what our development adds" stays accurate.
- D3. Limitations said a Miquel restatement with Mathlib's Cospherical "has not been done". It is now done (L14 `l14_miquel_cospherical`; L15 `cov_B2_b`). Edit 14. Its other sentences (degeneracies excluded, M not distinct from D,E,F) still stand.
- D4. Miquel non-collinearity was stated only in prose. It is now proved (`cov_B2_obligation`). Edit 6 is an addition, not a correction.
- D5. Feuerbach point: the paper says the point is not given explicitly. That is still true, but uniqueness (non-equilateral) is now proved. Edit 11 adds this without dropping the original claim.
- D6. The Layer-15 narrower findings were made explicit wherever the paper discusses the limits. Edit 12 (Lebesgue area/AreaBridge) and edit 15 (uniqueness ⇒ radius formula ∃ vs ∀).
- D7. Availability / verification text said the checks ran on the version-1 commits only. Version 2 is now described, and the earlier files are said to be byte-identical (INTEGRATE_REPORT "All published library files are byte-identical to HEAD"). Edits 5, 8.
- Checked and left unchanged: abstract/contributions "Miquel ... weaker hypotheses"; "Brahmagupta area is the shoelace value"; "Malfatti uniqueness not proved"; "Feuerbach Fact(finrank=2) unused". L14 shows the Fact is needed only in the defining-property restatement, not in Thm 1, so no contradiction; the new subsection says this explicitly. The gate counts 46/84/30/77 in §Verification refer to the v1 commits; they stay, and the v2 counts are given in the new subsection.

## Counts used (all from report lines)
- L14: 6 restatements (Feuerbach 1, Brahmagupta 1, Miquel 2, Malfatti 2) covering all 4 numbered theorems; none false or strengthened.
- L15: 19 writer statements (4 obligations). Classified: covered 13, narrower 4 (B3_a, B3_b, Bretschneider[O/N], B4_b), out of scope 1 (B4_a_unique, unproved), writer false 1 (B3_remark_cyclic_iff).
  NOTE: L15_COMPARE's totals line says "E 12", but its own table lists 13 E rows (B1×7, B2×3, B3_obligation, B4_a, B4_b_obligation). 12 + 3 + 1 + 1 + 1 = 18 ≠ 19, so the table count of 13 is the one used. The paper puts the O/N Bretschneider row under "narrower".
- Gates v2: 71/101/50/93 (INTEGRATE_REPORT). Files and line counts: INTEGRATE_REPORT tables.
- Every \decl added (26 new distinct names) was checked against the union of the v2 REQUIRED lists on jack: all present (`comm` output empty apart from the macro-definition line).

## Compile
- pdflatex ×2: rc 0, rc 0. 0 undefined references/citations, no LaTeX errors. 5 overfull boxes, the same 5 table rows (3.4pt) as before the edit; none new.
- Pages: 23 before -> 26 after.
- Theorem numbering unchanged (thm:feuerbach..malfatti = 1..4, same as backup). The new subsection is 9.1. No section numbers shifted, because it is a subsection at the end of §9.

## Open items
1. NEWCOMMIT: 4 occurrences in the availability text (plus the REPIN comment). INTEGRATE_REPORT records the local (unpushed) commits feuerbach 83d2486e8c67…, brahmagupta ded0ff1c4790…, miquel 9f99fbf4ebc0…, malfatti c0f16c5521c5… on jack. Nothing has been pushed; fill these in (or the post-push hashes) at publication.
2. Commit macros/`commitof:` still point at the v1 commits. That is intentional, since the line links remain valid (the files are byte-identical), but see the REPIN comment if v2 links are wanted.
3. "Transcript audited": no separate audit report was found among the inputs. The only evidence is the writer's self-reported file list (CLASSICAL_REPORT "Files read") and the statement writer's run.log (web: Wikipedia only). The paper's wording follows the instruction; please confirm that an audit exists, or soften the wording.
4. The statement writer's run.log says it read "only the brief and the Wikipedia page", while sources.md cites Coxeter–Greitzer, Johnson etc. The paper says "collected from the literature (with citations)". These citations may be second-hand via Wikipedia, so consider adding a caveat.
5. The battery (mutation/ablation/satisfiability), the arm64 rebuild and namegate4.sh were not rerun on v2. The paper now says so for the battery and rebuild. namegate4.sh checks against `~/Projects/<repo>-repo` (v1 REQUIRED), so it will flag the 26 new names until those mirrors are updated to the v2 commits.
6. The README in each repo also gained origin's licence/citation commits (merged before the new commit). The paper text did not need a change for this.
