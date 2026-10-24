# Paper A — update for Layers 14 and 15 (PAPER_UPDATE_REPORT)

Date: 2026-10-22. Paper: `AFM/CoordCertificates/paper.tex`. Backup: `paper.tex.bak-prel1415` (made before any edit; byte-identical to the previous paper.tex).
Method: one Python script (`/tmp/pupdA/edit.py`) of exact-substring replacements. It asserted each old string occurs exactly once (26 replacements), plus one follow-up replacement inside the new subsection.
Sources used: INTEGRATE_REPORT.md (file names, counts, gate/tamper, nothing dropped), L14_REPORT.md, L15_COMPARE.md, /tmp/blindA/CLASSICAL_REPORT.md, classical_statements.txt, /tmp/blindsrc_A/statements_sources.md, /tmp/blindA/Classical.lean (for the writer statements' exact form), L15_scratch/*.lean (for declaration names).

## Compile
- Before: pdflatex ×2, rc 0, **22 pages**, no undefined references.
- After: pdflatex ×2, rc 0 both times, **25 pages**, 0 undefined references/citations, 0 `!` errors, 0 overfull boxes.
- Theorem numbering unchanged: the same 6 theorem environments in the same order, Theorems 1–6. The new subsection is §10.1 (`\label{sec:l1415}`), placed inside Verification after the hand-check sentence and before Limitations. Section numbers are unchanged.

## Edits (old → new, abbreviated)
| # | label | old | new |
|---|---|---|---|
| 1 | date | `\date{7 October 2026}` | `\date{7 October 2026; version~2, 22 October 2026}` |
| 2 | repin-comment | `% Commit hashes of the published repositories (content commits;` | `% L1415-REPIN: \commitdesargues \commitmonge \commitsimson \commitnapoleon \commitlami \urlcommitdesargues \urlcommitmonge \urlcommitsimson …` |
| 3 | abstract-lines | `The five libraries have about 1{,}430 lines of Lean, use no \lean{sorry}, and depend only …` | `The five libraries, without the version-2 files described next, have about 1{,}430 lines of Lean, use no \lean{sorry}, and depend only on Le…` |
| 4 | contrib-simson | `non-degenerate triangle; the geometric converse is not proved (Section~\ref{sec:simson}). …` | `non-degenerate triangle. The first version did not prove the geometric converse; version~2 proves it, in \lean{EuclideanSpace ℝ (Fin 2)}, in…` |
| 5 | contrib-v2 | `needs it, or it is only needed for the statement to mean what it says. \end{itemize}` | `needs it, or it is only needed for the statement to mean what it says. \item (Version~2.) Mathlib-only restatements of the six numbered theo…` |
| 6 | avail-v2 | `(\path{LICENSE}, \path{CITATION.cff}, \path{README.md}); none changes any Lean source, so …` | `(\path{LICENSE}, \path{CITATION.cff}, \path{README.md}); none changes any Lean source, so the commits cited above remain the sources of the …` |
| 7 | avail-sizes | `\lean{Napoleon} (two files, 205 lines) and \lean{Lami} (one file, 284 lines), each with a …` | `\lean{Napoleon} (two files, 205 lines) and \lean{Lami} (one file, 284 lines), each with a root file that only imports. Version~2 adds 218 an…` |
| 8 | method-monge | `statement is not stated as a declaration (Section~\ref{sec:limits}).` | `statement is not stated as a declaration in the main files (Section~\ref{sec:limits}); the Layer-14 file of version~2 states it (\decl{Monge…` |
| 9 | desargues-compose | `A reader looking for a statement of the form ``there is a point $O$ on $AA'$, $BB'$ and $C…` | `A reader looking for a statement of the form ``there is a point $O$ on $AA'$, $BB'$ and $CC'$'' has to compose the two declarations; Mathlib…` |
| 10 | monge-instantiation | `We note this only as an instantiation; it is not stated as a separate declaration.` | `We note this only as an instantiation; it is not stated as a separate declaration in the main files. Version~2 proves the companion form (on…` |
| 11 | monge-scope | `The lemma is about centres only; that this homothety maps the one circle onto the other is…` | `The lemma is about centres only; in the main files, that this homothety maps the one circle onto the other is not formalised. Version~2 prov…` |
| 12 | simson-para | `\paragraph{Only the forward direction.} Our Lean development proves only the forward direc…` | `\paragraph{The converse.} The main files of our development prove only the forward direction of the Wallace--Simson theorem.` |
| 13 | simson-converse | `The geometric converse, ``if the feet are collinear then $p$ lies on the circumcircle'', i…` | `The geometric converse, ``if the feet are collinear then $p$ lies on the circumcircle'', was therefore not formalised in the first version o…` |
| 14 | napoleon-halfplane | ```Outward'' is thus expressed through signed area rather than through half-planes; the ste…` | ```Outward'' is thus expressed through signed area rather than through half-planes; in the main files the step from the signed-area statement…` |
| 15 | correct-simson | `\decl{Simson.area2} has a one-way bridge, \decl{Simson.collinear_of_area2_eq_zero} ($\math…` | `\decl{Simson.area2} has a one-way bridge in the main files, \decl{Simson.collinear_of_area2_eq_zero} ($\mathrm{area2}=0$ implies \mdecl{Coll…` |
| 16 | related-simson-weaker | `The Wallace--Simson theorem is \emph{not} new to formal mathematics, and our version is we…` | `The Wallace--Simson theorem is \emph{not} new to formal mathematics, and the first version of ours was weaker than the existing ones in one …` |
| 17 | related-simson-forward | `Our Lean development proves only the forward direction; its \decl{Simson.area2_perpFoot_eq…` | `The main files of our Lean development prove only the forward direction; their \decl{Simson.area2_perpFoot_eq_zero_iff} is a determinant-for…` |
| 18 | related-summary | `The Simson development is a Lean proof of the forward direction of a theorem already forma…` | `The Simson development is a Lean proof of the forward direction (version~2 adds the converse) of a theorem already formalised, with its conv…` |
| 19 | verify-note | `The two author-check confirmations have since been supplied and their placeholders resolve…` | `The two author-check confirmations have since been supplied and their placeholders resolved; no placeholders remain in the paper except the …` |
| 20 | inventory-simson | `Simson's \decl{Simson.area2} is bridged in one direction only.` | `Simson's \decl{Simson.area2} is bridged in one direction only at the cited commits (the other direction is in the Layer-15 file of version~2…` |
| 21 | subsection | `The author has checked each entry of Table~\ref{tab:thms} by hand.` | `The author has checked each entry of Table~\ref{tab:thms} by hand. \subsection{Layers 14 and 15}\label{sec:l1415} Version~2 adds two further…` |
| 22 | limit-monge | `to $O_2$, but no composed statement about circles is given: there are no circles in the st…` | `to $O_2$, but the main files give no composed statement about circles: there are no circles in the statement, and that the homothety maps on…` |
| 23 | limit-converses | `\item \emph{Converses.} The Desargues converse concludes collinearity in the dual plane; t…` | `\item \emph{Converses.} In the main files the Desargues converse concludes collinearity in the dual plane, and turning this into the existen…` |
| 24 | limit-fields | `\item \emph{Fields.} Simson and Napoleon are stated in $\CC$ only, not in a general Euclid…` | `\item \emph{Fields.} In the main files Simson and Napoleon are stated in $\CC$ only, not in a general Euclidean plane (\lean{EuclideanSpace …` |
| 25 | limit-orientation | `\item \emph{Orientation in Napoleon.} ``Outward'' is expressed by the sign of the area of …` | `\item \emph{Orientation in Napoleon.} In the main files ``outward'' is expressed by the sign of the area of the erected triangles, not by ha…` |
| 26 | ack | `The author checked each formal statement in Table~\ref{tab:thms} against its informal coun…` | `The author checked each formal statement in Table~\ref{tab:thms} against its informal counterpart by hand. The Layer-14 and Layer-15 files o…` |
| 27 | subsection-fix | `Unused writer hypotheses agree with Table~nondeg: A≠A' etc. in A1(a) and distinct centres in A2(a).` | `The writer's hypotheses A≠A′, B≠B′, C≠C′ in A1(a) and distinct centres in A2(a) were not needed; the latter agrees with Table~nondeg.` (rewording of my own new text, so it doesn't claim A≠A′ is in the table) |
## New subsection content (§10.1 "Layers 14 and 15"), summary
- Files: `<Lib>/L14.lean` and `<Lib>/L15Classical.lean`; namespace `<Lib>.Classical`. Line counts and gate counts are taken from INTEGRATE_REPORT (gate counts 34/15/21/45/23 PASS, standard axioms; tamper all rejected; library files unchanged by SHA-256).
- Layer 14: all **6/6** numbered theorems are restated Mathlib-only, with a namespace-free check that includes pp.explicit. Each has its witness and the non-degeneracy it proves (all `\decl`). None was false or needed an extra hypothesis. The subsection also states what is missing: secondary forms without a separate witness (napoleon_inner, lami_oriented, monge_homothety, simson_feet), and that the converses are not restated in L14.
- Layer 15: the statement collector gave citations. The writer was blind, with an audited transcript, and wrote 9 theorems + 5 obligations. Its marks: 4 AMBIGUOUS + 1 EXTRA HYPOTHESIS (positive radii). Classification of the 14 statements: **9 covered** (E), **4 outside the paper's statements but proved** (O: A1-obligation, A2-obligation-ext, A2-obligation-int, A3(b)), **0 narrower**, **1 writer statement false as written** (D), **0 open**.
- NEW PROOFs listed: `Simson.Classical.cov_A3_b` (+ bridge `area2_eq_zero_of_collinear`), `Napoleon.Classical.cov_A4_a` (half-planes + non-degeneracy), `Monge.Classical.cov_A2_b`, `Desargues.Classical.cov_A1_obligation`, `Monge.Classical.cov_A2_obligation_ext/_int`, `Napoleon.Classical.cov_A4_obligation_corrected`.
- Writer mis-statement: `classical_A4_obligation` omits U ≠ V. The negation is `Napoleon.Classical.A4_obligation_false`, the corrected form is `cov_A4_obligation_corrected`. Stated as the writer's error.

## Discrepancies fixed (paper claim → contradicted/outdated by report line)
1. **Simson converse "not proved/not formalised"** (contributions, §Simson "Only the forward direction", §correct Simson bullet, bridge inventory, Related work ×2 + summary, Limitations "Converses"). L15_COMPARE: `cov_A3_b` NEW PROOF; `area2_eq_zero_of_collinear` 8 lines. Each passage now says the first version did not prove it and version 2 does (L15 file). Priority claim explicitly withheld. The paragraph title was changed from "Only the forward direction." to "The converse.".
2. **Desargues converse needs a second lemma / reader must compose** (§Desargues, Limitations). `cov_A1_b` builds the concurrency point explicitly. Updated.
3. **Monge companion form "not a separate declaration"** (§Monge). `cov_A2_b`. Updated.
4. **Monge "homothety maps one circle onto the other is not formalised/proved"** (§Monge Scope, Limitations). `cov_A2_obligation_ext` + `ext_eq_of_isExt` + `cov_A2_a` prove it for positive radii (the writer's IsExtSimCenter is exactly "homothety maps circle s onto circle t"). Updated. The tangent-line formulation is still listed as not formalised.
5. **Monge composed statement "not stated as a declaration"** (Method). `l14_monge` concludes Mathlib `Collinear`. Updated.
6. **Napoleon "signed-area → opposite side of the line not formalised"** (§Napoleon, Limitations "Orientation"). `l14_napoleon_outer` (SOppSide, no orientation hypothesis) and `cov_A4_a`. Updated.
7. **"Simson and Napoleon stated in ℂ only"** (Limitations "Fields"). The L15 statements are in `EuclideanSpace ℝ (Fin 2)` (classical_statements/Classical.lean A3, A4). Qualified to "in the main files".
8. **Satisfiability "unresolved" for desargues_mk, simson, lami_nondegenerate.** These are not contradicted, because the battery is of the cited commits. The L14 witnesses now give concrete configurations for the Mathlib-only forms. Added one sentence in §10.1; the battery figures were left unchanged.
9. **Abstract / contributions** did not mention the version-2 content. Added one abstract sentence and one contributions bullet. The line count "about 1,430" is now scoped to "without the version-2 files".
10. **Availability:** version-2 commit text with the 5 `NEWCOMMIT` tokens. It says earlier statements/files are unchanged and that `scratch/` is removed (INTEGRATE_REPORT step 1/5). Sizes of the new files were added (INTEGRATE_REPORT tables).
11. **Acknowledgements/AI use:** the L14/L15 work is by AI agents and is not part of the author's hand check. This is honest scoping and was added.
12. **Version note:** `\date{7 October 2026; version~2, 22 October 2026}`.

## Repository pins
- Commit macros/hashes **not changed**.
- Added above the pin definitions (line 44): `% L1415-REPIN: \commitdesargues \commitmonge \commitsimson \commitnapoleon \commitlami \urlcommitdesargues … \urlcommitlami (only if line links are to point at the version-2 commit; …); plus the five NEWCOMMIT tokens in the Availability paragraph`.
- Availability: "desargues NEWCOMMIT, monge NEWCOMMIT, simson NEWCOMMIT, napoleon NEWCOMMIT, lami NEWCOMMIT".

## Open items
1. Fill the five `NEWCOMMIT` tokens after the commits are pushed. Nothing is committed yet (INTEGRATE_REPORT: "Nothing was committed or pushed"). Decide whether to repoint the `\commit*`/`\urlcommit*` macros. The library files are unchanged, so the line links stay valid either way.
2. The version-2 commit **removes `scratch/`**, including `scratch/Ax.lean`, the file the Verification paragraph mentions as "a file kept outside the library" for `#print axioms`. The paper text refers to the cited commits, so it is still accurate, but the availability text now notes the removal. Check that this is acceptable.
3. The house battery (mutation, contradiction, ablation, linter, satisfiability) was **not** re-run on the version-2 files. §10.1 says the battery figures refer to the cited commits. Gate and tamper were re-run (INTEGRATE_REPORT).
4. L14/L15 gates were run on arm64 macOS only, with `jl -g` (GNU tools), because the pinned gate.sh needs GNU mktemp. This is consistent with the existing Availability text. Not yet re-run on the original build machine.
5. The author's hand check covers Table 1 only. The Acknowledgements now say L14/L15 are not hand-checked. The author may want to read the 6 L14 statements in L14_REPORT's appendix.
6. The `\decl` names of the new declarations come from the L15 scratch files, with the namespace renamed per INTEGRATE_REPORT (`L15Compare` → `<Lib>.Classical`), and from L14_REPORT. If a name gate is run over `\decl`, it must include the new files.
7. Desargues `cov_A1_b` "with lines as spans" comes from L15_COMPARE ("`pline y z` is the projectivisation of span"). The writer's `pline` = `Projectivization.Subspace.span {p,q}`. Fine as worded.
