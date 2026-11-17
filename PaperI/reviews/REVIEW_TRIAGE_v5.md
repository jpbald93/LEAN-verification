# Paper I — round-2 review triage (v5 draft → v6)

Round-2 reviews landed 2026-11-10: `gemini-4-argon` (18:51, 0 MAJOR / 10 MINOR), `gpt-6-astra` (18:55,
3 MAJOR / 14 MINOR), `claude-opus-5-5` (20:03, 2 MAJOR / 17 MINOR). 46 findings, 5 major, heavy overlap;
consolidated below to 24 rows. Every row was re-checked with a tool before it was applied — the check is named.

| # | finding (reviewers) | verification I ran | disposition | where it is fixed in v6 |
|---|---|---|---|---|
| 1 | §6.1 "27 definitions" is wrong; the three files hold 36 | `def` count in `PaperJ/layer0/{soddy_3d,descartes_degenerate,descartes_plane3d}.lean` = 14+14+8, nine of them `noncomputable def` | **accepted** | §6.1 Status: "36 definitions, nine of them declared `noncomputable def`" |
| 2 | §7 "`paperi_circles` also carries private lemmas" contradicts l.819 and the code | `git grep '^private '` on `final_circles` → 0 lines; `final_quad` → 0 | **accepted (my sentence was false)** | §7 "What the counts measure": 118+15 / 115+23 / 110+11, only Inversion counts private lemmas |
| 3 | §7 l.919–922 stale: "the paragraphs here at the earlier ones they name" | paragraph now quotes the final commits only | **accepted** | sentence deleted |
| 4 | §7 30-October figures given in quad/circles/arbelos/inversion order against a quad/arbelos/circles/inversion table | pairs cross-checked with the reports | **accepted** | figures now name each development |
| 5 | §7 arbelos tamper arithmetic "7 because 11−2" | `tests/tamper.sh` on all four: arbelos `falsehyp`+`falsehyp_ext`; circles/inversion +`falsehyp2/3`+`falsestmt`; quad also `fusshyp`,`fussstmt` → 7 / 9 / 9 / 11 | **accepted** | §7 gates paragraph rewritten (five token/axiom + two semantic) |
| 6 | van Aubel "squares lie outside" still inside the theorem environment | read l.310 vs l.313 | **accepted** | clause removed from the theorem, note kept |
| 7 | internal tangency needs `0 ≤ ρ_s` | `Arbelos/Basic.lean:58` `isIntTangent_iff` | **accepted** | §4 Proofs: `0\le\rho_s\le\rho_t` |
| 8 | §8 item 5 omits `r₂<0` in `bridge_intTangent` | item 5 listed only `steiner_alg_*`, `fuss_opposite`, `steiner_porism` | **accepted (round-1 rejection was wrong here)** | item 5 extended |
| 9 | Layer 15: `I5c` scope gap suppressed; three closures presented as proofs, not scratch certificates | `L15_COMPARE_M.md:29,48`, `L15_GAP_CLOSED.md:15–16` | **accepted** | Layer-15 paragraph: no substantive-difference row → "no row classified as a substantive difference", I5c and I5b gaps stated, closures marked as scratch certificates outside the four gates |
| 10 | Layer 15: library area is a two-triangle sum, not "a three-term formula"; closure is for a 2-D vector space, not a torsor | `quadArea = triArea A B C + triArea A C D`; `L15_GAP_CLOSED.md` | **accepted** | Layer-15 paragraph rewritten |
| 11 | Layer 15: Ptolemy equality characterises concyclicity **or collinear cyclic order** | `PtolemyOrder.classical_I2b` statement | **accepted** | parenthetical corrected; `ptolemy_order.lean` named as a scratch certificate |
| 12 | §7 Layer 13: blind input was more damaged than reported — the `LEAK` regex deleted whole theorem sentences; `blind_79/80` came from a hand-made excerpt | `AFM/tools/blind.py:38–39`; re-ran it on `paperi.tex.bak-phase6` → 24 of 25 theorem environments survive, six shortened | **accepted** | Layer-13 paragraph: redaction cause stated, Johnson row and inversion basics marked uncompared, addendum provenance stated |
| 13 | §7 Layer 13: "stated every pair … proved both implications" over-universal | `L13_COMPARE_M/J` report selected pairings, restrictions, one-way rows | **accepted** | "selected pairings … for those it reported as two-way" |
| 14 | §7 Layer 13: "No prose statement was misread" claims validation of unpaired statements | same reports | **accepted** | "No compared pair was classified as a misreading … omitted and unpaired statements were not thereby validated" |
| 15 | §7 "each report lists the names it mutated and records the file hashes" | `battery_final_*.md` contain one 40-hex HEAD each, no per-file hashes | **accepted (false as written)** | reports now described as HEAD + lists; digests attributed to `RECEIPTS.md` |
| 16 | §7 non-vacuity: the final unresolved items do not all have Layer-14 witnesses | `battery_final_arbelos.md` unresolved vs the 31 `l14w_*` names | **accepted** | sentence rewritten with the Steiner-porism and `bankoff_exists` gaps and the 50-restatement moment |
| 17 | §7 survivors paragraph garbled ("two reasons, only one weakening") | survivor list in `BATT`/report; `twin_left_exists` is the only library survivor | **accepted** | paragraph rewritten |
| 18 | §7 Layer 14: the Peaucellier search claim cannot be checked without its restrictions, and a fully integral pivot-inside cell exists | checked `A=±3i, P=4, Q=-4, a=5, b=3, R=4`: four sides 5, `a²−b²=16=R²`, `Q=-inv_4(P)`; and `A=(√21,2)` etc. for the rational-length example | **accepted** | restriction names the classical cell; both examples stated with what is rational about them |
| 19 | §6.1 the `cmp_exists_unique_completion` correspondence overstates what the cited development proves | read the two theorem names/statements in `PaperJ/SCOUT.md` §1 and the §6.1 text | **accepted** | §6.1 opening: column completion + `two_tangent_spheres` classification, no claimed reduction |
| 20 | §6.1 "every statement here is an instance" contradicts the same paragraph and the scout; `soddy_exists_3d` not tagged as a reproof; the "explicit" 3-D claim belongs to `soddyCentre`/`soddy_dist_sq` | `SCOUT.md` §1 classes (REPROOF / NONE FOUND) | **accepted** | closing paragraph rewritten; `soddy_exists_3d` tagged reproof of `curvature_center_converse`/`converse_soddy_gosset` |
| 21 | §6.1 "contradicts the intuitive expectation"; atlas wording implies it proves existence of an enclosing circle; refuted completion-map claim uses undefined `P_X` | `SCOUT.md` §4 (the expectation was ours); atlas-lean statement | **accepted** | expectation clause deleted; atlas sentence rewritten; `P_X` defined with a new `\cite{platek}` bibitem (arXiv:2604.03067, title read from the e-print) |
| 22 | §6.1 supplementary hypotheses vanish in the summary: `plane_fourth_sphere` needs a **positive** root `k`; the line classification holds for two positive-radius externally tangent circles on the same side of their common tangent; `I5b` covers nonzero roots only | statements in `descartes_plane3d.lean` / `descartes_degenerate.lean` | **accepted** | line-case frame and positive-root clause added to §6.1 |
| 23 | Abstract: pedal-area identity has an earlier unit-circle complex form (`lean-genius`) | round-1 finding, unchanged | **accepted** | qualifier added before the remaining-statements sentence |
| 24 | Layer 10 descriptions: `cross_eq_det` is `Basis.det`, not `Matrix.det`; no "Johnson-circle predicate" (two centre identities); `bridge_peaucellier_collinear` is a `Collinear` statement | bridge names and statements in `Bridge.lean` | **accepted** | all three descriptions corrected |
| 25 | §10: the four repo URLs and `LEAN-verification` return 404 (gh api, all four + folder); the §6.1 files and Layer-15 certificates are not listed | `gh api` by two reviewers; the trees have no remote (`RECEIPTS.md`) | **accepted, and cannot be closed by me** — pushing is Josh's step | §10 rewritten: "currently local, not published", planned locations, and the supporting-material list now names the three §6.1 files with SHA-256 and the Layer-15 certificates |
| 26 | §7 cross-machine: "their logs are no longer in the evidence folders" is false for `6ed3d660`/`9f386b22`; the circles/inversion second-machine PASS (78/46) is unverified | `FUSS_INTEGRATE.md` §3 and `FIX1_REPORT.md:29–30` record both digests on both machines; `REPORT_I3.md`/`REPORT_I4.md` are owning-machine runs | **accepted** | paragraph rewritten: reports cited, historical status stated, and the missing circles/inversion second-machine log admitted |
| 27 | §7 hand-check paragraph is an active `\PH` "release blocker" | `grep '\\PH{'` | **accepted** | placeholder replaced by the actual status: hand check pending, round-1 (39 findings, 37 applied) and round-2 (46 findings, 5 major, all applied) recorded |

**Not applied as written:** nothing was rejected. Two cosmetic halves were merged: Argon's "add a sentence
about `namegate`'s limits" (Astra 12) is covered by row 15's reattribution of the digests, because the paper
already says the script checks names and anchors; and Astra's "extend `l14w_steiner_porism` with injectivity
and disjointness" is left as a stated gap rather than a library change (it would change a gated witness file
and every Layer-14 count for no claim in the paper).

**Verification of the result:** `pdflatex` twice, rc=0, **30 pages** (was 28), 0 undefined references, no
`\PH` left in the text, name gate **PASS** (160 `\decl` names, 83 anchors, `namegate_i.py`).
Backup of the pre-triage draft: `paperi.tex.bak-r2triage`; the edits are scripted in `apply_r2.py`.

Round-3 reviews dispatched on this v6 to the two reviewers that raised majors (Astra, Opus); Argon's round-2
was MINOR-only and its 10 findings are all in the table above.
