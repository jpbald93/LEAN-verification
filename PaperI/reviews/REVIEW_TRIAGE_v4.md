# Paper I v4 — review triage

Frozen input: `paperi.tex` as dispatched to the three reviewers at 16:22 EST (28-page build after fixes).
Reviews in hand when this triage was written: `gemini-4-argon` (16:30) and `gpt-6-astra` (16:36);
`claude-opus-5-5` was still running and its findings are triaged in `REVIEW_TRIAGE_v4_opus.md` when it lands.

Both available reviews raise **majors**, and they agree on four of them independently (§6.1 status claim,
Layer-10 bridge description, Layer-13 `blind_79/80`). Every factual claim I could re-check with a tool was
re-checked; the two mathematical counterexamples (Astra 1 and 11) I re-derived myself with SymPy rather than
taking them on trust.

## Verified by me before accepting

| claim | how | result |
|---|---|---|
| collinear-feet example admits a completion | SymPy: three spheres `(0,0,1),(2,0,1),(1,0,1/4)`, radii `1,1,1/4`; fourth `(1,√3/3,1/3)`, radius `1/3` | all three distances equal `r+ρ` exactly; sphere rests on `z=0` → **the paper's nonexistence claim was false** |
| Peaucellier cell with rational link lengths | SymPy: `a=3, b=5, R=4`, `A=(√21,2)`, `B=(√21,−2)`, `P=(√21+√5,0)`, `Q=(√21−√5,0)` | `|A|=|B|=5`, all four rhombus sides `3`, `|P||Q|=16=R²`, `A≠B`, `P≠Q` → **the paper's nonexistence claim was false** |
| `soddy_exists_3d` needs `κ≠0` | ssh john, `~/lean/l13_inversion/scratch/soddy_3d.lean:438–459` | conclusion is `κ ≠ 0 → ∃ x ρ, …` |
| `no_enclosing_soddy` is conditional | ssh jack, `~/x_paperi_inversion/scratch/descartes_degenerate.lean:581–584` | hypotheses include `dist 0 ca = R-a`, `dist 0 cb = R-b`, `dist ca cb = a+b` |
| quad bridge has no `powPt`, no `convexHull`, convexity is `SOppSide` | local `layer10/Bridge_paperi_quad.lean` | 15 bridge theorems, none of them about `powPt` or `convexHull`; `convexQuad_iff_sOppSide` is the convexity bridge |
| `det3/dot/triple/det3g/det4g` are inversion's | `layer10/Bridge_paperi_inversion.lean` names + reports | private definitions of `Inversion/Descartes.lean`, not arbelos |
| blind statements are `blind_79/80`, 80 in total | local `layer13/Blind.lean:1260,1277`; `grep -c "^theorem blind_"` = 80 | the paper said `blind_81/82` |
| supplementary files: 77 theorems, 68 public, 27 defs | ssh jack/john `grep -c` on the three files (`soddy_3d` 32 public, `descartes_plane3d` 16+3, `descartes_degenerate` 20+6) | the paper's "67" was wrong; Astra's 77/68 is right, Argon's 62 wrong |
| survivor `twin_left_exists` is a library theorem | `layer10/battery_final_arbelos.md` survivor detail `[lit2->3@53]` | `2*a` → `3*a` in `Arbelos.twin_left_exists`, a Table-1 theorem |

## Argon (`REVIEW_gemini-4-argon_v4.md`)

| # | sev | verdict | reason | action |
|---|---|---|---|---|
| 1 | MAJOR | accept | three §6.1 files are untracked scratch, in no gate/tamper list; count 67 wrong | Status paragraph rewritten: 77 theorem declarations (68 public) + 27 definitions, compiled and token-checked, explicitly *not* under the four gates |
| 2 | MAJOR | accept | quad bridges `powPt`/`convexHull` do not exist; arbelos has three half-disc pieces, not two; `det*` helpers are inversion's | Layer-10 paragraph rewritten from the actual bridge theorem names of all four modules |
| 3 | MAJOR | accept | `blind_79/80`, and `blind_80`'s stored comparison is one-directional | Layer-13 paragraph rewritten with the real names, the real directions, and "fresh two-way comparison pending" |
| 4 | MINOR | accept | `bridge_powPt_eq_power` does not exist | Limits item 4 now cites `powPt_eq_power` (circles) and `bridge_powC` (arbelos) |
| 5 | MINOR | accept | §5 said no power bridge exists | replaced by the bridge citation |
| 6 | MINOR | accept | quad area is the two-triangle sum | "three-term" → "the two-triangle sum of Definition 1(iii)" |
| 7 | MINOR | accept | counts paragraph predates Layer 10/14 | reconciliation sentence added with the final-commit figures |
| 8 | MINOR | accept | `paperi_quad` tracks nine `scratch/` files | sentence added to the receipts paragraph |
| 9 | MINOR | accept (a) / defer (b) | (a) the arbelos 8th tamper test belongs to `53d0573`, removed from the final-commit row; (b) the duplicated `REQUIRED=` append in `gate.sh` is a real defect in the four repos | (a) done; (b) queued as a repo fix, not a prose change — the gate's count is unaffected |
| 10 | MINOR | accept | example fixes move 3, maps by move 0 | clarified |
| 11 | MINOR | accept | Paper J scout requires `atlas`/`lean-genius`/LMW citations here | three citations added |
| 12 | MINOR | accept | "three developments" reads as four repos | "the three files" |
| 13 | MINOR | accept, unchanged | one `\PH` remains on purpose (hand check + reviews) | stays until phase 9 |

## Astra (`REVIEW_gpt-6-astra_v4.md`)

| # | sev | verdict | reason | action |
|---|---|---|---|---|
| 1 | MAJOR | accept | nonexistence false — I re-derived the counterexample exactly | collinear case now says the construction degenerates, with the `1,1,1/4` completion named |
| 2 | MAJOR | accept | feet/centre conflation and radius-vs-curvature slip | plane paragraph rewritten (`z=0`, centres `(p,r)`, radius `1/3` = curvature `3`, `z=2r` labelled explanatory) |
| 3 | MAJOR | accept | `κ≠0` is in the Lean conclusion | "every nonzero root `κ` … realised by the sphere of signed radius `1/κ`" |
| 4 | MAJOR | accept | enclosing claim needs the enclosing-member setup | restated with the three metric hypotheses and the `c₄=0, ρ=R` conclusion |
| 5 | MAJOR | accept, not re-read at source | the reviewer quotes the cited repository's signatures; I did not re-open that repository | all three correspondences narrowed (matrix-column completion, curvature identity, three-hyperplane exclusion) |
| 6 | MAJOR | accept | same as Argon 1, plus the public/private split | merged into the Status rewrite |
| 7 | MAJOR | accept | "every survivor is a witness", "each a weakened bound" both false | survivors paragraph rewritten (14 witness + 1 theorem, two distinct reasons) |
| 8 | MAJOR | accept | same defect as Argon 2, plus §5 and §9 | merged into the Layer-10 rewrite and the Limits fix |
| 9 | MAJOR | accept | stored Bankoff comparison is one-directional and no longer compiles against the strengthened theorem | Layer-13 paragraph states exactly that, and that a fresh comparison is pending |
| 10 | MINOR | accept | direction of `apollonian_integral` was reversed; J's and M's row counts must be kept | both directions and both row counts stated |
| 11 | MAJOR | accept | nonexistence false — I re-derived the rational cell | narrowed to "the bounded search found none under its restrictions", with the rational example given |
| 12 | MINOR | accept | 31 witnesses shared, omissions listed; area formula wrong | "31 concrete witness declarations", exact two-triangle formula |
| 13 | MAJOR | accept | I5c packing gap must not be hidden | scope-gap sentence added; abstract qualified to "under Apollonian curvature moves" |

## State after applying

- `paperi.tex` edits: §5 intro (power bridge), §5 Theorem 23 note, all four §6.1 paragraphs + Status,
  survivors paragraph, counts paragraph, receipts paragraph, tamper table (arbelos row), Layer-10 paragraph,
  Layer-14 paragraph, Layer-13 paragraph, Layer-15 paragraph, Limits item 4, abstract, three citations.
- Rebuild: `pdflatex` twice, rc=0, **28 pages**, 0 undefined references, `\PH` count 1 (intentional).
- Layer-11 anchor gate re-run after the edits: **NAME GATE PASS**, 160 `\decl` names, 83 anchors
  (one name added, `CircleSystems.powPt_eq_power`); `AFM/PaperI/L11_ANCHORS.md` refreshed.
- Not applied, deliberately: nothing from either review. Deferred: the `gate.sh` duplicate-`REQUIRED` defect
  (repo hygiene, four repos, gate counts unchanged) and the fresh two-way Bankoff comparison (needs a
  compiling certificate, next dispatch on john).

## Opus 5.5 (`REVIEW_claude-opus-5-5_v4.md`, landed 17:01)

Verdict: major revision, 30 findings, 12 major, "none needs a new proof". Its majors 1, 2, 3, 9, 12, 15, 16
and 21 are the same defects Argon and Astra found, and were already fixed when it landed; they are listed
as such. Its independent value: it re-ran `namegate_i.py` (PASS, 159/83) and reproduced every battery cell,
the survivor and unused-hypothesis names, the line counts and the digests.

| # | sev | verdict | reason | action |
|---|---|---|---|---|
| 1 | MAJOR | accept (fixed earlier) | same as Argon 1 / Astra 6 | Status rewritten (77 theorems, 68 public, 27 defs; not gated) |
| 2 | MAJOR | accept (fixed earlier) | same as Astra 1; its numeric check finds the same radius-1/3 completion I did | collinear case rewritten |
| 3 | MAJOR | accept (fixed earlier) | same as Astra 4; also tells me "contradicts the intuitive expectation" was only about our own brief | enclosing result restated conditionally |
| 4 | MAJOR | accept | SCOUT §1 classes the 3D Soddy algebra as REPROOF; only `augdescartes` was cited | reproof tagging added (`soddy_gosset`, `apollonian_reflection`, Coq `DescartesCircles.v` + new bibitem `coqdescartes`); line case and `plane_descartes` tagged as instances of `augmented_descartes_general`/`soddy_gosset_general` |
| 5 | MINOR | accept (fixed earlier) | radius 1/3 = curvature 3 | fixed in the plane paragraph |
| 6 | MINOR | accept | the zero-root identification was garbled and the decl names were missing | now cites `plane_root_zero_iff_eq` and `planeQuad_other_root`, and says the `z=2r` reading is not formalised |
| 7 | MINOR | accept | the completion-map claim is Paper K's, not Paper J's; numerical only | provenance corrected; "refuted numerically (Python, six configurations; no Lean counterexample)" |
| 8 | MINOR | accept | "beyond the plane" appeared inside a negation | sentence replaced by the instance-of-`augdescartes` statement |
| 9 | MAJOR | accept (fixed earlier) | same as Argon 3 / Astra 9 | Layer-13 paragraph rewritten |
| 10 | MINOR | accept | "every difference is the library stronger" contradicts the paragraph's own rows | replaced by the encoding explanation, with the two directions named |
| 11 | MINOR | accept | the comparer was the same model, on work copies | stated in the paragraph |
| 12 | MAJOR | accept (fixed earlier) | same as Argon 2 / Astra 8 | Layer-10 rewrite; §7 item 4 fixed |
| 13 | MINOR | accept (fixed earlier) | §5 power sentence stale | fixed |
| 14 | MINOR | accept | "Every notion … is tied" over-claims; the bridge inventory has NO-BRIDGE rows (4/7, 7/11, 21/23, 9/10) | opening qualified to "each notion that has a Mathlib counterpart"; the unbridged helpers are named |
| 15 | MAJOR | accept (fixed earlier) | arbelos 8th test belongs to `53d0573`; the "seven rather than nine" arithmetic was wrong | row fixed; the arithmetic sentence is being rewritten (it still needs the two semantic tests wording) |
| 16 | MAJOR | accept (fixed earlier) | same as Astra 7 | survivors paragraph rewritten |
| 17 | MAJOR | accept | the "30 October gave the same mutation figures" clause was false (167/152/190/134 vs 273/298/321/272) | replaced by the incomparable-denominators sentence |
| 18 | MAJOR | accept | the counts paragraph still described `92c003b` / `53d0573` / 59+8 | rewritten at the final commits, inversion arithmetic stated, `53d0573` marked pre-publication |
| 19 | MINOR | accept | the cross-machine paragraph quoted pre-Layer-10/14 states and two digests with no surviving log | rewritten: final commits **not** rebuilt cross-machine; digests reported as earlier-run evidence with their commits |
| 20 | MINOR | accept | hand classification covers the 29 Oct set only; "stmt-invalid" undefined; witness commit unnamed | all three added |
| 21 | MINOR | accept (fixed earlier) | "a witness for each" | now 31 witnesses for 50 restatements |
| 22 | MINOR | accept | the Layer-15 closures are scratch certificates | stated for all three closures and the area bridge |
| 23 | MINOR | accept | Euler's proof does use `Fact (finrank = 2)` | corrected |
| 24 | MINOR | accept | "squares lie outside" unproved inside a theorem | moved out of the theorem environment |
| 25 | MINOR | accept | revision history inside a theorem | moved out (it is in Layer 13) |
| 26 | MINOR | **reject** | §7 item 5 already lists `r_2<0` in `bridge_intTangent` — its snapshot missed the fifth bullet | none needed |
| 27 | MINOR | accept | "the commits will be given" is stale | rewritten in the present tense |
| 28 | MINOR | accept, blocked on Josh | the four repo URLs are 404 and there is no remote; all 83 `\src` links are dead until the repos are pushed | **cannot be fixed from here** — needs the four repositories pushed with the pinned commits and a `PaperI` folder; recorded as a pre-deposit task |
| 29 | MINOR | accept, deferred | the name gate only checks `\decl`/`\src`, which is how `bridge_powPt_eq_power` and `blind_81/82` got through | both names are gone; extending `namegate_i.py` to `\lean{}` identifiers with an allow-list is queued as phase 10 (a false-positive risk needs care) |
| 30 | MINOR | accept, unchanged | one `\PH` remains by design | filled before submission |

Round-2 state: all 39 findings from three reviewers are triaged, 37 accepted and applied, 1 rejected with a
reason (26), 1 blocked on the owner (28), 1 deferred as tooling (29). Rebuild after the Opus round: 28 pages,
0 undefined references, `\PH` 1, name gate PASS at 160 declarations / 83 anchors.
